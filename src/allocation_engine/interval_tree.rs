// Copyright (C) 2022 Alibaba Cloud. All rights reserved.
// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2

use crate::{Error, Result};
use std::cmp::{max, min, Ordering};

/// Policy for resource allocation.
#[derive(Copy, Clone, Debug)]
pub enum AllocPolicy {
    /// Allocate from the first matched entry.
    FirstMatch,
    /// Allocate first matched entry from the end of the range.
    LastMatch,
    // Allocate a memory slot starting with the specified addrres
    // if it is available.
    ExactMatch,
}

impl Default for AllocPolicy {
    fn default() -> Self {
        AllocPolicy::FirstMatch
    }
}

/// Struct to describe resource allocation constraints.
#[derive(Copy, Clone, Debug)]
pub struct Constraint {
    /// Size to allocate.
    pub size: u64,
    /// Lower boundary for the allocated resource.
    pub min: u64,
    /// Upper boundary for the allocated resource.
    pub max: u64,
    /// Alignment for the allocated resource.
    pub align: u64,
    /// Resource allocation policy.
    pub policy: AllocPolicy,
}

/// A closed interval range [min, max] used to describe a
/// memory slot that will be assigned to a device by the VMM.
/// This structure represents the key of the Node object in
/// the interval tree implementation.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Hash)]
pub struct Range {
    pub min: u64,
    pub max: u64,
}

impl std::fmt::Debug for Range {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "[ {:016x}, {:016x} ]", self.min, self.max)
    }
}

impl Range {
    /// Create a new Range object.
    pub fn new(min: u64, max: u64) -> Result<Self> {
        if min > max {
            return Err(Error::InvalidRange(min, max));
        }
        Ok(Range { min: min, max: max })
    }

    /// Get length of the range.
    pub fn len(&self) -> u64 {
        self.max - self.min + 1
    }

    /// Check whether two Range objects intersect with each other.
    pub fn intersect(&self, other: &Range) -> bool {
        max(self.min, other.min) <= min(self.max, other.max)
    }

    /// Check whether the key is fully covered.
    pub fn contain(&self, other: &Range) -> bool {
        self.min <= other.min && self.max >= other.max
    }

    /// Create a new Range object with min being the first value from the range
    /// that is aligned to `align`.
    pub fn align_forward(&self, align: u64) -> Result<Range> {
        match align {
            0 | 1 => Ok(*self),
            _ => {
                if !align.is_power_of_two() {
                    return Err(Error::InvalidAlignment);
                }
                if let Some(min) = self.min.checked_add(align - 1).map(|v| v & !(align - 1)) {
                    if min <= self.max {
                        return Ok(Range::new(min, self.max)?);
                    }
                }
                return Err(Error::UnalignedAddress);
            }
        }
    }

    /// Create a new Range object with min being the last value from the range
    /// that is aligned to `align`.
    pub fn align_back(&self, align: u64, size: u64) -> Result<Range> {
        let mut candidate_address = self.max.checked_sub(size).ok_or(Error::UnalignedAddress)? + 1;
        candidate_address = (candidate_address / align) * align;
        if candidate_address >= self.min {
            return Ok(Range::new(candidate_address, candidate_address + size)?);
        }
        return Err(Error::UnalignedAddress);
    }
}

impl Ord for Range {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.min.cmp(&other.min) {
            Ordering::Equal => self.max.cmp(&other.max),
            res => res,
        }
    }
}

// Node state for interval tree nodes.
///
/// Valid state transition:
/// - None -> Free: IntervalTree::insert()
/// - Free -> Allocated: IntervalTree::allocate()
/// - Allocated -> Free: IntervalTree::free()
/// - * -> None: IntervalTree::delete()
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord)]
pub enum NodeState {
    /// Node is free.
    Free,
    /// Node is allocated.
    Allocated,
}

impl NodeState {
    fn take(&mut self) -> Self {
        std::mem::replace(self, NodeState::Free)
    }

    fn replace(&mut self, value: NodeState) -> Self {
        std::mem::replace(self, value)
    }

    pub(crate) fn is_free(&self) -> bool {
        *self == NodeState::Free
    }
}

/// Internal tree node to implement interval tree.
#[derive(Debug, PartialEq)]
pub(crate) struct InnerNode {
    /// Interval handled by this node.
    pub(crate) key: Range,
    /// Optional contained data, None if the node is free.
    pub(crate) node_state: NodeState,
    /// Optional left child of current node.
    pub(crate) left: Option<Box<InnerNode>>,
    /// Optional right child of current node.
    pub(crate) right: Option<Box<InnerNode>>,
    /// Cached height of the node.
    pub(crate) height: u64,
    /// Cached maximum valued covered by this node.
    pub(crate) max_key: u64,
}

impl InnerNode {
    fn new(key: Range, node_state: NodeState) -> Self {
        InnerNode {
            key,
            node_state,
            left: None,
            right: None,
            height: 1,
            max_key: key.max,
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_range() {
        assert_eq!(
            Range::new(2u64, 1u64).unwrap_err(),
            Error::InvalidRange(2, 1)
        );
    }

    #[test]
    fn test_range_intersect() {
        let a = Range::new(1u64, 4u64).unwrap();
        let b = Range::new(4u64, 6u64).unwrap();
        let c = Range::new(2u64, 3u64).unwrap();
        let d = Range::new(4u64, 4u64).unwrap();
        let e = Range::new(5u64, 6u64).unwrap();

        assert!(a.intersect(&b));
        assert!(b.intersect(&a));
        assert!(a.intersect(&c));
        assert!(c.intersect(&a));
        assert!(a.intersect(&d));
        assert!(d.intersect(&a));
        assert!(!a.intersect(&e));
        assert!(!e.intersect(&a));

        assert_eq!(a.len(), 4);
        assert_eq!(d.len(), 1);
    }

    #[test]
    fn test_range_contain() {
        let a = Range::new(2u64, 6u64).unwrap();
        assert!(a.contain(&Range::new(2u64, 3u64).unwrap()));
        assert!(a.contain(&Range::new(3u64, 4u64).unwrap()));
        assert!(a.contain(&Range::new(5u64, 5u64).unwrap()));
        assert!(a.contain(&Range::new(5u64, 6u64).unwrap()));
        assert!(a.contain(&Range::new(6u64, 6u64).unwrap()));
        assert!(!a.contain(&Range::new(1u64, 1u64).unwrap()));
        assert!(!a.contain(&Range::new(1u64, 2u64).unwrap()));
        assert!(!a.contain(&Range::new(1u64, 3u64).unwrap()));
        assert!(!a.contain(&Range::new(1u64, 7u64).unwrap()));
        assert!(!a.contain(&Range::new(7u64, 8u64).unwrap()));
        assert!(!a.contain(&Range::new(6u64, 7u64).unwrap()));
        assert!(!a.contain(&Range::new(7u64, 8u64).unwrap()));
    }

    #[test]
    fn test_range_align_forward() {
        let a = Range::new(2u64, 6u64).unwrap();
        assert_eq!(a.align_forward(0).unwrap(), Range::new(2u64, 6u64).unwrap());
        assert_eq!(a.align_forward(1).unwrap(), Range::new(2u64, 6u64).unwrap());
        assert_eq!(a.align_forward(2).unwrap(), Range::new(2u64, 6u64).unwrap());
        assert_eq!(a.align_forward(4).unwrap(), Range::new(4u64, 6u64).unwrap());
        assert_eq!(a.align_forward(8).unwrap_err(), Error::UnalignedAddress);
        assert_eq!(a.align_forward(3).unwrap_err(), Error::InvalidAlignment);

        let a = Range::new(0xFFFF_FFFF_FFFF_FFFDu64, 0xFFFF_FFFF_FFFF_FFFFu64).unwrap();
        assert_eq!(
            a.align_forward(2).unwrap(),
            Range::new(0xFFFF_FFFF_FFFF_FFFEu64, 0xFFFF_FFFF_FFFF_FFFF).unwrap()
        );
        assert_eq!(a.align_forward(4).unwrap_err(), Error::UnalignedAddress);
    }

    #[test]
    fn test_range_align_back() {
        let a = Range::new(2u64, 10u64).unwrap();
        assert_eq!(a.align_back(8, 1).unwrap(), Range::new(8, 9).unwrap());
        assert_eq!(a.align_back(8, 5).unwrap_err(), Error::UnalignedAddress);
    }

    #[test]
    fn test_range_ord() {
        let a = Range::new(1u64, 4u64).unwrap();
        let b = Range::new(1u64, 4u64).unwrap();
        let c = Range::new(1u64, 3u64).unwrap();
        let d = Range::new(1u64, 5u64).unwrap();
        let e = Range::new(2u64, 2u64).unwrap();

        assert_eq!(a, b);
        assert_eq!(b, a);
        assert!(a > c);
        assert!(c < a);
        assert!(a < d);
        assert!(d > a);
        assert!(a < e);
        assert!(e > a);
    }
}
