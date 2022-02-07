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

impl std::fmt::Display for Range {
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

    /// Returns a readonly reference to the node associated with the `key` or None if not found.
    fn search(&self, key: &Range) -> Option<&Self> {
        match self.key.cmp(key) {
            Ordering::Equal => Some(self),
            Ordering::Less => self.right.as_ref().and_then(|node| node.search(key)),
            Ordering::Greater => self.left.as_ref().and_then(|node| node.search(key)),
        }
    }

    /// Returns a shared reference to the node covers full range of the `key`.
    fn search_superset(&self, key: &Range) -> Option<&Self> {
        if self.key.contain(key) {
            Some(self)
        } else if key.max < self.key.min && self.left.is_some() {
            // Safe to unwrap() because we have just checked it.
            self.left.as_ref().unwrap().search_superset(key)
        } else if key.min > self.key.max && self.right.is_some() {
            // Safe to unwrap() because we have just checked it.
            self.right.as_ref().unwrap().search_superset(key)
        } else {
            None
        }
    }

    /// Returns a mutable reference to the node covers full range of the `key`.
    fn search_superset_mut(&mut self, key: &Range) -> Option<&mut Self> {
        if self.key.contain(key) {
            Some(self)
        } else if key.max < self.key.min && self.left.is_some() {
            // Safe to unwrap() because we have just checked it.
            self.left.as_mut().unwrap().search_superset_mut(key)
        } else if key.min > self.key.max && self.right.is_some() {
            // Safe to unwrap() because we have just checked it.
            self.right.as_mut().unwrap().search_superset_mut(key)
        } else {
            None
        }
    }

    /// Rotate the node if necessary to keep balance.
    fn rotate(self) -> Box<Self> {
        let l = height(&self.left);
        let r = height(&self.right);
        match (l as i32) - (r as i32) {
            1 | 0 | -1 => Box::new(self),
            2 => self.rotate_left_successor(),
            -2 => self.rotate_right_successor(),
            _ => unreachable!(),
        }
    }

    /// Perform a single left rotation on this node.
    fn rotate_left(mut self) -> Box<Self> {
        let mut new_root = self.right.take().expect("Node is broken");
        self.right = new_root.left.take();
        self.update_cached_info();
        new_root.left = Some(Box::new(self));
        new_root.update_cached_info();
        new_root
    }

    /// Perform a single right rotation on this node.
    fn rotate_right(mut self) -> Box<Self> {
        let mut new_root = self.left.take().expect("Node is broken");
        self.left = new_root.right.take();
        self.update_cached_info();
        new_root.right = Some(Box::new(self));
        new_root.update_cached_info();
        new_root
    }

    /// Performs a rotation when the left successor is too high.
    fn rotate_left_successor(mut self) -> Box<Self> {
        let left = self.left.take().expect("Node is broken");
        if height(&left.left) < height(&left.right) {
            let rotated = left.rotate_left();
            self.left = Some(rotated);
            self.update_cached_info();
        } else {
            self.left = Some(left);
        }
        self.rotate_right()
    }

    /// Performs a rotation when the right successor is too high.
    fn rotate_right_successor(mut self) -> Box<Self> {
        let right = self.right.take().expect("Node is broken");
        if height(&right.left) > height(&right.right) {
            let rotated = right.rotate_right();
            self.right = Some(rotated);
            self.update_cached_info();
        } else {
            self.right = Some(right);
        }
        self.rotate_left()
    }

    fn delete_root(mut self) -> Option<Box<Self>> {
        match (self.left.take(), self.right.take()) {
            (None, None) => None,
            (Some(l), None) => Some(l),
            (None, Some(r)) => Some(r),
            (Some(l), Some(r)) => Some(Self::combine_subtrees(l, r)),
        }
    }

    /// Find the minimal key below the tree and returns a new optional tree where the minimal
    /// value has been removed and the (optional) minimal node as tuple (min_node, remaining)
    fn get_new_root(mut self) -> (Self, Option<Box<Self>>) {
        match self.left.take() {
            None => {
                let remaining = self.right.take();
                (self, remaining)
            }
            Some(left) => {
                let (min_node, left) = left.get_new_root();
                self.left = left;
                (min_node, Some(self.updated_node()))
            }
        }
    }

    fn combine_subtrees(l: Box<Self>, r: Box<Self>) -> Box<Self> {
        let (mut new_root, remaining) = r.get_new_root();
        new_root.left = Some(l);
        new_root.right = remaining;
        new_root.updated_node()
    }

    /// Update cached information of the node.
    /// Please make sure that the cached values of both children are up to date.
    fn update_cached_info(&mut self) {
        self.height = max(height(&self.left), height(&self.right)) + 1;
        self.max_key = max(max_key(&self.left), max(max_key(&self.right), self.key.max));
    }

    /// Update the sub-tree to keep balance.
    fn updated_node(mut self) -> Box<Self> {
        self.update_cached_info();
        self.rotate()
    }

    /// Insert a new (key, data) pair into the subtree.
    fn insert(mut self, key: Range, node_state: NodeState) -> Result<Box<Self>> {
        match self.key.cmp(&key) {
            Ordering::Equal => {
                return Err(Error::ResourceExhausted);
            }
            Ordering::Less => {
                if self.key.intersect(&key) {
                    return Err(Error::Overlap(key, self.key));
                }
                match self.right {
                    None => self.right = Some(Box::new(InnerNode::new(key, node_state))),
                    Some(_) => {
                        self.right = self
                            .right
                            .take()
                            .map(|n| n.insert(key, node_state).unwrap())
                    }
                }
            }
            Ordering::Greater => {
                if self.key.intersect(&key) {
                    return Err(Error::Overlap(key, self.key));
                }
                match self.left {
                    None => self.left = Some(Box::new(InnerNode::new(key, node_state))),
                    Some(_) => {
                        self.left = self.left.take().map(|n| n.insert(key, node_state).unwrap())
                    }
                }
            }
        }
        Ok(self.updated_node())
    }

    /// Delete `key` from the subtree.
    ///
    /// Note: it doesn't return whether the key exists in the subtree, so caller need to ensure the
    /// logic.
    fn delete(mut self, key: &Range) -> Option<Box<Self>> {
        match self.key.cmp(&key) {
            Ordering::Equal => {
                return self.delete_root();
            }
            Ordering::Less => {
                if let Some(node) = self.right.take() {
                    let right = node.delete(key);
                    self.right = right;
                    return Some(self.updated_node());
                }
            }
            Ordering::Greater => {
                if let Some(node) = self.left.take() {
                    let left = node.delete(key);
                    self.left = left;
                    return Some(self.updated_node());
                }
            }
        }
        Some(Box::new(self))
    }

    /// Update an existing entry and return the old value.
    fn update(&mut self, key: &Range, node_state: NodeState) -> Result<()> {
        match self.key.cmp(&key) {
            Ordering::Equal => {
                match (self.node_state, node_state) {
                    (NodeState::Free, NodeState::Free)
                    | (NodeState::Allocated, NodeState::Free)
                    | (NodeState::Allocated, NodeState::Allocated) => {
                        return Err(Error::AddressSlotNeverAllocated(self.key));
                    }
                    _ => {}
                }
                self.node_state.replace(node_state);
                Ok(())
            }
            Ordering::Less => match self.right.as_mut() {
                None => Err(Error::AddressSlotNeverAllocated(*key)),
                Some(node) => node.update(key, node_state),
            },
            Ordering::Greater => match self.left.as_mut() {
                None => Err(Error::AddressSlotNeverAllocated(*key)),
                Some(node) => node.update(key, node_state),
            },
        }
    }
}

/// Compute height of the optional sub-tree.
fn height(node: &Option<Box<InnerNode>>) -> u64 {
    node.as_ref().map_or(0, |n| n.height)
}

/// Compute maximum key value covered by the optional sub-tree.
fn max_key(node: &Option<Box<InnerNode>>) -> u64 {
    node.as_ref().map_or(0, |n| n.max_key)
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
