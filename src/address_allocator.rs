// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// Copyright (C) 2019 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

use crate::allocation_engine::Range;
use crate::allocation_engine::{AllocPolicy, IntervalTree, NodeState};
use crate::Error;
use crate::Result;
use std::cmp::{max, min};
use std::fmt;
use std::result;

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

impl Constraint {
    /// Create a new constraint object with default settings.
    pub fn new(size: u64) -> Self {
        Constraint {
            size: u64::from(size),
            min: 0,
            max: std::u64::MAX,
            align: 4,
            policy: AllocPolicy::default(),
        }
    }

    /// Set the min constraint.
    pub fn min(mut self, min: u64) -> Self {
        self.min = min;
        self
    }

    /// Set the max constraint.
    pub fn max(mut self, max: u64) -> Self {
        self.max = max;
        self
    }

    /// Set the alignment constraint.
    pub fn align(mut self, align: u64) -> Self {
        self.align = align;
        self
    }

    /// Set the allocation policy.
    pub fn policy(mut self, policy: AllocPolicy) -> Self {
        self.policy = policy;
        self
    }
}

#[derive(Debug, PartialEq)]
pub struct AddressAllocator {
    base: u64,
    end: u64,
    interval_tree: IntervalTree,
}

impl AddressAllocator {
    pub fn new(base: u64, size: u64) -> std::result::Result<Self, Error> {
        if size == 0 {
            return Err(Error::InvalidSize);
        }
        let end = base.checked_add(size - 1);
        if !end.is_some() {
            return Err(Error::InvalidSize);
        }
        let interval_tree = IntervalTree::new();
        let mut address_allocator = AddressAllocator {
            base: base,
            end: end.unwrap(),
            interval_tree: interval_tree,
        };

        address_allocator
            .interval_tree
            .insert(Range::new(base, end.unwrap())?, NodeState::Free)?;
        Ok(address_allocator)
    }

    pub fn allocate(
        &mut self,
        _address: Option<u64>,
        size: u64,
        align_size: Option<u64>,
        alloc_policy: AllocPolicy,
    ) -> Result<Range> {
        if size == 0 {
            return Err(Error::InvalidSize);
        }

        let alignment = align_size.unwrap_or(4);
        if !alignment.is_power_of_two() || alignment == 0 {
            return Err(Error::UnalignedAddress);
        }

        let constraint = Constraint::new(size).align(alignment).policy(alloc_policy);
        let candidate = match self.interval_tree.root.as_mut() {
            None => None,
            Some(node) => node.find_candidate(&constraint),
        };

        match candidate {
            None => Err(Error::ResourceExhausted),
            Some(node) => {
                let node_key = node.key;
                let range = Range::new(
                    max(node_key.min, constraint.min),
                    min(node_key.max, constraint.max),
                )?;
                // Safe to unwrap because candidate satisfy the constraints.
                let aligned_key = match alloc_policy {
                    AllocPolicy::LastMatch => {
                        range.align_back(constraint.align, constraint.size).unwrap()
                    }
                    _ => range.align_forward(constraint.align).unwrap(),
                };

                let result = Range::new(aligned_key.min, aligned_key.min + constraint.size - 1)?;

                // Allocate a resource from the node, no need to split the candidate node.
                if node_key.min == aligned_key.min && node_key.len() == constraint.size {
                    self.interval_tree
                        .root
                        .as_mut()
                        .unwrap()
                        .update(&node_key, NodeState::Allocated)?;
                    return Ok(node_key);
                }

                // Split the candidate node.
                // TODO: following algorithm is not optimal in preference of simplicity.
                self.interval_tree.delete(&node_key);
                if aligned_key.min > node_key.min {
                    self.interval_tree.insert(
                        Range::new(node_key.min, aligned_key.min - 1)?,
                        NodeState::Free,
                    )?;
                }

                self.interval_tree.insert(result, NodeState::Free)?;
                if result.max < node_key.max {
                    self.interval_tree
                        .insert(Range::new(result.max + 1, node_key.max)?, NodeState::Free)?;
                }

                self.interval_tree
                    .root
                    .as_mut()
                    .unwrap()
                    .update(&result, NodeState::Allocated)?;
                Ok(result)
            }
        }
    }

    /// Free an allocated range and return the associated data.
    pub fn free(&mut self, key: &Range) -> Result<()> {
        let _ = self.interval_tree.delete(key);
        let mut range = *key;

        // Try to merge with adjacent free nodes.
        if range.min > 0 {
            if let Some((r, v)) = self
                .interval_tree
                .get_superset(&Range::new(range.min - 1, range.min - 1)?)
            {
                if v.is_free() {
                    range.min = r.min;
                }
            }
        }
        if range.max < std::u64::MAX {
            if let Some((r, v)) = self
                .interval_tree
                .get_superset(&Range::new(range.max + 1, range.max + 1)?)
            {
                if v.is_free() {
                    range.max = r.max;
                }
            }
        }

        if range.min < key.min {
            self.interval_tree
                .delete(&Range::new(range.min, key.min - 1)?);
        }
        if range.max > key.max {
            self.interval_tree
                .delete(&Range::new(key.max + 1, range.max)?);
        }
        self.interval_tree.insert(range, NodeState::Free)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_fails_overflow() {
        assert_eq!(
            AddressAllocator::new(u64::max_value(), 0x100).unwrap_err(),
            Error::InvalidSize
        );
    }

    #[test]
    fn new_fails_size_zero() {
        assert_eq!(
            AddressAllocator::new(0x1000, 0x0).unwrap_err(),
            Error::InvalidSize
        );
    }

    #[test]
    fn allocate_fails_alignment_zero() {
        let mut pool = AddressAllocator::new(0x1000, 0x10000).unwrap();
        assert_eq!(
            format!(
                "{}",
                pool.allocate(Some(0x1000), 0x100, Some(0), AllocPolicy::FirstMatch)
                    .unwrap_err()
            ),
            "Address is unaligned."
        );
    }

    #[test]
    fn allocate_fails_alignment_non_power_of_two() {
        let mut pool = AddressAllocator::new(0x1000, 0x10000).unwrap();
        assert_eq!(
            format!(
                "{}",
                pool.allocate(Some(0x1000), 0x100, Some(200), AllocPolicy::FirstMatch)
                    .unwrap_err()
            ),
            "Address is unaligned."
        );
        assert_eq!(
            format!(
                "{}",
                pool.allocate(Some(0x1000), 0x0, Some(5), AllocPolicy::FirstMatch)
                    .unwrap_err()
            ),
            "The size is invalid."
        );
    }

    #[test]
    fn allocate_fails_not_enough_space() {
        let mut pool = AddressAllocator::new(0x1000, 0x1000).unwrap();
        assert_eq!(
            pool.allocate(None, 0x800, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1000 as u64, 0x17ff as u64).unwrap()
        );
        assert!(pool
            .allocate(None, 0x900, Some(0x100), AllocPolicy::FirstMatch)
            .is_err());
        assert_eq!(
            pool.allocate(None, 0x400, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1800 as u64, 0x1bff as u64).unwrap()
        );
    }

    #[test]
    fn allocate_alignment() {
        let mut pool = AddressAllocator::new(0x1000, 0x1000).unwrap();
        assert_eq!(
            pool.allocate(None, 0x110, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1000 as u64, 0x110f as u64).unwrap()
        );
        assert_eq!(
            pool.allocate(None, 0x100, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1200 as u64, 0x12ff as u64).unwrap()
        );
        assert_eq!(
            pool.allocate(None, 0x10, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1300 as u64, 0x130f as u64).unwrap()
        );
        // ---------------------------------------------------
        let mut pool_reverse = AddressAllocator::new(0x1000, 0x10000).unwrap();
        assert_eq!(
            pool_reverse
                .allocate(None, 0x110, Some(0x100), AllocPolicy::LastMatch)
                .unwrap(),
            Range::new(0x10e00 as u64, 0x10f0f as u64).unwrap()
        );
        assert_eq!(
            pool_reverse
                .allocate(None, 0x100, Some(0x100), AllocPolicy::LastMatch)
                .unwrap(),
            Range::new(0x10d00 as u64, 0x10dff as u64).unwrap()
        );
        assert_eq!(
            pool_reverse
                .allocate(None, 0x10, Some(0x100), AllocPolicy::LastMatch)
                .unwrap(),
            Range::new(0x10c00 as u64, 0x10c0f as u64).unwrap()
        );
    }

    #[test]
    fn allocate_address() {
        let mut pool = AddressAllocator::new(0x1000, 0x1000).unwrap();
        assert_eq!(
            pool.allocate(Some(0x1000), 0x800, None, AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1000 as u64, 0x17ff as u64).unwrap()
        );

        assert_eq!(
            pool.allocate(Some(0x1a00), 0x100, None, AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1800 as u64, 0x18ff as u64).unwrap()
        );
    }

    #[test]
    fn allocate_address_alignment() {
        let mut pool = AddressAllocator::new(0x1000, 0x1000).unwrap();
        assert_eq!(
            pool.allocate(Some(0x1200), 0x800, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1000 as u64, 0x17ff as u64).unwrap()
        );

        // Unaligned request
        //  This will work when we add start address
        //assert_eq!(
        //    format!(
        //        "{}",
        //        pool.allocate(
        //            Some(0x1210),
        //            0x800,
        //            Some(0x100),
        //        )
        //        .unwrap_err()
        //    ),
        //    "No available ranges."
        //);

        // Aligned request
        assert_eq!(
            pool.allocate(Some(0x1b00), 0x100, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1800 as u64, 0x18ff as u64).unwrap()
        );
    }

    #[test]
    fn allocate_address_not_enough_space() {
        let mut pool = AddressAllocator::new(0x1000, 0x1000).unwrap();

        // First range is [0x1200:0x1a00]
        assert_eq!(
            pool.allocate(Some(0x1200), 0x800, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1000 as u64, 0x17ff as u64).unwrap()
        );

        // Second range is [0x1c00:0x1e00]
        assert_eq!(
            pool.allocate(Some(0x1c00), 0x200, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1800 as u64, 0x19ff as u64).unwrap()
        );

        // There is 0x200 between the first 2 ranges.
        // We ask for an available address but the range is too big
        assert_eq!(
            pool.allocate(Some(0x1b00), 0x800, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap_err(),
            Error::ResourceExhausted
        );

        // We ask for an available address, with a small enough range
        assert_eq!(
            pool.allocate(Some(0x1b00), 0x100, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1a00 as u64, 0x1aff as u64).unwrap()
        );
    }

    #[test]
    fn allocate_address_free_and_realloc() {
        let mut pool = AddressAllocator::new(0x1000, 0x1000).unwrap();

        // First range is [0x1200:0x1a00]
        assert_eq!(
            pool.allocate(Some(0x1200), 0x800, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1000 as u64, 0x17ff).unwrap()
        );

        let _ = pool.free(&Range::new(0x1000 as u64, 0x17ff as u64).unwrap());

        assert_eq!(
            pool.allocate(Some(0x1200), 0x800, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1000 as u64, 0x17ff).unwrap()
        );
    }

    #[test]
    fn allocate_address_free_fail_and_realloc() {
        let mut pool = AddressAllocator::new(0x1000, 0x1000).unwrap();

        // First range is [0x1200:0x1a00]
        assert_eq!(
            pool.allocate(Some(0x1000), 0x800, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1000 as u64, 0x17ff as u64).unwrap()
        );

        // We try to free a range smaller than the allocated one.
        //assert_eq!(
        //    format!("{:?}", pool.free(0x1000, 0x100)),
        //    "The range was not found."
        //);
        //
        //assert_eq!(
        //    format!(
        //        "{}",
        //        pool.allocate(
        //            Some(0x1200),
        //            0x800,
        //            Some(0x100),
        //        )
        //        .unwrap_err()
        //    ),
        //    "No available ranges."
        //);
    }

    #[test]
    fn allocate_address_fail_free_and_realloc() {
        let mut pool = AddressAllocator::new(0x1000, 0x1000).unwrap();

        //First allocation fails
        assert_eq!(
            pool.allocate(Some(0x1200), 0x2000, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap_err(),
            Error::ResourceExhausted
        );

        // We try to free a range that was not allocated.
        //assert_eq!(
        //    format!("{}", pool.free(GuestAddress(0x1200), 0x2000).unwrap_err()),
        //    "The range was not found."
        //);

        // Now we try an allocation that should succeed.
        assert_eq!(
            pool.allocate(Some(0x1200), 0x800, Some(0x100), AllocPolicy::FirstMatch)
                .unwrap(),
            Range::new(0x1000 as u64, 0x17ff as u64).unwrap()
        );
    }
}
