// Copyright (C) 2022 Alibaba Cloud. All rights reserved.
// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2

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
