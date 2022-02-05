# Design

## Allocation engine

This implementation uses an interval tree that is specialised for allocation of
memory-mapped I/O and port I/O address space. The fields of the strctures
defined will have semantic meaning for this context (e.g node state to indicate
if a node in the tree is assigned or not to a device).

We offer three options for placing a memory slot in the managed address space:

1. `LastMatch` -> When using this allocation policy the allocator will try to
insert the range described by the constraint at the first available position
starting from the end of the managed address space.
2. `FirstMatch` -> When using this allocation policy the allocator will try to
insert the range described by the constraint at the first available position
starting from the begining of the managed address space.
3. `ExactMatch` -> When using this allocation policy the allocator will try to
insert the range at the exact position described by the constraint, otherwise
it will return an error.

```rust
/// Policy for resource allocation.
pub enum AllocPolicy {
    /// Allocate from the first matched entry.
    FirstMatch,
    /// Allocate first matched entry from the end of the range.
    LastMatch,
    // Allocate a memory slot starting with the specified addrres
    // if it is available.
    ExactMatch,
}
```

Struct `Constraint` is used to describe the overall information of the resource
needed to be allocated. This structure is also used by IntervalTree to know where
and how to allocate the resource.

```rust
/// Struct to describe resource allocation constraints.
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
```

## Interval tree

An interval tree is a tree data structure used for storing information about intervals.
Specifically, it allows one to efficiently identify intervals that are overlaping
with a given point, or another interval. We considered that this characteristic
makes this data structure appropriate to be used as an allocation engine for
memory slots inside an address space. The time complexity of an interval tree,
namely O(log ⁡n+m) for queries, O(log n) for creation and O(log n) for insertion
and deletion of nodes.

 ```rust
/// A closed interval range [min, max] used to describe a
/// memory slot that will be assigned to a device by the VMM.
/// This structure represents the key of the Node object in
/// the interval tree implementation.
pub struct Range {
    pub min: u64,
    pub max: u64,
}

/// Node state for interval tree nodes.
///
/// Valid state transition:
/// - None -> Free: IntervalTree::insert(key, NodeState::Free)
/// - Free -> Allocated: IntervalTree::insert(key, NodeState::Allocated)
/// - Allocated -> Free: IntervalTree::free()
/// - * -> None: IntervalTree::delete()
pub enum NodeState {
    /// Node is free.
    Free,
    /// Node is allocated.
    Allocated,
}

/// Internal tree node to implement interval tree.
pub(crate) struct InnerNode {
    /// Interval handled by this node.
    pub(crate) key: Range,
    /// State of the node, this can be `Free` or `Allocated`
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
```

## Usage

The concept of Interval Tree may seem complicated, but using vm-allocator to do
resource allocation and release is simple and straightforward.

To use the `IntervalTree` implementation as an address allocator one should first
create an interval tree object and give an address space as a root node.

```rust
pub struct AddressAllocator {
    base: u64,
    end: u64,
    interval_tree: IntervalTree,
}

impl AddressAllocator {
    pub fn new(base: u64, size: u64) -> std::result::Result<Self, Error> {
        let interval_tree = IntervalTree::new();
        let end = base.checked_add(size - 1)?;
        let mut address_allocator = AddressAllocator {
            base: base,
            end: end,
            interval_tree: interval_tree,
        };

        address_allocator
            .interval_tree
            .insert(Range::new(base, end)?, NodeState::Free)?;
        Ok(address_allocator)
    }
```

After, the user should create a constraint with the size for the resource, optionally
 the constraint could also contain the maximum, minimum and alignment for the
 constraint.

```rust
 pub fn allocate(
        &mut self,
        _address: Option<u64>,
        size: u64,
        align_size: Option<u64>,
        alloc_policy: AllocPolicy,
    ) -> Result<Range> {
        let constraint = Constraint::new(size).align(alignment).policy(alloc_policy);
        // some other code here
        if logical_condition {
            let key = self.interval_tree.find_candidate(&constaint);
            self.interval_tree.insert(key, NodeState::Allocated);
        }
    }
```

![Allocation example](/images/allocation_example.png)

## License

**!!!NOTICE**: The BSD-3-Clause license is not included in this template.
The license needs to be manually added because the text of the license file
also includes the copyright. The copyright can be different for different
crates. If the crate contains code from CrosVM, the crate must add the
CrosVM copyright which can be found
[here](https://chromium.googlesource.com/chromiumos/platform/crosvm/+/master/LICENSE).
For crates developed from scratch, the copyright is different and depends on
the contributors.
