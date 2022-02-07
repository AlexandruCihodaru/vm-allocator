// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Manages system resources that can be allocated to VMs and their devices.

#![deny(missing_docs)]

mod allocation_engine;
mod id_allocator;

pub use crate::id_allocator::IdAllocator;
use std::fmt;
use std::result;

/// Error type for IdAllocator usage.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// All ids from the range specified are exhausted.
    Overflow,
    /// An id that is not part of the specified range was requested to be released.
    OutOfRange(u32),
    /// An id that was already released was requested to be released.
    AlreadyReleased(u32),
    /// An id  that was never allocated was requested to be released.
    IdNeverAllocated(u32),
    /// smth smth
    AddressSlotNeverAllocated(allocation_engine::Range),
    /// There are no more IDs available in the manage range
    ResourceExhausted,
    /// The range to manage is invalid.
    InvalidRange(u64, u64),
    /// Address is unaligned
    UnalignedAddress,
    /// Alignment value is invalid
    InvalidAlignment,
    /// smth smth
    Overlap(allocation_engine::Range, allocation_engine::Range),
}

impl std::error::Error for Error {}

/// Wrapper over std::result::Result
pub type Result<T> = result::Result<T, Error>;

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;

        match *self {
            Overflow => write!(f, "Id counter overflowed."),
            OutOfRange(id) => write!(f, "Specified id: {} is not in the range.", id),
            ResourceExhausted => {
                write!(f, "There are no more available ids in the specified range.")
            }
            AlreadyReleased(id) => write!(f, "Specified id: {} is already released.", id),
            IdNeverAllocated(id) => write!(
                f,
                "Specified id: {} was never allocated, can't release it",
                id
            ),
            InvalidRange(begin, end) => {
                write!(f, "The range specified: {}-{} is not valid.", begin, end)
            }
            UnalignedAddress => write!(f, "Address is unaligned."),
            InvalidAlignment => write!(f, "Alignment value is invalid."),
            Overlap(candidate, allocated_range) => write!(
                f,
                "Addresses are overlaping.{} intersects with existing {}",
                candidate, allocated_range
            ),
            AddressSlotNeverAllocated(range) => {
                write!(f, "Specufued range: {} was never allocated.", range)
            }
        }
    }
}
