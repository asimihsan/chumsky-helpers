// Copyright 2025 Asim Ihsan
//
// This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
// SPDX-License-Identifier: MPL-2.0

pub mod literal;
pub mod number;

use std::ops::Range;

// It's common for AST nodes to use a wrapper type that allows attaching span information to them
#[derive(Debug, Clone, PartialEq)]
pub struct Spanned<T>(T, Range<usize>);
