/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

struct StackOffset
{
	explicit constexpr StackOffset(size_t _value) : value(_value) {}
	size_t value;
	auto operator<=>(StackOffset const&) const = default;
};
// comparison operations with size_t
constexpr auto operator<=>(StackOffset const lhs, size_t const rhs) noexcept { return lhs.value <=> rhs; }
constexpr auto operator<=>(size_t const lhs, StackOffset const rhs) noexcept { return lhs <=> rhs.value; }
constexpr bool operator==(StackOffset const lhs, size_t const rhs) noexcept { return lhs.value == rhs; }

/// Distance from the stack top (depth 0 = top).
/// Natural for stack operations (SWAP1 = swap with depth 1); used for operations that
/// conceptually work "from the top".
struct StackDepth
{
	explicit constexpr StackDepth(size_t _value) : value(_value) {}
	size_t value;
	auto operator<=>(StackDepth const&) const = default;
};
// comparison operations with size_t
constexpr auto operator<=>(StackDepth const lhs, size_t const rhs) noexcept { return lhs.value <=> rhs; }
constexpr auto operator<=>(size_t const lhs, StackDepth const rhs) noexcept { return lhs <=> rhs.value; }
constexpr bool operator==(StackDepth const lhs, size_t const rhs) noexcept { return lhs.value == rhs; }