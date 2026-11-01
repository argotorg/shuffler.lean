#pragma once

#include "StackSlot.h"

#include <cstddef>
#include <cstdint>

/// ShuffleTrace.h's ShuffleOp
struct ShuffleOp
{
	enum class Kind : std::uint8_t { Swap = 0, Dup = 1, Pop = 2, Push = 3, Load = 4, Store = 5 };

	Kind kind;
	/// the operand of SWAPn and DUPn, 0 for the others
	std::uint8_t depth;
	/// the slot of a Push or a Load, junk for the others
	StackSlot slot;

	static constexpr ShuffleOp swap(StackDepth const _depth)
	{
		return {Kind::Swap, static_cast<std::uint8_t>(_depth.value), StackSlot::makeJunk()};
	}
	static constexpr ShuffleOp dup(StackDepth const _depth)
	{
		return {Kind::Dup, static_cast<std::uint8_t>(_depth.value), StackSlot::makeJunk()};
	}
	static constexpr ShuffleOp pop() { return {Kind::Pop, 0, StackSlot::makeJunk()}; }
	static constexpr ShuffleOp push(StackSlot const _slot) { return {Kind::Push, 0, _slot}; }
	static constexpr ShuffleOp load(StackSlot const _slot) { return {Kind::Load, 0, _slot}; }
};
static_assert(sizeof(ShuffleOp) == 12 && alignof(ShuffleOp) == 4);
static_assert(offsetof(ShuffleOp, kind) == 0 && offsetof(ShuffleOp, depth) == 1 && offsetof(ShuffleOp, slot) == 4);
