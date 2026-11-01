#pragma once

#include "SSACFGTypes.h"

#include <bit>
#include <compare>
#include <cstddef>
#include <cstdint>

/// StackSlot.h's StackSlot. The members are public, as C callers read them.
struct StackSlot
{
	enum class Kind : std::uint8_t { Value = 0, Junk = 1, FunctionCallReturnLabel = 2, FunctionReturnLabel = 3 };

	std::uint32_t payload;
	Kind kind;
	/// for Kind::Value: the opcode of the defining instruction
	InstOpcode valueOpcode;

	static constexpr StackSlot makeJunk() { return {0, Kind::Junk, InstOpcode::Unreachable}; }

	constexpr bool isValue() const { return kind == Kind::Value; }
	constexpr bool isLiteralValue() const { return valueOpcode == InstOpcode::Const; }
	constexpr bool isJunk() const { return kind == Kind::Junk; }
	constexpr bool isFunctionCallReturnLabel() const { return kind == Kind::FunctionCallReturnLabel; }
	constexpr bool isFunctionReturnLabel() const { return kind == Kind::FunctionReturnLabel; }

	/// The members as one word, to compare them with one compare in place of three. The shift drops the 2
	/// padding bytes, which the caller does not initialize.
	bool operator==(StackSlot const& _other) const
	{
		return (std::bit_cast<std::uint64_t>(*this) ^ std::bit_cast<std::uint64_t>(_other)) << 16 == 0;
	}
};
static_assert(sizeof(StackSlot) == 8 && alignof(StackSlot) == 4);
static_assert(offsetof(StackSlot, payload) == 0 && offsetof(StackSlot, kind) == 4 && offsetof(StackSlot, valueOpcode) == 5);
/// operator== needs the members in the low 6 bytes of the word
static_assert(std::endian::native == std::endian::little);

/// Whether a slot can be materialized on the stack top out of thin air, without a copy of it on the stack
constexpr bool canBeFreelyGenerated(StackSlot const _slot)
{
	return _slot.isLiteralValue() || _slot.isJunk() || _slot.isFunctionCallReturnLabel();
}

/// Array index into stack from the bottom (offset 0 = bottom)
struct StackOffset
{
	StackOffset() = default;  // for Emission::m_blocked
	explicit constexpr StackOffset(std::size_t const _value): value(_value) {}
	std::size_t value;
	constexpr auto operator<=>(StackOffset const&) const = default;
};
constexpr auto operator<=>(StackOffset const _lhs, std::size_t const _rhs) { return _lhs.value <=> _rhs; }
constexpr bool operator==(StackOffset const _lhs, std::size_t const _rhs) { return _lhs.value == _rhs; }

/// Distance from the stack top (depth 0 = top)
struct StackDepth
{
	explicit constexpr StackDepth(std::size_t const _value): value(_value) {}
	std::size_t value;
};
