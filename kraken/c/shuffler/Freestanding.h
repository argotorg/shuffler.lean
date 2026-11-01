#pragma once

// Storage, status and compiler support for the freestanding shuffler.
#include "StackSlot.h"

#include <optional>
#include <type_traits>

/// A function that the Kraken proof treats as a separate unit. g++ must also not specialize it; clang does
/// not know noclone.
#if __has_cpp_attribute(gnu::noclone)
#define UNIT [[gnu::noinline, gnu::noclone]]
#else
#define UNIT [[gnu::noinline]]
#endif

namespace
{

/// The EVM stack limit
constexpr std::size_t maxStackSize = 1024;
constexpr std::size_t maxSwapDepth = 16;
constexpr std::size_t maxDupDepth = 15;

/// Whether a slot is a variable, Value.Var of the Lean model: a value that is not a literal. Only a variable can be
/// spilled.
constexpr bool isVariable(StackSlot const _slot)
{
	return _slot.isValue() && !_slot.isLiteralValue();
}

/// The value of T that Optional<T> takes as its empty state: a value that is never present
template<class T>
struct Niche;

/// build_bottom_up checks n <= maxStackSize, so an offset that is stored is below maxStackSize. (In
/// buildBottomUp, targetOffset is SIZE_MAX between the decrement and the increment, and is not stored then.)
template<>
struct Niche<StackOffset>
{
	static constexpr StackOffset value{SIZE_MAX};
};

/// std::optional<T> in the size of T: Niche<T>::value is the empty state
template<class T>
class Optional
{
public:
	constexpr Optional(std::nullopt_t): m_value(Niche<T>::value) {}
	/// `_value` is not Niche<T>::value
	constexpr Optional(T const _value): m_value(_value) {}

	constexpr bool has_value() const { return m_value != Niche<T>::value; }
	constexpr explicit operator bool() const { return has_value(); }
	/// Only for has_value()
	constexpr T const& operator*() const { return m_value; }
	constexpr T const* operator->() const { return &m_value; }
	/// As std::optional: empty is equal only to empty
	constexpr bool operator==(Optional const&) const = default;

private:
	T m_value;
};
static_assert(sizeof(Optional<StackOffset>) == sizeof(StackOffset));

/// An array with an element for each offset of the largest stack. The elements are not initialized: the
/// arrays are large, and each user writes an element before it reads it. The array is in a union, so
/// OffsetArray() initializes no element, and T needs no default constructor.
template<class T>
class OffsetArray
{
	static_assert(std::is_trivially_copyable_v<T> && std::is_trivially_destructible_v<T>);

public:
	OffsetArray() {}

	T& operator[](StackOffset const _offset) { return m_elements[_offset.value]; }
	T const& operator[](StackOffset const _offset) const { return m_elements[_offset.value]; }
	T* data() { return m_elements; }

private:
	union { T m_elements[maxStackSize]; };
};

/// What a step of the emission ends with: Shuffler.cpp's std::nullopt or Blocked, or a failed yulAssert
enum class [[nodiscard]] Status : std::uint8_t { Done, Blocked, AssertionFailed };

#define yulAssert(_condition, ...) do { if (!(_condition)) return Status::AssertionFailed; } while (false)

}
