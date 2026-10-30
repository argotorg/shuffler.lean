// Emission::buildBottomUp, Emission::removeSurplus, Emission::permuteAtLowestHeight, Emission::permute,
// Emission::pop and the MappingBuilder of solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp, freestanding, with the
// behavior of the Lean model, Shuffler/BuildBottomUp/Defs.lean, Shuffler/RemoveSurplus/Defs.lean,
// Shuffler/PermuteAtLowestHeight/Defs.lean, Shuffler/Permute/Defs.lean, State.pop of Shuffler/Emission/Defs.lean and
// buildMapping of Shuffler/BuildMapping/Defs.lean.
// The differences from Shuffler.cpp:
//
// - There are no exceptions, so a failed yulAssert returns Status::AssertionFailed.
// - The source stack of build_bottom_up has no surplus, so every slot has a destination.
// - The checks marked `Lean` come from the Lean model; Shuffler.cpp does not have them.
// - The MappingBuilder constructor of Shuffler.cpp is five functions, one for each phase, and the mapping is the
//   caller's.
#include <bit>
#include <compare>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <type_traits>

/// A function that the Kraken proof treats as a separate unit. g++ must also not specialize it; clang does
/// not know noclone.
#if __has_cpp_attribute(gnu::noclone)
#define UNIT [[gnu::noinline, gnu::noclone]]
#else
#define UNIT [[gnu::noinline]]
#endif

/// InstOpcode (SSACFGTypes.h): only the opcodes that this file uses
enum class InstOpcode : std::uint8_t { Const = 0, Unreachable = 5 };

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

namespace
{

/// The EVM stack limit
constexpr std::size_t maxStackSize = 1024;
constexpr std::size_t maxSwapDepth = 16;
constexpr std::size_t maxDupDepth = 15;

/// Whether a slot can be materialized on the stack top out of thin air, without a copy of it on the stack
constexpr bool canBeFreelyGenerated(StackSlot const _slot)
{
	return _slot.isLiteralValue() || _slot.isJunk() || _slot.isFunctionCallReturnLabel();
}

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

/// Stack.h's Stack: the working stack in a caller's buffer, with the trace of the operations on it
class Stack
{
public:
	Stack(StackSlot* const _data, std::size_t const _size, ShuffleOp* const _trace):
		m_data(_data), m_size(_size), m_trace(_trace)
	{}

	std::size_t size() const { return m_size; }
	std::size_t traceSize() const { return m_traceSize; }
	StackSlot const& operator[](StackOffset const _offset) const { return m_data[_offset.value]; }
	StackSlot const& top() const { return m_data[m_size - 1]; }
	StackOffset topOffset() const { return StackOffset{m_size - 1}; }
	StackDepth offsetToDepth(StackOffset const _offset) const { return StackDepth{m_size - 1 - _offset.value}; }

	void swap(StackOffset const _offset)
	{
		StackSlot const slot = m_data[_offset.value];
		m_data[_offset.value] = top();
		m_data[m_size - 1] = slot;
		record(ShuffleOp::swap(offsetToDepth(_offset)));
	}

	/// A non-literal value can only be pushed by a reload of its spill
	void push(StackSlot const _slot)
	{
		m_data[m_size++] = _slot;
		record(_slot.isValue() && !_slot.isLiteralValue() ? ShuffleOp::load(_slot) : ShuffleOp::push(_slot));
	}

	void dup(StackOffset const _offset)
	{
		record(ShuffleOp::dup(StackDepth{offsetToDepth(_offset).value + 1}));
		m_data[m_size] = m_data[_offset.value];
		m_size++;
	}

	Status pop()
	{
		yulAssert(m_size != 0);
		--m_size;
		record(ShuffleOp::pop());
		return Status::Done;
	}

private:
	void record(ShuffleOp const _op) { m_trace[m_traceSize++] = _op; }

	StackSlot* m_data;
	std::size_t m_size;
	ShuffleOp* m_trace;
	std::size_t m_traceSize = 0;
};

/// The partial bijection between the working stack's slots and target offsets: no offset is bound twice, a
/// target offset no slot is bound for is generated, and a slot without a destination is surplus
class Mapping
{
public:
	/// The mapping without bindings, Mapping.lean's ⊥: no slot of a stack of `_sourceSize` slots has a
	/// destination, and no slot is bound for a target offset below `_targetSize`
	Mapping(std::size_t const _sourceSize, std::size_t const _targetSize)
	{
		for (StackOffset pos{0}; pos < _sourceSize; ++pos.value)
			m_destinationOf[pos] = std::nullopt;
		for (StackOffset destination{0}; destination < _targetSize; ++destination.value)
			m_positionOf[destination] = std::nullopt;
	}

	/// A copy of the entries of `_other` for a stack of `_sourceSize` slots and `_targetSize` target offsets.
	/// The loops copy only these entries; a copy of the whole object would copy 16 KiB with memcpy or rep movs.
	Mapping(Mapping const& _other, std::size_t const _sourceSize, std::size_t const _targetSize)
	{
		for (StackOffset pos{0}; pos < _sourceSize; ++pos.value)
			m_destinationOf[pos] = _other.m_destinationOf[pos];
		for (StackOffset destination{0}; destination < _targetSize; ++destination.value)
			m_positionOf[destination] = _other.m_positionOf[destination];
	}

	Mapping(Mapping const&) = delete;
	Mapping& operator=(Mapping const&) = delete;

	/// The destination of the slot at `_pos`, or none for a surplus slot
	Optional<StackOffset> destinationOf(StackOffset const _pos) const { return m_destinationOf[_pos]; }
	Optional<StackOffset> positionOf(StackOffset const _destination) const { return m_positionOf[_destination]; }

	void bind(StackOffset const _pos, StackOffset const _destination)
	{
		m_destinationOf[_pos] = _destination;
		m_positionOf[_destination] = _pos;
	}

	void swapDestinations(StackOffset const _a, StackOffset const _b)
	{
		Optional<StackOffset> const destinationOfA = m_destinationOf[_a];
		m_destinationOf[_a] = m_destinationOf[_b];
		m_destinationOf[_b] = destinationOfA;
		if (Optional<StackOffset> const destination = m_destinationOf[_a])
			m_positionOf[*destination] = _a;
		if (Optional<StackOffset> const destination = m_destinationOf[_b])
			m_positionOf[*destination] = _b;
	}

	/// Removes the slot at `_top`, the top of the stack, with its binding. The entry of `_top` in
	/// m_destinationOf stays: it is above the stack, and the next push or dup binds it again.
	void pop(StackOffset const _top)
	{
		if (Optional<StackOffset> const destination = m_destinationOf[_top])
			m_positionOf[*destination] = std::nullopt;
	}

private:
	OffsetArray<Optional<StackOffset>> m_destinationOf;
	OffsetArray<Optional<StackOffset>> m_positionOf;
};

/// spill/SpillSet.h's SpillSet, the Lean model's SpillSet (a Finset VarId), in a caller's buffer: the variable id is
/// spilled if m_spilled[id] is not 0. The buffer has a byte for each variable id of the caller.
///
/// An aggregate: with a user-provided constructor, g++ -O1 changes the asm of build_bottom_up and emission_pop.
struct SpillSet
{
	/// SpillSet.is_spilled: Shuffler.cpp's free isSpilled and SpillSet::isSpilled. Only a variable can be spilled.
	constexpr bool isSpilled(StackSlot const _slot) const { return isVariable(_slot) && m_spilled[_slot.payload] != 0; }

	/// SpillSet.add: spills the variable `_slot`. SpillSet::add takes a variable id; Shuffler.cpp's Planner checks
	/// that the slot is a variable before it calls add (S:955, S:993). Defined after emission_pop.
	Status add(StackSlot _slot);

	std::uint8_t* m_spilled;
};

/// Shuffler.cpp's isSpilled
constexpr bool isSpilled(StackSlot const _slot, SpillSet const _spills)
{
	return _spills.isSpilled(_slot);
}

class Emission
{
public:
	/// The slot at `offset` of the working stack is out of reach by `excess` slots
	struct Blocked
	{
		StackOffset offset;
		std::size_t excess;
	};

	/// The source stack is `_stack`, and `_plannedMapping` maps it to the target. The working mapping starts as
	/// a copy of it; `_plannedMapping` must outlive the Emission.
	Emission(
		Stack const _stack,
		StackSlot const* const _target,
		std::size_t const _targetSize,
		Mapping const& _plannedMapping,
		std::uint8_t const* const _spills
	):
		m_target(_target),
		m_targetSize(_targetSize),
		// m_spills is a SpillSet const, so the Emission does not write _spills
		m_spills{const_cast<std::uint8_t*>(_spills)},
		m_stack(_stack),
		m_mapping(_plannedMapping, _stack.size(), _targetSize),
		m_pendingGenerations(0),
		m_plannedMapping(_plannedMapping)
	{
		for (StackOffset offset{0}; offset < _targetSize; ++offset.value)
			if (!m_mapping.positionOf(offset))
				++m_pendingGenerations;
	}

	std::size_t traceSize() const { return m_stack.traceSize(); }
	/// The height of the working stack
	std::size_t stackSize() const { return m_stack.size(); }
	/// Only after Status::Blocked
	Blocked blocked() const { return m_blocked; }
	/// The working mapping
	Mapping const& mapping() const { return m_mapping; }
	std::size_t pendingGenerations() const { return m_pendingGenerations; }

	/// Removes the top slot with its destination, if any. Shuffler.cpp pops the stack first, then the mapping;
	/// so does the Lean model, State.pop.
	///
	/// `used` makes it a root of the g++ call graph order, so g++ emits it after Emission::buildBottomUp: the asm
	/// and the .LB labels of the units before it stay as they are, and the Kraken proofs name those labels.
	[[gnu::used]] UNIT Status pop()
	{
		StackOffset const top = m_stack.topOffset();
		if (Status const status = m_stack.pop(); status != Status::Done)
			return status;
		m_mapping.pop(top);
		return Status::Done;
	}

	/// Builds the target bottom-up. Every offset either holds its slot already, gets a retained slot that is
	/// floating above it, or gets a freshly generated slot.
	/// Once everything is generated the rest is one final permutation.
	///
	/// Loop invariant: every offset below `targetOffset` is final, i.e., holds the slot bound for it.
	UNIT Status buildBottomUp()
	{
		for (StackOffset targetOffset{0}; targetOffset < m_targetSize; ++targetOffset.value)
		{
			// the offset exists and already holds the slot bound for it: nothing to do
			if (targetOffset < m_stack.size() && isFinal(targetOffset))
				continue;

			// all is generated, the final permutation
			if (m_pendingGenerations == 0)
			{
				yulAssert(m_stack.size() == m_targetSize);
				// every slot goes to the offset it is bound for
				OffsetArray<StackOffset> permutation;
				for (StackOffset pos{0}; pos < m_stack.size(); ++pos.value)
				{
					Optional<StackOffset> const destination = m_mapping.destinationOf(pos);
					yulAssert(destination.has_value());
					permutation[pos] = *destination;
				}
				return permute(permutation);
			}

			// a target offset that needs something DUPed urgently before it goes out of dup reach
			Optional<StackOffset> urgentToDup = std::nullopt;
			for (StackOffset offset = targetOffset; offset < m_targetSize; ++offset.value)  // going bottom-up so we can start from targetOffset
			{
				// only offsets no slot is bound for yet (ie that need to be duped) can be urgent
				if (m_mapping.positionOf(offset))
					continue;
				StackSlot const slot = m_target[offset.value];
				if (slot.isJunk() || canBeFreelyGenerated(slot) || isSpilled(slot))
					continue;
				if (Optional<StackOffset> const sourceCopy = shallowestCopyPosition(slot))
				{
					if (!isDupReachable(*sourceCopy))
						return blockDupUnreachable(*sourceCopy);
					// a copy sitting at the offset being filled floats to the top when it is, so no hurry
					if (depthOf(*sourceCopy).value == maxDupDepth && *sourceCopy != targetOffset && !urgentToDup)
						urgentToDup = offset;
				}
			}

			if (
				urgentToDup &&  // if there is a slot that is about to go out of dup range but demands more copies
				*urgentToDup != targetOffset &&  // and it's not the target offset anyways
				m_stack.size() - targetOffset.value < maxSwapDepth  // and duping it doesn't make the target go out of swap range
			)
			{
				// generate it
				if (Status const status = generate(*urgentToDup); status != Status::Done)
					return status;
				// and revisit the current target in the next iteration (with unsigned wrapping this is also fine for 0)
				--targetOffset.value;
				continue;
			}

			// a slot whose offset is exactly where the result of a dup would end up is in place for free,
			// as long as nothing is urgent and targetOffset stays in reach for the slot generated after it
			StackOffset const sourceTop{m_stack.size()};
			if (
				!urgentToDup &&  // nothing urgent
				sourceTop > targetOffset &&  // the new top sits above the current targetOffset
				sourceTop < m_targetSize &&  // the new top is in the target offset range
				!m_mapping.positionOf(sourceTop) &&  // no slot is bound for the offset at the source top yet
				sourceTop.value - targetOffset.value < maxSwapDepth  // targetOffset stays in swap reach
			)
			{
				// we generate the slot demanded at source top
				if (Status const status = generate(sourceTop); status != Status::Done)
					return status;
				// revisit target offset
				--targetOffset.value;
				continue;
			}

			if (
				m_mapping.positionOf(targetOffset).has_value()  // a slot is bound for the target: retained or generated already
			)
			{
				// We go bottom-up, so the slot that should go into targetOffset is somewhere above
				// Any equal slot that is not in place will do the trick: the one at `targetOffset` itself, else the shallowest one
				Optional<StackOffset> const boundForTarget = m_mapping.positionOf(targetOffset);
				yulAssert(
					boundForTarget.has_value() && *boundForTarget >= targetOffset,
					"slot bound for the offset being filled is missing or already below it"
				);
				StackOffset const sourceForTargetOffset = *boundForTarget;
				StackSlot const& slot = m_stack[sourceForTargetOffset];
				StackOffset pos = sourceForTargetOffset;
				if (m_stack[targetOffset] == slot)
					// if the slot currently occupying targetOffset happens to be an equal copy of that value we're done
					// and can set `pos` directly to the target offset
					pos = targetOffset;
				else
					// otherwise search if there is an equal, movable copy shallower than carrier
					for (StackOffset candidate = m_stack.topOffset(); candidate > sourceForTargetOffset; --candidate.value)
						if (m_stack[candidate] == slot && !isFinal(candidate))
						{
							pos = candidate;
							break;
						}

				// we picked a valid `pos`
				yulAssert(m_stack[pos] == m_stack[sourceForTargetOffset]);

				// update the destinations if needed
				m_mapping.swapDestinations(pos, sourceForTargetOffset);

				// we're already done
				if (pos == targetOffset)
					continue;

				// if `pos` is not already at the top of the stack, swap it up
				if (pos != m_stack.topOffset())
				{
					if (!isSwapReachable(pos))
						return blockSwapUnreachable(pos);  // bail
					if (Status const status = swapWith(pos); status != Status::Done)
						return status;
				}
			}
			else
			{
				// the slot needs to be DUPed
				if (Status const status = generate(targetOffset); status != Status::Done)
					return status;

				// `generate` might have already placed the slot into the target offset, then we're done for this offset
				yulAssert(targetOffset < m_stack.size());  // Lean
				if (isFinal(targetOffset))
					continue;
			}

			// we might have to swap the top down into the target offset
			yulAssert(targetOffset < m_stack.size());  // Lean
			yulAssert(!isFinal(targetOffset));
			if (targetOffset != m_stack.topOffset())
			{
				if (!isSwapReachable(targetOffset))
					return blockSwapUnreachable(targetOffset);
				if (Status const status = swapWith(targetOffset); status != Status::Done)
					return status;
			}
		}
		yulAssert(m_stack.size() == m_targetSize);
		return Status::Done;
	}

	/// Pops all surplus slots, or blocks if a surplus slot that has to be popped is out of swap reach. Defined after
	/// spill_set.
	Status removeSurplus();

	/// At the lowest height, permutes every slot to its destination, or, if the destination is above the stack,
	/// into a hole: an offset whose target slot the planned mapping does not bind. Defined after permute.
	Status permuteAtLowestHeight();

private:
	/// Produces the slot for `_targetOffset`
	UNIT Status produce(StackOffset const _targetOffset)
	{
		StackSlot const slot = m_target[_targetOffset.value];
		Optional<StackOffset> const copy = shallowestCopyPosition(slot);
		Status status;
		if (slot.isJunk())
			status = push(slot, _targetOffset);
		else if (copy && isDupReachable(*copy))
			status = dup(*copy, _targetOffset);
		else if (canBeFreelyGenerated(slot) || isSpilled(slot))
			status = push(slot, _targetOffset);
		else if (copy)
			return blockDupUnreachable(*copy);
		else
			yulAssert(false, "generated slot has no copy on the stack and is not spilled");
		if (status != Status::Done)
			return status;
		yulAssert(m_mapping.positionOf(_targetOffset) == m_stack.topOffset());
		--m_pendingGenerations;
		return Status::Done;
	}

	/// Produces the slot for `_targetOffset` and moves it toward its place right away: if the offset exists
	/// already and holds a slot that is not final, a single swap places the produced slot and floats the other
	/// one, which may be its own placement. An equal slot there just takes over the destination.
	UNIT Status generate(StackOffset const _targetOffset)
	{
		yulAssert(_targetOffset < m_targetSize);  // Lean
		if (Status const status = produce(_targetOffset); status != Status::Done)
			return status;
		// `produce` left the slot on top; swap it down only if its offset exists strictly below the top:
		// as the top itself it is in place already, beyond the height it has to wait on top anyway
		if (_targetOffset.value + 1 < m_stack.size() && !isFinal(_targetOffset))
		{
			if (m_stack[_targetOffset] == m_stack.top())
				// an equal slot stands at the offset: retag instead of swapping two equal slots
				m_mapping.swapDestinations(_targetOffset, m_stack.topOffset());
			else if (isSwapReachable(_targetOffset))
				return swapWith(_targetOffset);
			// out of swap reach: leave the slot on top; buildBottomUp re-checks reach when filling the offset
		}
		return Status::Done;
	}

public:
	/// Shuffler.cpp's permute: the slot at each offset `pos` goes to the offset `_permutation[pos]`, a permutation
	/// of the offsets of the working stack. permute changes the array in place: the regroup and each pass write it.
	/// Shuffler.cpp takes the permutation by value; here the caller owns the array (8 KiB), so that the frame of
	/// permute does not hold a copy. The differences from Shuffler.cpp, as in the Lean model: the groups of equal
	/// slots come from a mark per offset, not from a sort; an empty stack is done; and a swap does not assert that
	/// the slot is not final.
	UNIT Status permute(OffsetArray<StackOffset>& _permutation)
	{
		if (m_stack.size() == 0)  // Lean
			return Status::Done;

		// Equal slots are interchangeable: among them, those already at one of their desired offsets stay, the
		// others take the remaining offsets. Otherwise equal slots would pass each other in cycles.
		// A group is the offsets of equal slots, and the highest of them is its leader. desiredBy[offset] is
		// the leader of the group that desires the offset, or none before that group.
		OffsetArray<Optional<StackOffset>> desiredBy;
		for (StackOffset offset{0}; offset < m_stack.size(); ++offset.value)
			desiredBy[offset] = std::nullopt;
		for (StackOffset leader{0}; leader < m_stack.size(); ++leader.value)
		{
			StackSlot const slot = m_stack[leader];
			if (shallowestCopyPosition(slot) != leader)
				continue;
			// the group's desired offsets
			for (StackOffset pos{0}; pos <= leader; ++pos.value)
				if (m_stack[pos] == slot)
					desiredBy[_permutation[pos]] = leader;
			// slots already standing on one of the group's desired offsets stay put, the others take the vacant
			// offsets (desired, but not in the group), both sides ascending, so nothing crosses
			StackOffset vacant{0};
			for (StackOffset pos{0}; pos <= leader; ++pos.value)
			{
				if (!(m_stack[pos] == slot))
					continue;
				if (desiredBy[pos] == leader)
				{
					_permutation[pos] = pos;
					continue;
				}
				while (vacant < m_stack.size() && !(desiredBy[vacant] == leader && !(m_stack[vacant] == slot)))
					++vacant.value;
				yulAssert(vacant < m_stack.size(), "movers and vacant must have the same size");
				_permutation[pos] = vacant;
				++vacant.value;
			}
		}

		// _permutation is a permutation of the offsets. Let m be the number of offsets i with _permutation[i] != i,
		// and t be 1 if _permutation[top] == top, else 0. Then 3 <= 2 m + 3 t <= 2 size() + 1, and each iteration
		// that does not return lowers 2 m + 3 t. Thus the loop ends after at most 2 size() - 1 iterations.
		StackOffset const top = m_stack.topOffset();
		while (true)
		{
			StackOffset pos = _permutation[top];
			if (pos == top)
			{
				// the top is in place: find the shallowest misplaced slot
				for (StackOffset candidate = top; candidate.value-- > 0;)
					if (_permutation[candidate] != candidate)
					{
						pos = candidate;
						break;
					}
				// nothing misplaced was found, we're done
				if (pos == top)
					return Status::Done;
			}
			// an equal slot at `pos` serves the top's destination just as well; a misplaced slot equal to the
			// top takes over the top's destination, making the top the misplaced one
			if (m_stack[pos] == m_stack.top())
				m_mapping.swapDestinations(pos, top);
			else if (!isSwapReachable(pos))
				return blockSwapUnreachable(pos);
			else
			{
				m_stack.swap(pos);
				m_mapping.swapDestinations(pos, top);
			}
			StackOffset const desired = _permutation[pos];
			_permutation[pos] = _permutation[top];
			_permutation[top] = desired;
		}
	}

private:
	UNIT bool isSpilled(StackSlot const _slot) const { return m_spills.isSpilled(_slot); }

	/// Whether the slot at `_pos` has no target offset to go to and is to be popped
	bool isSurplus(StackOffset const _pos) const { return !m_mapping.destinationOf(_pos).has_value(); }

	/// Whether the slot at `_pos` is bound for `_pos` itself, i.e., already is at its final target offset
	bool isFinal(StackOffset const _pos) const { return m_mapping.destinationOf(_pos) == _pos; }

	/// Depth of the slot at `_pos` below the top of the working stack
	StackDepth depthOf(StackOffset const _pos) const { return m_stack.offsetToDepth(_pos); }

	/// Whether a swap can reach the slot at `_pos`; trivially true for the top itself
	bool isSwapReachable(StackOffset const _pos) const { return depthOf(_pos).value <= maxSwapDepth; }

	/// Whether a dup can reach the slot at `_pos`
	bool isDupReachable(StackOffset const _pos) const { return depthOf(_pos).value <= maxDupDepth; }

	UNIT Optional<StackOffset> shallowestCopyPosition(StackSlot const _slot) const
	{
		for (StackOffset pos{m_stack.size()}; pos.value-- > 0;)
			if (m_stack[pos] == _slot)
				return pos;
		return std::nullopt;
	}

	/// Swaps the top with the slot at `_pos`, the destinations traveling along
	UNIT Status swapWith(StackOffset const _pos)
	{
		yulAssert(_pos < m_stack.size());  // Lean
		yulAssert(!isFinal(_pos), "swapping a final slot out of place");
		StackDepth const depth = depthOf(_pos);
		yulAssert(1 <= depth.value && depth.value <= maxSwapDepth, "invalid swap target");
		m_stack.swap(_pos);
		m_mapping.swapDestinations(_pos, m_stack.topOffset());
		return Status::Done;
	}

	UNIT Status push(StackSlot const _slot, StackOffset const _destination)
	{
		m_stack.push(_slot);
		yulAssert(!m_mapping.positionOf(_destination), "destination already bound to a slot");
		m_mapping.bind(m_stack.topOffset(), _destination);
		return Status::Done;
	}

	UNIT Status dup(StackOffset const _copy, StackOffset const _destination)
	{
		// Stack.h's dup
		yulAssert(!m_stack[_copy].isFunctionReturnLabel(), "Cannot dup function return label");
		m_stack.dup(_copy);
		yulAssert(!m_mapping.positionOf(_destination), "destination already bound to a slot");
		m_mapping.bind(m_stack.topOffset(), _destination);
		return Status::Done;
	}

	/// The slot at `_position` is out of reach by `_excess` slots
	Status block(StackOffset const _position, std::size_t const _excess)
	{
		yulAssert(_excess > 0);
		m_blocked = {_position, _excess};
		return Status::Blocked;
	}

	/// A swap cannot reach the slot at `_position`
	Status blockSwapUnreachable(StackOffset const _position)
	{
		return block(_position, depthOf(_position).value - maxSwapDepth);
	}

	/// A dup cannot reach the slot at `_position`
	Status blockDupUnreachable(StackOffset const _position)
	{
		return block(_position, depthOf(_position).value - maxDupDepth);
	}

	StackSlot const* m_target;
	std::size_t m_targetSize;
	/// Shuffler.cpp's SpillSet const&: the Emission does not spill
	SpillSet const m_spills;

	/// The working stack and its (in sync) mapping
	Stack m_stack;
	Mapping m_mapping;
	/// Number of target offsets whose slot still has to be produced; decremented by `produce`
	std::size_t m_pendingGenerations;
	Blocked m_blocked;
	/// The mapping of the source stack to the target, State.planned_mapping. After the other members, so that
	/// their offsets stay.
	Mapping const& m_plannedMapping;
};

}

/// The Emission constructor and Emission::buildBottomUp for a source stack of m slots without surplus: data holds
/// the source slots and dest[i] is the target offset of source slot i. Writes the operations to ops and returns their
/// number, also when a slot is out of reach. Then blocked gets its offset and its excess, which is positive, else
/// 0 and 0. Returns -2 for a failed assertion. If the result is not -2, data holds the slots of the working stack
/// after the operations: the n slots of the target if blocked[1] is 0.
///
/// dest holds distinct offsets below n (none, SIZE_MAX, is a slot without a destination), every variable id in
/// target is an index of spilled, data has room for n slots and ops for 6n entries. m <= n <= 1024, else the result
/// is -2.
extern "C" std::int64_t build_bottom_up(
	std::uint64_t const m,
	std::uint64_t const n,
	StackSlot* const data,
	StackSlot const* const target,
	Optional<StackOffset> const* const dest,
	std::uint8_t const* const spilled,
	ShuffleOp* const ops,
	std::uint64_t* const blocked
)
{
	// the mapping has room for maxStackSize offsets
	if (m > n || n > maxStackSize)
		return -2;
	Mapping planned{m, n};
	for (StackOffset pos{0}; pos < m; ++pos.value)
		if (Optional<StackOffset> const destination = dest[pos.value])
			planned.bind(pos, *destination);
	Emission emission{Stack{data, m, ops}, target, n, planned, spilled};
	switch (emission.buildBottomUp())
	{
	case Status::Done:
		blocked[0] = 0;
		blocked[1] = 0;
		return static_cast<std::int64_t>(emission.traceSize());
	case Status::Blocked:
		blocked[0] = emission.blocked().offset.value;
		blocked[1] = emission.blocked().excess;
		return static_cast<std::int64_t>(emission.traceSize());
	case Status::AssertionFailed:
		return -2;
	}
	__builtin_unreachable();
}

/// The Emission constructor and `count` calls of Emission::pop, for a source stack of m slots and a target of n
/// slots: data holds the source slots and dest[i] is the target offset of source slot i, or none (SIZE_MAX).
/// Writes the operations to ops and returns their number, count. Writes the destination of each of the m - count
/// slots that stay to destinationOf, the position of the slot bound for each of the n target offsets, or none, to
/// positionOf, and the number of target offsets that no slot of the source stack is bound for to pending. Returns
/// -2 for a failed assertion: a pop of an empty stack.
///
/// dest holds distinct offsets below n, and ops has room for count entries. m, n <= 1024, else the result is -2.
extern "C" std::int64_t emission_pop(
	std::uint64_t const m,
	std::uint64_t const n,
	StackSlot* const data,
	StackSlot const* const target,
	Optional<StackOffset> const* const dest,
	std::uint8_t const* const spilled,
	std::uint64_t const count,
	ShuffleOp* const ops,
	Optional<StackOffset>* const destinationOf,
	Optional<StackOffset>* const positionOf,
	std::uint64_t* const pending
)
{
	// the mapping has room for maxStackSize offsets
	if (m > maxStackSize || n > maxStackSize)
		return -2;
	Mapping planned{m, n};
	for (StackOffset pos{0}; pos < m; ++pos.value)
		if (Optional<StackOffset> const destination = dest[pos.value])
			planned.bind(pos, *destination);
	Emission emission{Stack{data, m, ops}, target, n, planned, spilled};
	// a pop of an empty stack fails, so the loop ends after at most m + 1 pops
	for (std::uint64_t i = 0; i < count; ++i)
		if (emission.pop() != Status::Done)
			return -2;
	for (StackOffset pos{0}; pos < m - count; ++pos.value)
		destinationOf[pos.value] = emission.mapping().destinationOf(pos);
	for (StackOffset destination{0}; destination < n; ++destination.value)
		positionOf[destination.value] = emission.mapping().positionOf(destination);
	*pending = emission.pendingGenerations();
	return static_cast<std::int64_t>(emission.traceSize());
}

namespace
{

// `used` and this place make g++ emit add after emission_pop, so the asm of the units above and their labels stay
[[gnu::used]] UNIT Status SpillSet::add(StackSlot const _slot)
{
	yulAssert(isVariable(_slot), "spill candidate must be a variable");  // Lean
	yulAssert(m_spilled[_slot.payload] == 0, "can't spill a value twice");
	m_spilled[_slot.payload] = 1;
	return Status::Done;
}

}

/// SpillSet::add for each of the addCount slots of adds, in order, on the spill set in spilled: the variable id is
/// spilled if spilled[id] is not 0. Then results[i] is 1 if the slot queries[i] is spilled, else 0. Returns 0, or -2
/// for a failed assertion: an add of a slot that is not a variable, or of a variable that is spilled. Then spilled
/// holds the adds before it, and results is not written.
///
/// spilled has idCount bytes, and results has room for queryCount entries. The id of each variable in adds and
/// queries is below idCount, else the result is -2 and nothing is written.
extern "C" std::int64_t spill_set(
	std::uint64_t const idCount,
	std::uint8_t* const spilled,
	StackSlot const* const adds,
	std::uint64_t const addCount,
	StackSlot const* const queries,
	std::uint64_t const queryCount,
	std::uint8_t* const results
)
{
	for (std::uint64_t i = 0; i < addCount; ++i)
		if (isVariable(adds[i]) && adds[i].payload >= idCount)
			return -2;
	for (std::uint64_t i = 0; i < queryCount; ++i)
		if (isVariable(queries[i]) && queries[i].payload >= idCount)
			return -2;
	SpillSet spills{spilled};
	for (std::uint64_t i = 0; i < addCount; ++i)
		if (spills.add(adds[i]) != Status::Done)
			return -2;
	for (std::uint64_t i = 0; i < queryCount; ++i)
		results[i] = isSpilled(queries[i], spills);
	return 0;
}

namespace
{

// `used` and this place make g++ emit removeSurplus after spill_set, so the asm of the units above and their labels
// stay
[[gnu::used]] UNIT Status Emission::removeSurplus()
{
	while (m_stack.size() != 0)
	{
		// scan from the top down: the first surplus slot is the shallowest, the last reachable one the deepest
		Optional<StackOffset> shallowestSurplus = std::nullopt;
		Optional<StackOffset> deepestReachableSurplus = std::nullopt;
		for (StackOffset pos{m_stack.size()}; pos.value-- > 0;)
			if (isSurplus(pos))
			{
				if (!shallowestSurplus)
					shallowestSurplus = pos;
				if (isSwapReachable(pos))
					deepestReachableSurplus = pos;
			}
		if (!shallowestSurplus)
			break;
		// there is a surplus but we can't reach it
		if (!deepestReachableSurplus)
			return blockSwapUnreachable(*shallowestSurplus);

		if (StackOffset const stackTopOffset = m_stack.topOffset(); *shallowestSurplus != stackTopOffset)
		{
			// a surplus slot equal to the top takes over the top's destination, so the top itself can be popped
			Optional<StackOffset> equalSurplus = std::nullopt;
			for (StackOffset pos = stackTopOffset; pos.value-- > 0;)
				if (isSurplus(pos) && m_stack[pos] == m_stack.top())
				{
					equalSurplus = pos;
					break;
				}
			if (equalSurplus)
				m_mapping.swapDestinations(*equalSurplus, stackTopOffset);
			else if (Status const status = swapWith(*deepestReachableSurplus); status != Status::Done)
				return status;
		}
		if (Status const status = pop(); status != Status::Done)
			return status;
	}
	return Status::Done;
}

}

/// The Emission constructor and Emission::removeSurplus for a stack of m slots and a target of n slots: data holds the
/// slots and dest[i] is the target offset of slot i, or none (SIZE_MAX) for a surplus slot. Writes the operations to
/// ops and returns their number, also when a surplus slot is out of reach. Then blocked gets its offset and its
/// excess, which is positive, else 0 and 0. Returns -2 for a failed assertion. If the result is not -2, height gets
/// the height of the working stack, data holds its slots, and the first height entries of dest hold their
/// destinations; the other entries of dest are not written.
///
/// dest holds distinct offsets below n, and ops has room for 2m entries: each pass of removeSurplus pops a slot,
/// after at most one swap. m, n <= 1024, else the result is -2. spilled has idCount bytes, the spill set of the
/// state; removeSurplus does not read it.
extern "C" std::int64_t remove_surplus(
	std::uint64_t const m,
	std::uint64_t const n,
	StackSlot* const data,
	StackSlot const* const target,
	Optional<StackOffset>* const dest,
	std::uint8_t const* const spilled,
	[[maybe_unused]] std::uint64_t const idCount,
	ShuffleOp* const ops,
	std::uint64_t* const blocked,
	std::uint64_t* const height
)
{
	// the mapping has room for maxStackSize offsets
	if (m > maxStackSize || n > maxStackSize)
		return -2;
	Mapping planned{m, n};
	for (StackOffset pos{0}; pos < m; ++pos.value)
		if (Optional<StackOffset> const destination = dest[pos.value])
			planned.bind(pos, *destination);
	Emission emission{Stack{data, m, ops}, target, n, planned, spilled};
	switch (emission.removeSurplus())
	{
	case Status::Done:
		blocked[0] = 0;
		blocked[1] = 0;
		break;
	case Status::Blocked:
		blocked[0] = emission.blocked().offset.value;
		blocked[1] = emission.blocked().excess;
		break;
	case Status::AssertionFailed:
		return -2;
	}
	*height = emission.stackSize();
	for (StackOffset pos{0}; pos < emission.stackSize(); ++pos.value)
		dest[pos.value] = emission.mapping().destinationOf(pos);
	return static_cast<std::int64_t>(emission.traceSize());
}

/// The Emission constructor and Emission::permute for a stack of h slots: data holds the slots, and the slot i goes to
/// the offset perm[i]. The state is the state of Fuzz/Oracle.lean's runPermute: the target is the permuted stack, the
/// mapping binds slot i to perm[i], and the spill set is empty. permute reads neither the target nor the spill set,
/// so spilled is null. Writes the operations to ops and returns their number, also when a slot is out of reach. Then
/// blocked gets its offset and its excess, which is positive, else 0 and 0. Returns -2 for a failed assertion. If the
/// result is not -2, data holds the slots of the working stack, and dest the destination of each of its h slots.
/// permute does not write perm.
///
/// perm is a permutation of 0..h-1, and ops has room for 2h entries: permute makes at most 2h - 1 passes, each with
/// at most one swap. h <= 1024, else the result is -2 and nothing is written.
extern "C" std::int64_t permute(
	std::uint64_t const h,
	StackSlot* const data,
	std::uint64_t const* const perm,
	ShuffleOp* const ops,
	std::uint64_t* const blocked,
	Optional<StackOffset>* const dest
)
{
	// the mapping has room for maxStackSize offsets
	if (h > maxStackSize)
		return -2;
	OffsetArray<StackOffset> permutation;
	OffsetArray<StackSlot> target;
	Mapping planned{h, h};
	for (StackOffset pos{0}; pos < h; ++pos.value)
	{
		permutation[pos] = StackOffset{perm[pos.value]};
		target[permutation[pos]] = data[pos.value];
		planned.bind(pos, permutation[pos]);
	}
	Emission emission{Stack{data, h, ops}, target.data(), h, planned, nullptr};
	switch (emission.permute(permutation))
	{
	case Status::Done:
		blocked[0] = 0;
		blocked[1] = 0;
		break;
	case Status::Blocked:
		blocked[0] = emission.blocked().offset.value;
		blocked[1] = emission.blocked().excess;
		break;
	case Status::AssertionFailed:
		return -2;
	}
	for (StackOffset pos{0}; pos < h; ++pos.value)
		dest[pos.value] = emission.mapping().destinationOf(pos);
	return static_cast<std::int64_t>(emission.traceSize());
}

namespace
{

// `used` and this place make g++ emit permuteAtLowestHeight after permute, so the asm of the units above and their
// labels stay
[[gnu::used]] UNIT Status Emission::permuteAtLowestHeight()
{
	OffsetArray<StackOffset> permutation;
	// offsets whose target slots will be generated later, and the slots that wait for one of them
	OffsetArray<StackOffset> holes;
	OffsetArray<StackOffset> parked;
	std::size_t holeCount = 0;
	std::size_t parkedCount = 0;
	// each offset below the height gets one entry of permutation, so permutation needs no initial value
	for (StackOffset pos{0}; pos < m_stack.size(); ++pos.value)
	{
		// all surplus is gone, so every slot has a destination
		Optional<StackOffset> const destination = m_mapping.destinationOf(pos);
		yulAssert(destination.has_value(), "every source slot must be bound");
		yulAssert(pos < m_targetSize);  // Lean
		// no slot is planned for the target offset pos, so its slot has to be generated
		bool const isHole = !m_plannedMapping.positionOf(pos).has_value();
		// the destination can not be served yet
		bool const isParked = *destination >= m_stack.size();
		if (!isParked)
			permutation[pos] = *destination;
		if (isParked && isHole)
			permutation[pos] = pos;
		if (isParked && !isHole)
			parked[StackOffset{parkedCount++}] = pos;
		if (!isParked && isHole)
			holes[StackOffset{holeCount++}] = pos;
	}
	yulAssert(parkedCount == holeCount, "parked and holes must have the same size");
	// parked is in ascending order, so the sort of Shuffler.cpp does not change it
	for (StackOffset i{0}; i < parkedCount; ++i.value)
		permutation[parked[i]] = holes[i];
	return permute(permutation);
}

}

/// The Emission constructor and Emission::permuteAtLowestHeight for a stack of m slots and a target of n slots: data
/// holds the slots and dest[i] is the target offset of slot i, or none (SIZE_MAX); the planned mapping is this
/// mapping. Writes the operations to ops and returns their number, also when a slot is out of reach. Then blocked gets
/// its offset and its excess, which is positive, else 0 and 0. Returns -2 for a failed assertion. If the result is not
/// -2, data holds the slots of the working stack, and dest the destination of each of its m slots: a permutation does
/// not change the height.
///
/// dest holds distinct offsets below n, and ops has room for 2m entries: permute makes at most 2m - 1 passes, each
/// with at most one swap. m, n <= 1024, else the result is -2 and nothing is written. spilled has idCount bytes, the
/// spill set of the state; permuteAtLowestHeight does not read it, nor target.
extern "C" std::int64_t permute_at_lowest_height(
	std::uint64_t const m,
	std::uint64_t const n,
	StackSlot* const data,
	StackSlot const* const target,
	Optional<StackOffset>* const dest,
	std::uint8_t const* const spilled,
	[[maybe_unused]] std::uint64_t const idCount,
	ShuffleOp* const ops,
	std::uint64_t* const blocked
)
{
	// the mapping has room for maxStackSize offsets
	if (m > maxStackSize || n > maxStackSize)
		return -2;
	Mapping planned{m, n};
	for (StackOffset pos{0}; pos < m; ++pos.value)
		if (Optional<StackOffset> const destination = dest[pos.value])
			planned.bind(pos, *destination);
	Emission emission{Stack{data, m, ops}, target, n, planned, spilled};
	switch (emission.permuteAtLowestHeight())
	{
	case Status::Done:
		blocked[0] = 0;
		blocked[1] = 0;
		break;
	case Status::Blocked:
		blocked[0] = emission.blocked().offset.value;
		blocked[1] = emission.blocked().excess;
		break;
	case Status::AssertionFailed:
		return -2;
	}
	for (StackOffset pos{0}; pos < m; ++pos.value)
		dest[pos.value] = emission.mapping().destinationOf(pos);
	return static_cast<std::int64_t>(emission.traceSize());
}

namespace
{

/// Shuffler.cpp's MappingBuilder, the Lean model's MappingBuilder and buildMapping
/// (Shuffler/BuildMapping/Defs.lean): builds the mapping of the source stack to the target. Every target offset is
/// either served by a source slot (retained) or left empty (generated); source slots without a target offset are
/// surplus. The constructor of Shuffler.cpp runs five phases; here each phase is a unit, and build_mapping runs them
/// in order.
///
/// The mapping is the caller's, so that the builder does not copy its 16 KiB. dropped has a byte for each source slot:
/// the slot is scheduled to be popped if its byte is not 0. Shuffler.cpp asserts that dropped has the size of the
/// source; here both sizes are m, so the assertion has no counterpart.
class MappingBuilder
{
public:
	/// A copy that sits in a wildcard slot can either be moved to the target offset demanding it or left there,
	/// serving the demand with a duplicate
	enum class WildcardSlotsStrategy : std::uint8_t { Leave, Take };

	/// `_mapping` has no bindings for `_sourceSize` source slots and `_targetSize` target offsets
	MappingBuilder(
		StackSlot const* const _source,
		std::size_t const _sourceSize,
		StackSlot const* const _target,
		std::size_t const _targetSize,
		std::uint8_t const* const _dropped,
		WildcardSlotsStrategy const _wildcardSlotsStrategy,
		Mapping& _mapping
	):
		m_source(_source),
		m_sourceSize(_sourceSize),
		m_target(_target),
		m_targetSize(_targetSize),
		m_dropped(_dropped),
		m_wildcardSlotsStrategy(_wildcardSlotsStrategy),
		m_mapping(_mapping)
	{}

	/// slots already in place get mapped directly
	Status mapInPlace();
	/// the remaining target offsets take the closest unused copy, deepest first: what is left over is generated on
	/// top, where that is cheapest
	Status mapClosestCopies();
	/// copies sitting in wildcard slots are taken or left according to the strategy
	Status mapWildcardSlotCopies();
	/// wildcards keep whatever sits there
	Status keepWildcardSlots();
	/// the remaining wildcards absorb the closest surplus slot instead of having it popped
	Status absorbSurplus();

	/// Whether any target offset's demand was answered by a copy sitting in a wildcard slot, i.e. whether the
	/// `WildcardSlotsStrategy` had anything to decide
	bool sawWildcardCopy() const { return m_sawWildcardCopy; }

private:
	/// Which copies `closestCopy` considers: only those standing in wildcard slots or only those that do not
	enum class CopyLocation : std::uint8_t { OutsideWildcardSlots, InWildcardSlots };

	/// Whether the source slot is not scheduled to be dropped and also not yet pointing to a target
	bool mappable(StackOffset const _sourceOffset) const
	{
		return m_dropped[_sourceOffset.value] == 0 && !m_mapping.destinationOf(_sourceOffset).has_value();
	}

	/// Whether a source slot already serves `_targetOffset`
	bool hasSourceAssigned(StackOffset const _targetOffset) const
	{
		return m_mapping.positionOf(_targetOffset).has_value();
	}

	/// Whether the target at `_targetOffset` is junk, i.e. accepts whatever ends up there
	bool isWildcardTarget(StackOffset const _targetOffset) const { return m_target[_targetOffset.value].isJunk(); }

	/// Whether the source slot at `_sourceOffset` stands at an offset that exists in the target and is junk there,
	/// i.e. a copy that may stay put
	bool inWildcardSlot(StackOffset const _sourceOffset) const
	{
		return _sourceOffset < m_targetSize && isWildcardTarget(_sourceOffset);
	}

	/// The closest mappable copy of the slot demanded at `_targetOffset` among the copies at `_location`; ties go to
	/// the shallower copy
	Optional<StackOffset> closestCopy(StackOffset _targetOffset, CopyLocation _location) const;

	static std::size_t absDiff(StackOffset const _a, StackOffset const _b)
	{
		return _a > _b ? _a.value - _b.value : _b.value - _a.value;
	}

	Status map(StackOffset _sourceOffset, StackOffset _targetOffset);

	std::size_t commonSize() const { return m_sourceSize < m_targetSize ? m_sourceSize : m_targetSize; }

	StackSlot const* m_source;
	std::size_t m_sourceSize;
	StackSlot const* m_target;
	std::size_t m_targetSize;
	std::uint8_t const* m_dropped;
	WildcardSlotsStrategy m_wildcardSlotsStrategy;
	Mapping& m_mapping;
	bool m_sawWildcardCopy = false;
};

// `used` and this place make g++ emit the units of MappingBuilder after remove_surplus, so the asm of the units above
// and their labels stay
[[gnu::used]] UNIT Status MappingBuilder::map(StackOffset const _sourceOffset, StackOffset const _targetOffset)
{
	yulAssert(mappable(_sourceOffset));
	// the assertions of Shuffler.cpp's Mapping::bind
	yulAssert(!m_mapping.destinationOf(_sourceOffset).has_value(), "slot already has a destination");
	yulAssert(!m_mapping.positionOf(_targetOffset).has_value(), "destination already bound to a slot");
	m_mapping.bind(_sourceOffset, _targetOffset);
	return Status::Done;
}

[[gnu::used]] UNIT Optional<StackOffset> MappingBuilder::closestCopy(
	StackOffset const _targetOffset,
	CopyLocation const _location
) const
{
	bool const inWildcardSlots = _location == CopyLocation::InWildcardSlots;
	Optional<StackOffset> best = std::nullopt;
	for (StackOffset i{0}; i < m_sourceSize; ++i.value)
		if (m_source[i.value] == m_target[_targetOffset.value] && mappable(i) && inWildcardSlot(i) == inWildcardSlots)
			if (!best || absDiff(i, _targetOffset) <= absDiff(*best, _targetOffset))
				best = i;
	return best;
}

[[gnu::used]] UNIT Status MappingBuilder::mapInPlace()
{
	for (StackOffset j{0}; j < commonSize(); ++j.value)
		if (m_source[j.value] == m_target[j.value] && mappable(j))
			if (Status const status = map(j, j); status != Status::Done)
				return status;
	return Status::Done;
}

[[gnu::used]] UNIT Status MappingBuilder::mapClosestCopies()
{
	for (StackOffset j{0}; j < m_targetSize; ++j.value)
		if (!hasSourceAssigned(j) && !isWildcardTarget(j))
			if (Optional<StackOffset> const copy = closestCopy(j, CopyLocation::OutsideWildcardSlots))
				if (Status const status = map(*copy, j); status != Status::Done)
					return status;
	return Status::Done;
}

[[gnu::used]] UNIT Status MappingBuilder::mapWildcardSlotCopies()
{
	for (StackOffset j{0}; j < m_targetSize; ++j.value)
		if (!hasSourceAssigned(j) && !isWildcardTarget(j))
			if (Optional<StackOffset> const copy = closestCopy(j, CopyLocation::InWildcardSlots))
			{
				// a function return label is always taken, can't be duped or pushed
				if (m_target[j.value].isFunctionReturnLabel())
				{
					if (Status const status = map(*copy, j); status != Status::Done)
						return status;
				}
				else
				{
					m_sawWildcardCopy = true;
					if (m_wildcardSlotsStrategy == WildcardSlotsStrategy::Take)
						if (Status const status = map(*copy, j); status != Status::Done)
							return status;
				}
			}
	return Status::Done;
}

[[gnu::used]] UNIT Status MappingBuilder::keepWildcardSlots()
{
	for (StackOffset j{0}; j < commonSize(); ++j.value)
		if (isWildcardTarget(j) && !hasSourceAssigned(j) && mappable(j))
			if (Status const status = map(j, j); status != Status::Done)
				return status;
	return Status::Done;
}

[[gnu::used]] UNIT Status MappingBuilder::absorbSurplus()
{
	for (StackOffset j{0}; j < m_targetSize; ++j.value)
		if (isWildcardTarget(j) && !hasSourceAssigned(j))
		{
			// of two slots at the same distance the deeper one: the comparison is strict
			Optional<StackOffset> best = std::nullopt;
			for (StackOffset o{0}; o < m_sourceSize; ++o.value)
				if (mappable(o) && (!best || absDiff(o, j) < absDiff(*best, j)))
					best = o;
			if (best)
				if (Status const status = map(*best, j); status != Status::Done)
					return status;
		}
	return Status::Done;
}

}

/// Shuffler.cpp's MappingBuilder constructor, the Lean model's buildMapping, for a source stack of m slots and a target
/// of n slots: dropped[i] is not 0 if source slot i is scheduled to be popped, and strategy is the
/// WildcardSlotsStrategy, 0 (Leave) or 1 (Take). Writes the position of the source slot bound for each of the n target
/// offsets, or none (SIZE_MAX), to sources, and sawWildcardCopy, 0 or 1, to saw. Returns 0, or -2 for a failed
/// assertion; then nothing is written.
///
/// dropped has m bytes, and sources has room for n entries. m, n <= 1024 and strategy <= 1, else the result is -2 and
/// nothing is written.
extern "C" std::int64_t build_mapping(
	std::uint64_t const m,
	std::uint64_t const n,
	StackSlot const* const source,
	StackSlot const* const target,
	std::uint8_t const* const dropped,
	std::uint8_t const strategy,
	Optional<StackOffset>* const sources,
	std::uint8_t* const saw
)
{
	// the mapping has room for maxStackSize offsets, and the strategy is Leave or Take
	if (m > maxStackSize || n > maxStackSize || strategy > 1)
		return -2;
	Mapping mapping{m, n};
	MappingBuilder builder{source, m, target, n, dropped, MappingBuilder::WildcardSlotsStrategy{strategy}, mapping};
	if (builder.mapInPlace() != Status::Done || builder.mapClosestCopies() != Status::Done ||
		builder.mapWildcardSlotCopies() != Status::Done || builder.keepWildcardSlots() != Status::Done ||
		builder.absorbSurplus() != Status::Done)
		return -2;
	for (StackOffset j{0}; j < n; ++j.value)
		sources[j.value] = mapping.positionOf(j);
	*saw = builder.sawWildcardCopy();
	return 0;
}

namespace
{

/// How Planner::resolve ends: the excess is dropped; no candidate is left to drop (Shuffler.cpp's false); or a failed
/// assertion. Not Status: its Blocked has another meaning.
enum class [[nodiscard]] Resolution : std::uint8_t { Dropped, Stuck, AssertionFailed };

/// How a slot can be regenerated after a drop, cheapest first: not needed or for free, pushed, reloaded from an
/// existing spill, duplicated from another copy, reloaded after a planned spill. Shuffler.cpp's classes 0 to 4; the
/// order of the values is the order of the classes.
enum class Class : std::uint8_t { Free = 0, Push = 1, Reload = 2, Copy = 3, Spill = 4 };

template<>
struct Niche<Class>
{
	static constexpr Class value{0xff};
};

/// The part of Shuffler.cpp's Planner that resolve uses, the Lean model's Planner.State with the source and the
/// target: the spill set, spillingAllowed and the dropped bytes are the caller's. The lambdas of Shuffler.cpp's
/// resolve are units.
class Planner
{
public:
	Planner(
		StackSlot const* const _source,
		std::size_t const _sourceSize,
		StackSlot const* const _target,
		std::size_t const _targetSize,
		SpillSet const _spills,
		bool const _spillingAllowed,
		std::uint8_t* const _dropped
	):
		m_source(_source),
		m_sourceSize(_sourceSize),
		m_target(_target),
		m_targetSize(_targetSize),
		m_spills(_spills),
		m_spillingAllowed(_spillingAllowed),
		m_dropped(_dropped)
	{}

	/// Drops slots above the blocked one until it is within reach, cheapest regeneration first: slots whose
	/// target is a wildcard, freely generatable ones, spilled ones, values with another retained copy, and
	/// finally values that get a planned spill. Function return labels cannot be regenerated and are never
	/// dropped.
	///
	/// `_mapping` is the plan, and `_current` the working mapping of a stack of `_currentSize` slots, with
	/// `_blocked.offset` below `_currentSize`. The drops and spills of the passes before a Stuck or a failed
	/// assertion stay, as in the Lean model. Each pass classifies at most m candidates, and a classification costs
	/// O(m + n), so resolve costs O(excess * m * (m + n)); it stops after at most m + 1 passes.
	Resolution resolve(
		Mapping const& _mapping,
		Emission::Blocked _blocked,
		Mapping const& _current,
		std::size_t _currentSize
	);

private:
	static bool isRetained(Mapping const& _mapping, StackOffset _sourceOffset);
	bool hasOtherRetainedCopy(
		Mapping const& _mapping,
		OffsetArray<std::uint8_t> const& _droppedNow,
		StackOffset _offset
	) const;
	/// this slot is needed somewhere in the target
	bool isDemanded(StackSlot _slot) const;
	/// The class of the slot at `_offset`, which has a destination, or none if it cannot be dropped
	Optional<Class> classify(
		Mapping const& _mapping,
		OffsetArray<std::uint8_t> const& _droppedNow,
		StackOffset _offset
	) const;

	StackSlot const* m_source;
	std::size_t m_sourceSize;
	StackSlot const* m_target;
	std::size_t m_targetSize;
	SpillSet m_spills;
	bool m_spillingAllowed;
	std::uint8_t* m_dropped;
};

// `used` and this place make g++ emit the units of Planner after build_mapping, so the asm of the units above and
// their labels stay
[[gnu::used]] UNIT bool Planner::isRetained(Mapping const& _mapping, StackOffset const _sourceOffset)
{
	return _mapping.destinationOf(_sourceOffset).has_value();
}

[[gnu::used]] UNIT bool Planner::hasOtherRetainedCopy(
	Mapping const& _mapping,
	OffsetArray<std::uint8_t> const& _droppedNow,
	StackOffset const _offset
) const
{
	for (StackOffset sourceOffset{0}; sourceOffset < m_sourceSize; ++sourceOffset.value)
		if (
			sourceOffset != _offset &&
			m_source[sourceOffset.value] == m_source[_offset.value] &&  // same value
			isRetained(_mapping, sourceOffset) &&
			_droppedNow[sourceOffset] == 0  // not yet dropped
		)
			return true;
	return false;
}

[[gnu::used]] UNIT bool Planner::isDemanded(StackSlot const _slot) const
{
	for (std::size_t j = 0; j < m_targetSize; ++j)
		if (!m_target[j].isJunk() && m_target[j] == _slot)
			return true;
	return false;
}

[[gnu::used]] UNIT Optional<Class> Planner::classify(
	Mapping const& _mapping,
	OffsetArray<std::uint8_t> const& _droppedNow,
	StackOffset const _offset
) const
{
	StackSlot const slot = m_source[_offset.value];
	if (slot.isFunctionReturnLabel())
		return std::nullopt;
	bool const regenerable = slot.isJunk() || canBeFreelyGenerated(slot) || isSpilled(slot, m_spills) ||
		hasOtherRetainedCopy(_mapping, _droppedNow, _offset);
	if (m_target[_mapping.destinationOf(_offset)->value].isJunk() && (regenerable || !isDemanded(slot)))
		return Class::Free;
	if (canBeFreelyGenerated(slot))
		return Class::Push;
	if (isSpilled(slot, m_spills))
		return Class::Reload;
	if (hasOtherRetainedCopy(_mapping, _droppedNow, _offset))
		return Class::Copy;
	if (m_spillingAllowed && isVariable(slot))
		return Class::Spill;
	return std::nullopt;
}

[[gnu::used]] UNIT Resolution Planner::resolve(
	Mapping const& _mapping,
	Emission::Blocked const _blocked,
	Mapping const& _current,
	std::size_t const _currentSize
)
{
	OffsetArray<std::uint8_t> droppedNow;
	for (StackOffset sourceOffset{0}; sourceOffset < m_sourceSize; ++sourceOffset.value)
		droppedNow[sourceOffset] = 0;

	// retained slots above the blocked one; the source offset of a retained slot is the one its destination
	// maps back to, while generated and surplus slots have no source. The working mapping binds each destination
	// once, so the candidates are distinct, and there are fewer than _currentSize.
	OffsetArray<StackOffset> candidates;
	std::size_t candidateCount = 0;
	for (StackOffset pos{_blocked.offset.value + 1}; pos < _currentSize; ++pos.value)
		if (Optional<StackOffset> const destination = _current.destinationOf(pos))
			if (Optional<StackOffset> const source = _mapping.positionOf(*destination))
			{
				// the Lean model checks this in classify and in the loop below, where it holds for each candidate
				if (!_mapping.destinationOf(*source))  // Lean
					return Resolution::AssertionFailed;
				candidates[StackOffset{candidateCount++}] = *source;
			}

	for (std::size_t dropped = 0; dropped < _blocked.excess; ++dropped)
	{
		// classes can shift as copies get dropped, so pick one victim at a time
		Optional<StackOffset> best = std::nullopt;
		Class bestClass = Class::Free;
		for (StackOffset i{0}; i < candidateCount; ++i.value)
		{
			StackOffset const offset = candidates[i];
			if (droppedNow[offset] != 0)
				continue;
			Optional<Class> const cls = classify(_mapping, droppedNow, offset);
			if (!cls)
				continue;
			// within a class prefer the slot whose target is highest
			if (
				!best ||
				*cls < bestClass ||
				(*cls == bestClass && *_mapping.destinationOf(offset) > *_mapping.destinationOf(*best))
			)
			{
				best = offset;
				bestClass = *cls;
			}
		}
		if (!best)
			return Resolution::Stuck;  // couldn't drop anything
		if (bestClass == Class::Spill && m_spills.add(m_source[best->value]) != Status::Done)
			return Resolution::AssertionFailed;
		droppedNow[*best] = 1;
		m_dropped[best->value] = 1;
	}
	return Resolution::Dropped;
}

}

/// Shuffler.cpp's Planner::resolve, the Lean model's Planner.resolve, for a source stack of m slots, a target of n
/// slots and a working stack of h slots: plan[i] is the target offset of source slot i in the plan, or none (SIZE_MAX),
/// and current[pos] the target offset of the slot at pos of the working stack in the working mapping, or none. The
/// slot at offset is blocked by excess slots. The variable id is spilled if spilled[id] is not 0, allowed is
/// spillingAllowed, 0 or 1, and dropped[i] is not 0 if source slot i is scheduled to be popped. Sets the dropped byte of
/// each victim to 1, and the spill byte of each new spill to 1. Returns 0 when it dropped excess slots, -1 when no slot
/// is left to drop, or -2 for a failed assertion. Then the drops and spills of the passes before stay.
///
/// plan holds m and current h distinct offsets below n, spilled has idCount bytes, and dropped has m bytes. m, n, h <=
/// 1024, offset < h, allowed <= 1 and the id of each variable of the source is below idCount, else the result is -2 and
/// nothing is written.
extern "C" std::int64_t resolve(
	std::uint64_t const m,
	std::uint64_t const n,
	StackSlot const* const source,
	StackSlot const* const target,
	Optional<StackOffset> const* const plan,
	std::uint64_t const h,
	Optional<StackOffset> const* const current,
	std::uint64_t const offset,
	std::uint64_t const excess,
	std::uint8_t* const spilled,
	std::uint64_t const idCount,
	std::uint8_t const allowed,
	std::uint8_t* const dropped
)
{
	// the mappings have room for maxStackSize offsets, the blocked slot is on the working stack, and only the
	// variables of the source are spilled
	if (m > maxStackSize || n > maxStackSize || h > maxStackSize || offset >= h || allowed > 1)
		return -2;
	for (std::uint64_t i = 0; i < m; ++i)
		if (isVariable(source[i]) && source[i].payload >= idCount)
			return -2;
	Mapping mapping{m, n};
	for (StackOffset pos{0}; pos < m; ++pos.value)
		if (Optional<StackOffset> const destination = plan[pos.value])
			mapping.bind(pos, *destination);
	Mapping working{h, n};
	for (StackOffset pos{0}; pos < h; ++pos.value)
		if (Optional<StackOffset> const destination = current[pos.value])
			working.bind(pos, *destination);
	Planner planner{source, m, target, n, SpillSet{spilled}, allowed == 1, dropped};
	switch (planner.resolve(mapping, Emission::Blocked{StackOffset{offset}, excess}, working, h))
	{
	case Resolution::Dropped:
		return 0;
	case Resolution::Stuck:
		return -1;
	case Resolution::AssertionFailed:
		return -2;
	}
	__builtin_unreachable();
}
