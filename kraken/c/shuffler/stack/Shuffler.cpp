// Emission::buildBottomUp, Emission::removeSurplus, Emission::permuteAtLowestHeight, Emission::permute,
// Emission::pop, the MappingBuilder, Planner::resolve, Emission::run and Planner::run of
// solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp, freestanding, with the behavior of the Lean model,
// Shuffler/BuildBottomUp/Defs.lean, Shuffler/RemoveSurplus/Defs.lean, Shuffler/PermuteAtLowestHeight/Defs.lean,
// Shuffler/Permute/Defs.lean, State.pop of Shuffler/Emission/Defs.lean, buildMapping of
// Shuffler/BuildMapping/Defs.lean, Shuffler/Resolve/Defs.lean, Shuffler/Emission/Run/Defs.lean and
// Shuffler/Planner/Run/Defs.lean.
// The differences from Shuffler.cpp:
//
// - There are no exceptions, so a failed yulAssert calls exit(1).
// - The checks marked `Lean` come from the Lean model; Shuffler.cpp does not have them.
// - The MappingBuilder constructor of Shuffler.cpp is five functions, one for each phase, and the mapping is the
//   caller's.

#include "../spill/SpillSet.h"
#include "../Stack.h"

namespace
{

/// Shuffler.cpp's isSpilled
constexpr bool isSpilled(StackSlot const _slot, SpillSet const _spills)
{
	return _spills.isSpilled(_slot);
}

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


/// Shuffler.cpp's MappingBuilder, the Lean model's MappingBuilder and buildMapping
/// (Shuffler/BuildMapping/Defs.lean): builds the mapping of the source stack to the target. Every target offset is
/// either served by a source slot (retained) or left empty (generated); source slots without a target offset are
/// surplus. The constructor of Shuffler.cpp runs five phases; here each phase is a unit, and Planner::run runs them
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
	/// `used` makes g++ emit this proof unit even without a caller.
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

	/// Pops all surplus slots, or blocks if a surplus slot that has to be popped is out of swap reach.
	Status removeSurplus();

	/// At the lowest height, permutes every slot to its destination, or, if the destination is above the stack,
	/// into a hole: an offset whose target slot the planned mapping does not bind.
	Status permuteAtLowestHeight();

	/// Shuffler.cpp's run and emit: removes the surplus, permutes at the lowest height, then builds the target
	/// bottom-up. The Result of run stays in the Emission and in the caller's buffers: blocked(), the trace, the
	/// working stack and mapping(). Before buildBottomUp, the checks marked `Lean` are State.Valid of the Lean model,
	/// the precondition of buildBottomUp.
	Status run();

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

	/// State.isAvailable of the Lean model: the slot of the target offset `_offset` can be generated, loaded, or DUPed
	/// from a copy on the stack, which can be out of reach. Shuffler.cpp does not have it.
	bool isAvailable(StackOffset _offset) const;

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

[[gnu::used]] UNIT bool Emission::isAvailable(StackOffset const _offset) const
{
	StackSlot const slot = m_target[_offset.value];
	return canBeFreelyGenerated(slot) || isSpilled(slot) || shallowestCopyPosition(slot).has_value();
}

[[gnu::used]] UNIT Status Emission::run()
{
	// removes all surplus (slots that have no destination in the target)
	if (Status const status = removeSurplus(); status != Status::Done)
		return status;
	if (Status const status = permuteAtLowestHeight(); status != Status::Done)
		return status;
	// State.Valid, in the order of the model
	yulAssert(
		m_stack.size() + m_pendingGenerations == m_targetSize,
		"stack height and pending generations must match the target size"
	);  // Lean
	std::size_t unmapped = 0;
	for (StackOffset offset{0}; offset < m_targetSize; ++offset.value)
		if (!m_mapping.positionOf(offset))
			++unmapped;
	yulAssert(unmapped == m_pendingGenerations, "pending generations must count unmapped target slots");  // Lean
	for (StackOffset offset{0}; offset < m_targetSize; ++offset.value)
		yulAssert(isAvailable(offset), "target slot is unavailable");  // Lean
	for (StackOffset offset{0}; offset < m_targetSize; ++offset.value)
		yulAssert(
			!m_target[offset.value].isFunctionReturnLabel() || m_mapping.positionOf(offset).has_value(),
			"function return label has no bound source"
		);  // Lean
	return buildBottomUp();
}

/// How Planner::resolve ends: the excess is dropped, or no candidate is left to drop (Shuffler.cpp's false).
/// A failed yulAssert ends the process. Status::Blocked has another meaning.
enum class [[nodiscard]] Resolution : std::uint8_t { Dropped, Stuck };

/// How a slot can be regenerated after a drop, cheapest first: not needed or for free, pushed, reloaded from an
/// existing spill, duplicated from another copy, reloaded after a planned spill. Shuffler.cpp's classes 0 to 4; the
/// order of the values is the order of the classes.
enum class Class : std::uint8_t { Free = 0, Push = 1, Reload = 2, Copy = 3, Spill = 4 };

template<>
struct Niche<Class>
{
	static constexpr Class value{0xff};
};


/// Shuffler.cpp's Planner, the Lean model's Planner.State with the source and the target: the spill set,
/// spillingAllowed and the dropped bytes are the caller's. The lambdas of Shuffler.cpp's resolve are units.
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

	/// Builds the mapping and emits from the source, and after each block resolves it and tries again, with the
	/// dropped bytes all 0 at the start. Done is a plan: `_data` holds its stack, `_ops` its `_traceSize` operations,
	/// and `_sources[j]` the source offset bound for target offset j in the mapping of the plan, or none. Blocked is
	/// Shuffler.cpp's false: resolve found nothing left to drop. Each attempt starts with a copy of the source in
	/// `_data`, and writes `_data` and `_ops` as emit does.
	Status run(
		MappingBuilder::WildcardSlotsStrategy _strategy,
		StackSlot* _data,
		ShuffleOp* _ops,
		Optional<StackOffset>* _sources,
		std::size_t& _traceSize
	);

	/// Only after run: whether the mapping of any attempt answered a demand with a copy in a wildcard slot
	bool sawWildcardCopy() const { return m_sawWildcardCopy; }

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
	/// Set by run before the first read.
	bool m_sawWildcardCopy;
};


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
				yulAssert(_mapping.destinationOf(*source).has_value());  // Lean
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
		if (bestClass == Class::Spill)
			yulAssert(m_spills.add(m_source[best->value]) == Status::Done);
		droppedNow[*best] = 1;
		m_dropped[best->value] = 1;
	}
	return Resolution::Dropped;
}

/// ranges::contains on the `_size` slots of `_stack`
constexpr bool contains(StackSlot const* const _stack, std::size_t const _size, StackSlot const _slot)
{
	for (std::size_t i = 0; i < _size; ++i)
		if (_stack[i] == _slot)
			return true;
	return false;
}

[[gnu::used]] UNIT Status Planner::run(
	MappingBuilder::WildcardSlotsStrategy const _strategy,
	StackSlot* const _data,
	ShuffleOp* const _ops,
	Optional<StackOffset>* const _sources,
	std::size_t& _traceSize
)
{
	m_sawWildcardCopy = false;
	for (std::size_t j = 0; j < m_targetSize; ++j)
		yulAssert(
			m_target[j].isJunk() ||
			canBeFreelyGenerated(m_target[j]) ||
			contains(m_source, m_sourceSize, m_target[j]) ||
			isSpilled(m_target[j], m_spills),
			"target slot neither on the stack nor generatable"
		);

	for (;;)
	{
		Mapping mapping{m_sourceSize, m_targetSize};
		MappingBuilder builder{m_source, m_sourceSize, m_target, m_targetSize, m_dropped, _strategy, mapping};
		yulAssert(builder.mapInPlace() == Status::Done && builder.mapClosestCopies() == Status::Done &&
			builder.mapWildcardSlotCopies() == Status::Done && builder.keepWildcardSlots() == Status::Done &&
			builder.absorbSurplus() == Status::Done);
		m_sawWildcardCopy = m_sawWildcardCopy || builder.sawWildcardCopy();
		for (std::size_t i = 0; i < m_sourceSize; ++i)
			_data[i] = m_source[i];
		Emission emission{Stack{_data, m_sourceSize, _ops}, m_target, m_targetSize, mapping, m_spills.m_spilled};
		if (Status const status = emission.run(); status != Status::Blocked)
		{
			if (status == Status::Done)
			{
				for (StackOffset j{0}; j < m_targetSize; ++j.value)
					_sources[j.value] = mapping.positionOf(j);
				_traceSize = emission.traceSize();
			}
			return status;
		}
		std::size_t droppedBefore = 0;
		for (std::size_t i = 0; i < m_sourceSize; ++i)
			droppedBefore += m_dropped[i] != 0;
		switch (resolve(mapping, emission.blocked(), emission.mapping(), emission.stackSize()))
		{
		case Resolution::Dropped:
			break;
		case Resolution::Stuck:
			return Status::Blocked;
		}
		std::size_t droppedAfter = 0;
		for (std::size_t i = 0; i < m_sourceSize; ++i)
			droppedAfter += m_dropped[i] != 0;
		yulAssert(droppedAfter > droppedBefore, "resolution must decrease the number of undropped source slots");  // Lean
	}
}

}
