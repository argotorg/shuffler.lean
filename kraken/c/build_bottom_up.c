#include <stddef.h>
#include <stdint.h>

/*
 * Emission::buildBottomUp of solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp
 * (at cd1b0a2), and the parts of Emission that it uses. The names and the order of
 * the statements are those of the C++. The differences:
 *
 * - std::optional<Blocked> is Status: OK for none, BLOCKED with the offset and the
 *   excess in m_blocked, or ASSERTION for a failed yulAssert.
 * - std::optional<StackOffset> is a StackOffset, with NONE for none.
 * - Mapping keeps only m_destinationOf; positionOf searches it.
 * - The checks marked `// Lean` come from the Lean original
 *   (Shuffler.BuildBottomUp.Defs), which the C++ does not have.
 * - push and dup do the check of m_mapping.push before the stack operation.
 * - UNIT marks a function that the Kraken proof treats as a separate unit.
 */

#define UNIT __attribute__((noinline, noclone))
#define INLINE static inline __attribute__((always_inline))

/// the EVM stack limit
#define MAX_N 1024
#define m_maxSwapDepth 16
#define m_maxDupDepth 15

typedef size_t StackOffset;
#define NONE SIZE_MAX

/// 0 is junk (a wildcard), 1 the function return label,
/// 2 + 2 * i the variable with index i, 3 + 2 * i the literal with index i
typedef uint64_t StackSlot;

/// std::optional<Blocked>
typedef int64_t Status;
enum { OK = 0, BLOCKED = -1, ASSERTION = -2 };

#define yulAssert(cond, ...) do { if (!(cond)) return ASSERTION; } while (0)

/// an operation of the trace: a swap or dup with its depth, or a push with its slot
enum { SWAP, DUP, PUSH };
struct op {
	uint64_t kind, arg;
};

int64_t permute(uint64_t n, uint16_t *perm, uint8_t *trace, uint16_t *blocked);

/// the field order is that of the Kraken proof (BbuKraken/Layout.lean)
struct Emission {
	// the working stack size
	size_t m_dataSize;
	// number of target offsets whose slot still has to be produced; decremented by `produce`
	size_t m_pendingGenerations;
	size_t m_traceSize;
	size_t m_targetSize;
	StackSlot const *m_target;
	// m_spills[id] is not 0 if variable id is spilled
	uint8_t const *m_spills;
	struct op *m_trace;
	// the offset and the excess of a Blocked
	uint64_t *m_blocked;
	// the working stack and its (in sync) mapping
	StackSlot m_data[MAX_N];
	StackOffset m_destinationOf[MAX_N];
};

/// StackSlot::isJunk
INLINE int isJunk(StackSlot const _slot)
{
	return _slot == 0;
}

/// canBeFreelyGenerated: junk or a literal
INLINE int canBeFreelyGenerated(StackSlot const _slot)
{
	return _slot == 0 || (_slot & 1 && _slot != 1);
}

/// spill::isSpilled: a variable that is spilled
UNIT static int isSpilled(struct Emission const *e, StackSlot const _slot)
{
	return _slot >= 2 && !(_slot & 1) && e->m_spills[(_slot - 2) / 2];
}

/// Mapping::positionOf: the position of the slot bound for `_destination`, or NONE if no slot is bound for it
UNIT static StackOffset positionOf(struct Emission const *e, StackOffset const _destination)
{
	for (StackOffset pos = 0; pos < e->m_dataSize; pos++)
		if (e->m_destinationOf[pos] == _destination)
			return pos;
	return NONE;
}

/// Mapping::swapDestinations: Exchanges the destinations of the slots at `_a` and `_b`
INLINE void swapDestinations(struct Emission *e, StackOffset const _a, StackOffset const _b)
{
	StackOffset const destination = e->m_destinationOf[_a];
	e->m_destinationOf[_a] = e->m_destinationOf[_b];
	e->m_destinationOf[_b] = destination;
}

/// Whether the slot at `_pos` is bound for `_pos` itself, i.e., already is at its final target offset
INLINE int isFinal(struct Emission const *e, StackOffset const _pos)
{
	return e->m_destinationOf[_pos] == _pos;
}

/// Depth of the slot at `_pos` below the top of the working stack
INLINE size_t depthOf(struct Emission const *e, StackOffset const _pos)
{
	return e->m_dataSize - 1 - _pos;
}

/// Whether a swap can reach the slot at `_pos`; trivially true for the top itself
INLINE int isSwapReachable(struct Emission const *e, StackOffset const _pos)
{
	return depthOf(e, _pos) <= m_maxSwapDepth;
}

/// Whether a dup can reach the slot at `_pos`
INLINE int isDupReachable(struct Emission const *e, StackOffset const _pos)
{
	return depthOf(e, _pos) <= m_maxDupDepth;
}

/// Stack::shallowestCopyPosition
UNIT static StackOffset shallowestCopyPosition(struct Emission const *e, StackSlot const _slot)
{
	for (StackOffset pos = e->m_dataSize; pos-- > 0;)
		if (e->m_data[pos] == _slot)
			return pos;
	return NONE;
}

/// appends an operation to the trace
INLINE void record(struct Emission *e, uint64_t const _kind, uint64_t const _arg)
{
	e->m_trace[e->m_traceSize].kind = _kind;
	e->m_trace[e->m_traceSize].arg = _arg;
	e->m_traceSize++;
}

/// Swaps the top with the slot at `_pos`, the destinations traveling along
UNIT static Status swapWith(struct Emission *e, StackOffset const _pos)
{
	yulAssert(_pos < e->m_dataSize);  // Lean
	yulAssert(!isFinal(e, _pos), "swapping a final slot out of place");
	StackOffset const top = e->m_dataSize - 1;
	size_t const depth = depthOf(e, _pos);
	yulAssert(1 <= depth && depth <= m_maxSwapDepth, "invalid swap target");  // Stack::swap
	// m_stack.swap(_pos)
	record(e, SWAP, depth);
	StackSlot const slot = e->m_data[_pos];
	e->m_data[_pos] = e->m_data[top];
	e->m_data[top] = slot;
	swapDestinations(e, _pos, top);
	return OK;
}

/// The check of m_mapping.push comes before m_stack.push here, as in the Kraken model (BbuKraken/Model.lean, add)
UNIT static Status push(struct Emission *e, StackSlot const _slot, StackOffset const _destination)
{
	// m_mapping.push(_destination): Binds the freshly pushed top slot for `_destination`, which no slot may be bound for yet
	yulAssert(positionOf(e, _destination) == NONE, "destination already bound to a slot");
	e->m_destinationOf[e->m_dataSize] = _destination;
	// m_stack.push(_slot)
	record(e, PUSH, _slot);
	e->m_data[e->m_dataSize] = _slot;
	e->m_dataSize++;
	return OK;
}

/// The check of m_mapping.push comes before m_stack.dup here, as in push
UNIT static Status dup(struct Emission *e, StackOffset const _copy, StackOffset const _destination)
{
	// m_mapping.push(_destination): Binds the freshly pushed top slot for `_destination`, which no slot may be bound for yet
	yulAssert(positionOf(e, _destination) == NONE, "destination already bound to a slot");
	e->m_destinationOf[e->m_dataSize] = _destination;
	// m_stack.dup(_copy)
	record(e, DUP, depthOf(e, _copy) + 1);
	e->m_data[e->m_dataSize] = e->m_data[_copy];
	e->m_dataSize++;
	return OK;
}

/// The slot at `_position` is out of reach by `_excess` slots
INLINE Status block(struct Emission *e, StackOffset const _position, size_t const _excess)
{
	yulAssert(_excess > 0);
	e->m_blocked[0] = _position;
	e->m_blocked[1] = _excess;
	return BLOCKED;
}

/// A swap cannot reach the slot at `_position`
INLINE Status blockSwapUnreachable(struct Emission *e, StackOffset const _position)
{
	return block(e, _position, depthOf(e, _position) - m_maxSwapDepth);
}

/// A dup cannot reach the slot at `_position`
INLINE Status blockDupUnreachable(struct Emission *e, StackOffset const _position)
{
	return block(e, _position, depthOf(e, _position) - m_maxDupDepth);
}

/// Produces the slot for `_targetOffset`
UNIT static Status produce(struct Emission *e, StackOffset const _targetOffset)
{
	StackSlot const slot = e->m_target[_targetOffset];
	StackOffset const copy = shallowestCopyPosition(e, slot);
	Status status;
	if (isJunk(slot))
		status = push(e, slot, _targetOffset);
	else if (copy != NONE && isDupReachable(e, copy))
		status = dup(e, copy, _targetOffset);
	else if (canBeFreelyGenerated(slot) || isSpilled(e, slot))
		status = push(e, slot, _targetOffset);
	else if (copy != NONE)
		return blockDupUnreachable(e, copy);
	else
		yulAssert(0, "generated slot has no copy on the stack and is not spilled");
	if (status != OK)
		return status;
	yulAssert(positionOf(e, _targetOffset) == e->m_dataSize - 1);
	if (e->m_pendingGenerations > 0)  // Lean: Nat subtraction
		--e->m_pendingGenerations;
	return OK;
}

/// Produces the slot for `_targetOffset` and moves it toward its place right away: if the offset exists
/// already and holds a slot that is not final, a single swap places the produced slot and floats the other
/// one, which may be its own placement. An equal slot there just takes over the destination.
UNIT static Status generate(struct Emission *e, StackOffset const _targetOffset)
{
	yulAssert(_targetOffset < e->m_targetSize);  // Lean
	Status const blocked = produce(e, _targetOffset);
	if (blocked != OK)
		return blocked;
	// `produce` left the slot on top; swap it down only if its offset exists strictly below the top:
	// as the top itself it is in place already, beyond the height it has to wait on top anyway
	if (_targetOffset + 1 < e->m_dataSize && !isFinal(e, _targetOffset))
	{
		if (e->m_data[_targetOffset] == e->m_data[e->m_dataSize - 1])
			// an equal slot stands at the offset: retag instead of swapping two equal slots
			swapDestinations(e, _targetOffset, e->m_dataSize - 1);
		else if (isSwapReachable(e, _targetOffset))
			return swapWith(e, _targetOffset);
		// out of swap reach: leave the slot on top; buildBottomUp re-checks reach when filling the offset
	}
	return OK;
}

/// Emission::permute with the destinations: the permutation of permute.c, whose swaps go to the trace
UNIT static Status permuteDestinations(struct Emission *e)
{
	uint16_t permutation[MAX_N];
	uint8_t swaps[2 * MAX_N];
	uint16_t blocked[2];
	for (StackOffset i = 0; i < e->m_dataSize; i++)
		permutation[i] = e->m_destinationOf[i];
	int64_t const count = permute(e->m_dataSize, permutation, swaps, blocked);
	if (count < 0)
	{
		// the Blocked of the swaps of Emission::permute
		e->m_blocked[0] = blocked[0];
		e->m_blocked[1] = blocked[1];
		return BLOCKED;
	}
	for (int64_t i = 0; i < count; i++)
		record(e, SWAP, swaps[i]);
	return OK;
}

/// Builds the target bottom-up. Every offset either holds its slot already, gets a retained slot that is
/// floating above it, or gets a freshly generated slot.
/// Once everything is generated the rest is one final permutation.
///
/// Loop invariant: every offset below `targetOffset` is final, i.e., holds the slot bound for it.
UNIT static Status buildBottomUp(struct Emission *e)
{
	for (StackOffset targetOffset = 0; targetOffset < e->m_targetSize; ++targetOffset)
	{
		// the offset exists and already holds the slot bound for it: nothing to do
		if (targetOffset < e->m_dataSize && isFinal(e, targetOffset))
			continue;

		// all is generated, the final permutation
		if (e->m_pendingGenerations == 0)
		{
			yulAssert(e->m_dataSize == e->m_targetSize);
			// every slot goes to the offset it is bound for
			return permuteDestinations(e);
		}

		// a target offset that needs something DUPed urgently before it goes out of dup reach
		StackOffset urgentToDup = NONE;
		for (StackOffset offset = targetOffset; offset < e->m_targetSize; ++offset)  // going bottom-up so we can start from targetOffset
		{
			// only offsets no slot is bound for yet (ie that need to be duped) can be urgent
			if (positionOf(e, offset) != NONE)
				continue;
			StackSlot const slot = e->m_target[offset];
			if (isJunk(slot) || canBeFreelyGenerated(slot) || isSpilled(e, slot))
				continue;
			StackOffset const sourceCopy = shallowestCopyPosition(e, slot);
			if (sourceCopy != NONE)
			{
				if (!isDupReachable(e, sourceCopy))
					return blockDupUnreachable(e, sourceCopy);
				// a copy sitting at the offset being filled floats to the top when it is, so no hurry
				if (depthOf(e, sourceCopy) == m_maxDupDepth && sourceCopy != targetOffset && urgentToDup == NONE)
					urgentToDup = offset;
			}
		}

		if (
			urgentToDup != NONE &&  // if there is a slot that is about to go out of dup range but demands more copies
			urgentToDup != targetOffset &&  // and it's not the target offset anyways
			e->m_dataSize - targetOffset < m_maxSwapDepth  // and duping it doesn't make the target go out of swap range
		)
		{
			// generate it
			Status const blocked = generate(e, urgentToDup);
			if (blocked != OK)
				return blocked;
			// and revisit the current target in the next iteration (with unsigned wrapping this is also fine for 0)
			--targetOffset;
			continue;
		}

		// a slot whose offset is exactly where the result of a dup would end up is in place for free,
		// as long as nothing is urgent and targetOffset stays in reach for the slot generated after it
		StackOffset const sourceTop = e->m_dataSize;
		if (
			urgentToDup == NONE &&  // nothing urgent
			sourceTop > targetOffset &&  // the new top sits above the current targetOffset
			sourceTop < e->m_targetSize &&  // the new top is in the target offset range
			positionOf(e, sourceTop) == NONE &&  // no slot is bound for the offset at the source top yet
			sourceTop - targetOffset < m_maxSwapDepth  // targetOffset stays in swap reach
		)
		{
			// we generate the slot demanded at source top
			Status const blocked = generate(e, sourceTop);
			if (blocked != OK)
				return blocked;
			// revisit target offset
			--targetOffset;
			continue;
		}

		if (
			positionOf(e, targetOffset) != NONE  // a slot is bound for the target: retained or generated already
		)
		{
			// We go bottom-up, so the slot that should go into targetOffset is somewhere above
			// Any equal slot that is not in place will do the trick: the one at `targetOffset` itself, else the shallowest one
			StackOffset const boundForTarget = positionOf(e, targetOffset);
			yulAssert(
				boundForTarget != NONE && boundForTarget >= targetOffset,
				"slot bound for the offset being filled is missing or already below it"
			);
			StackOffset const sourceForTargetOffset = boundForTarget;
			StackOffset pos = sourceForTargetOffset;
			if (e->m_data[targetOffset] == e->m_data[sourceForTargetOffset])
				// if the slot currently occupying targetOffset happens to be an equal copy of that value we're done
				// and can set `pos` directly to the target offset
				pos = targetOffset;
			else
				// otherwise search if there is an equal, movable copy shallower than carrier
				for (
					size_t i = 0; i < depthOf(e, sourceForTargetOffset); ++i  // stackOffsets() | reverse | take(depthOf(...))
				)
				{
					StackOffset const candidate = e->m_dataSize - 1 - i;
					if (e->m_data[candidate] == e->m_data[sourceForTargetOffset] && !isFinal(e, candidate))
					{
						pos = candidate;
						break;
					}
				}

			// we picked a valid `pos`
			yulAssert(e->m_data[pos] == e->m_data[sourceForTargetOffset]);

			// update the destinations if needed
			swapDestinations(e, pos, sourceForTargetOffset);

			// we're already done
			if (pos == targetOffset)
				continue;

			// if `pos` is not already at the top of the stack, swap it up
			if (pos != e->m_dataSize - 1)
			{
				if (!isSwapReachable(e, pos))
					return blockSwapUnreachable(e, pos);  // bail
				Status const status = swapWith(e, pos);
				if (status != OK)
					return status;
			}
		}
		else
		{
			// the slot needs to be DUPed
			Status const blocked = generate(e, targetOffset);
			if (blocked != OK)
				return blocked;

			// `generate` might have already placed the slot into the target offset, then we're done for this offset
			yulAssert(targetOffset < e->m_dataSize);  // Lean
			if (isFinal(e, targetOffset))
				continue;
		}

		// we might have to swap the top down into the target offset
		yulAssert(targetOffset < e->m_dataSize);  // Lean
		yulAssert(!isFinal(e, targetOffset));
		if (targetOffset != e->m_dataSize - 1)
		{
			if (!isSwapReachable(e, targetOffset))
				return blockSwapUnreachable(e, targetOffset);
			Status const status = swapWith(e, targetOffset);
			if (status != OK)
				return status;
		}
	}
	yulAssert(e->m_dataSize == e->m_targetSize);
	return OK;
}

/*
 * The Emission constructor and Emission::run for a source stack without surplus:
 * dest[i] is the target offset of source slot i. Write the operations to ops and
 * return their number, write the blocked offset and excess and return BLOCKED, or
 * return ASSERTION.
 *
 * m <= n <= MAX_N, dest holds distinct offsets below n, every variable id in
 * target is an index of spilled, and ops has room for 6n entries.
 */
int64_t build_bottom_up(uint64_t m, uint64_t n, const uint64_t *source,
			const uint64_t *target, const uint64_t *dest,
			const uint8_t *spilled, struct op *ops, uint64_t *blocked)
{
	struct Emission e;
	e.m_target = target;
	e.m_targetSize = n;
	e.m_spills = spilled;
	e.m_dataSize = m;
	for (StackOffset i = 0; i < m; i++) {
		e.m_data[i] = source[i];
		e.m_destinationOf[i] = dest[i];
	}
	e.m_pendingGenerations = n - m;
	e.m_traceSize = 0;
	e.m_trace = ops;
	e.m_blocked = blocked;
	Status const status = buildBottomUp(&e);
	return status == OK ? (int64_t)e.m_traceSize : status;
}
