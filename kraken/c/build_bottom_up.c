#include <stddef.h>
#include <stdint.h>
#include <string.h>

/*
 * Emission::buildBottomUp of solidity/libyul/backends/evm/ssa/stack/Shuffler.cpp
 * (at cd1b0a2), and the parts of Emission that it uses. The names and the order of
 * the statements are those of the C++. The differences:
 *
 * - std::optional<Blocked> is Status: OK for none, BLOCKED with the offset and the
 *   excess in m_blocked, or ASSERTION for a failed yulAssert.
 * - std::optional<StackOffset> is a StackOffset, with NONE for none and hasValue for has_value.
 * - No slot is surplus, so a destination is a StackOffset, not a std::optional.
 * - The checks marked `// Lean` come from the Lean original
 *   (Shuffler.BuildBottomUp.Defs), which the C++ does not have.
 * - push and dup do the check of m_mapping.push before the stack operation.
 * - UNIT marks a function that the Kraken proof treats as a separate unit.
 * - StackSlot and struct op have the layout of StackSlot (StackSlot.h) and
 *   ShuffleOp (ShuffleTrace.h), so that a C++ caller can pass a StackData and
 *   a ShuffleTrace buffer as they are.
 */

#define UNIT __attribute__((noinline, noclone))
#define INLINE static inline __attribute__((always_inline))

/// the EVM stack limit
#define MAX_N 1024
#define m_maxSwapDepth 16
#define m_maxDupDepth 15

/// Array index into stack from the bottom (offset 0 = bottom)
typedef struct { size_t value; } StackOffset;
/// Distance from the stack top (depth 0 = top)
typedef struct { size_t value; } StackDepth;
#define NONE ((StackOffset){SIZE_MAX})

/// std::optional<StackOffset>::has_value
INLINE int hasValue(StackOffset const _offset)
{
	return _offset.value != SIZE_MAX;
}

/// StackSlot::Kind
enum { Value = 0, Junk = 1, FunctionCallReturnLabel = 2, FunctionReturnLabel = 3 };

/// InstOpcode (SSACFGTypes.h): the opcodes that the C reads or writes
enum { Const = 0, Unreachable = 5 };

/// StackSlot: m_payload, m_kind, m_valueOpcode and 2 bytes of padding, which nothing reads
typedef struct {
	uint32_t payload;
	uint8_t kind;
	uint8_t valueOpcode;
} StackSlot;
_Static_assert(sizeof(StackSlot) == 8 && _Alignof(StackSlot) == 4, "StackSlot layout");

/// std::optional<Blocked>
typedef int64_t Status;
enum { OK = 0, BLOCKED = -1, ASSERTION = -2 };

#define yulAssert(cond, ...) do { if (!(cond)) return ASSERTION; } while (0)

/// ShuffleOp::Kind
enum { Swap = 0, Dup = 1, Pop = 2, Push = 3, Load = 4, Store = 5 };

/// ShuffleOp: a swap or dup with its depth and a junk slot, or a push or load with depth 0 and its slot
struct op {
	uint8_t kind;
	uint8_t depth;
	StackSlot slot;
};
_Static_assert(sizeof(struct op) == 12 && offsetof(struct op, slot) == 4, "ShuffleOp layout");

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
	// the working stack, which has room for m_targetSize slots
	StackSlot *m_data;
	// the mapping of the working stack
	StackOffset m_destinationOf[MAX_N];
	StackOffset m_positionOf[MAX_N];
};

/// StackSlot::operator== (defaulted): the members are the low 6 bytes, the shift drops the padding
INLINE int slotEquals(StackSlot const _a, StackSlot const _b)
{
	uint64_t a, b;
	memcpy(&a, &_a, sizeof a);
	memcpy(&b, &_b, sizeof b);
	return (a ^ b) << 16 == 0;
}

/// StackSlot::isJunk
INLINE int isJunk(StackSlot const _slot)
{
	return _slot.kind == Junk;
}

/// StackSlot::isLiteralValue
INLINE int isLiteralValue(StackSlot const _slot)
{
	return _slot.valueOpcode == Const;
}

/// canBeFreelyGenerated
INLINE int canBeFreelyGenerated(StackSlot const _slot)
{
	return isLiteralValue(_slot) || _slot.kind == Junk || _slot.kind == FunctionCallReturnLabel;
}

/// spill::isSpilled: a variable that is spilled
UNIT static int isSpilled(struct Emission const *this, StackSlot const _slot)
{
	return _slot.kind == Value && !isLiteralValue(_slot) && this->m_spills[_slot.payload];
}

/// Mapping::positionOf: the position of the slot bound for `_destination`, or NONE if no slot is bound for it
INLINE StackOffset positionOf(struct Emission const *this, StackOffset const _destination)
{
	return this->m_positionOf[_destination.value];
}

/// Mapping::bind: Binds the slot at `_pos` for `_destination`; push and dup do the check
INLINE void bind(struct Emission *this, StackOffset const _pos, StackOffset const _destination)
{
	this->m_destinationOf[_pos.value] = _destination;
	this->m_positionOf[_destination.value] = _pos;
}

/// Mapping::swapDestinations: Exchanges the destinations of the slots at `_a` and `_b`
INLINE void swapDestinations(struct Emission *this, StackOffset const _a, StackOffset const _b)
{
	StackOffset const destination = this->m_destinationOf[_a.value];
	this->m_destinationOf[_a.value] = this->m_destinationOf[_b.value];
	this->m_destinationOf[_b.value] = destination;
	this->m_positionOf[this->m_destinationOf[_a.value].value] = _a;
	this->m_positionOf[this->m_destinationOf[_b.value].value] = _b;
}

/// Whether the slot at `_pos` is bound for `_pos` itself, i.e., already is at its final target offset
INLINE int isFinal(struct Emission const *this, StackOffset const _pos)
{
	return this->m_destinationOf[_pos.value].value == _pos.value;
}

/// Depth of the slot at `_pos` below the top of the working stack
INLINE StackDepth depthOf(struct Emission const *this, StackOffset const _pos)
{
	return (StackDepth){this->m_dataSize - 1 - _pos.value};
}

/// Whether a swap can reach the slot at `_pos`; trivially true for the top itself
INLINE int isSwapReachable(struct Emission const *this, StackOffset const _pos)
{
	return depthOf(this, _pos).value <= m_maxSwapDepth;
}

/// Whether a dup can reach the slot at `_pos`
INLINE int isDupReachable(struct Emission const *this, StackOffset const _pos)
{
	return depthOf(this, _pos).value <= m_maxDupDepth;
}

/// Stack::shallowestCopyPosition
UNIT static StackOffset shallowestCopyPosition(struct Emission const *this, StackSlot const _slot)
{
	for (StackOffset pos = {this->m_dataSize}; pos.value-- > 0;)
		if (slotEquals(this->m_data[pos.value], _slot))
			return pos;
	return NONE;
}

/// appends ShuffleOp::swap or ShuffleOp::dup to the trace
INLINE void record(struct Emission *this, uint8_t const _kind, size_t const _depth)
{
	this->m_trace[this->m_traceSize] = (struct op){_kind, (uint8_t)_depth, {0, Junk, Unreachable}};
	this->m_traceSize++;
}

/// appends the operation of Stack::push to the trace: a pushed non-literal value can only be a spill reload
INLINE void recordPush(struct Emission *this, StackSlot const _slot)
{
	uint8_t const kind = _slot.kind == Value && !isLiteralValue(_slot) ? Load : Push;
	this->m_trace[this->m_traceSize] = (struct op){kind, 0, _slot};
	this->m_traceSize++;
}

/// Swaps the top with the slot at `_pos`, the destinations traveling along
UNIT static Status swapWith(struct Emission *this, StackOffset const _pos)
{
	yulAssert(_pos.value < this->m_dataSize);  // Lean
	yulAssert(!isFinal(this, _pos), "swapping a final slot out of place");
	StackOffset const top = {this->m_dataSize - 1};
	StackDepth const depth = depthOf(this, _pos);
	yulAssert(1 <= depth.value && depth.value <= m_maxSwapDepth, "invalid swap target");  // Stack::swap
	// m_stack.swap(_pos)
	record(this, Swap, depth.value);
	StackSlot const slot = this->m_data[_pos.value];
	this->m_data[_pos.value] = this->m_data[top.value];
	this->m_data[top.value] = slot;
	swapDestinations(this, _pos, top);
	return OK;
}

/// The check of m_mapping.push comes before m_stack.push here, as in the Kraken model (BbuKraken/Model.lean, add)
UNIT static Status push(struct Emission *this, StackSlot const _slot, StackOffset const _destination)
{
	// m_mapping.push(_destination): Binds the freshly pushed top slot for `_destination`, which no slot may be bound for yet
	yulAssert(!hasValue(positionOf(this, _destination)), "destination already bound to a slot");
	bind(this, (StackOffset){this->m_dataSize}, _destination);
	// m_stack.push(_slot)
	recordPush(this, _slot);
	this->m_data[this->m_dataSize] = _slot;
	this->m_dataSize++;
	return OK;
}

/// The check of m_mapping.push comes before m_stack.dup here, as in push
UNIT static Status dup(struct Emission *this, StackOffset const _copy, StackOffset const _destination)
{
	// m_mapping.push(_destination): Binds the freshly pushed top slot for `_destination`, which no slot may be bound for yet
	yulAssert(!hasValue(positionOf(this, _destination)), "destination already bound to a slot");
	bind(this, (StackOffset){this->m_dataSize}, _destination);
	// m_stack.dup(_copy)
	record(this, Dup, depthOf(this, _copy).value + 1);
	this->m_data[this->m_dataSize] = this->m_data[_copy.value];
	this->m_dataSize++;
	return OK;
}

/// The slot at `_position` is out of reach by `_excess` slots
INLINE Status block(struct Emission *this, StackOffset const _position, size_t const _excess)
{
	yulAssert(_excess > 0);
	this->m_blocked[0] = _position.value;
	this->m_blocked[1] = _excess;
	return BLOCKED;
}

/// A swap cannot reach the slot at `_position`
INLINE Status blockSwapUnreachable(struct Emission *this, StackOffset const _position)
{
	return block(this, _position, depthOf(this, _position).value - m_maxSwapDepth);
}

/// A dup cannot reach the slot at `_position`
INLINE Status blockDupUnreachable(struct Emission *this, StackOffset const _position)
{
	return block(this, _position, depthOf(this, _position).value - m_maxDupDepth);
}

/// Produces the slot for `_targetOffset`
UNIT static Status produce(struct Emission *this, StackOffset const _targetOffset)
{
	StackSlot const slot = this->m_target[_targetOffset.value];
	StackOffset const copy = shallowestCopyPosition(this, slot);
	Status status;
	if (isJunk(slot))
		status = push(this, slot, _targetOffset);
	else if (hasValue(copy) && isDupReachable(this, copy))
		status = dup(this, copy, _targetOffset);
	else if (canBeFreelyGenerated(slot) || isSpilled(this, slot))
		status = push(this, slot, _targetOffset);
	else if (hasValue(copy))
		return blockDupUnreachable(this, copy);
	else
		yulAssert(0, "generated slot has no copy on the stack and is not spilled");
	if (status != OK)
		return status;
	yulAssert(positionOf(this, _targetOffset).value == this->m_dataSize - 1);
	if (this->m_pendingGenerations > 0)  // Lean: Nat subtraction
		--this->m_pendingGenerations;
	return OK;
}

/// Produces the slot for `_targetOffset` and moves it toward its place right away: if the offset exists
/// already and holds a slot that is not final, a single swap places the produced slot and floats the other
/// one, which may be its own placement. An equal slot there just takes over the destination.
UNIT static Status generate(struct Emission *this, StackOffset const _targetOffset)
{
	yulAssert(_targetOffset.value < this->m_targetSize);  // Lean
	Status const blocked = produce(this, _targetOffset);
	if (blocked != OK)
		return blocked;
	// `produce` left the slot on top; swap it down only if its offset exists strictly below the top:
	// as the top itself it is in place already, beyond the height it has to wait on top anyway
	if (_targetOffset.value + 1 < this->m_dataSize && !isFinal(this, _targetOffset))
	{
		if (slotEquals(this->m_data[_targetOffset.value], this->m_data[this->m_dataSize - 1]))
			// an equal slot stands at the offset: retag instead of swapping two equal slots
			swapDestinations(this, _targetOffset, (StackOffset){this->m_dataSize - 1});
		else if (isSwapReachable(this, _targetOffset))
			return swapWith(this, _targetOffset);
		// out of swap reach: leave the slot on top; buildBottomUp re-checks reach when filling the offset
	}
	return OK;
}

/// Emission::permute with the destinations: the permutation of permute.c, whose swaps go to the trace
/// and to m_data. The mapping is not used after the permutation, so it does not change.
UNIT static Status permuteDestinations(struct Emission *this)
{
	uint16_t permutation[MAX_N];
	uint8_t swaps[2 * MAX_N];
	uint16_t blocked[2];
	for (size_t i = 0; i < this->m_dataSize; i++)
		permutation[i] = this->m_destinationOf[i].value;
	int64_t const count = permute(this->m_dataSize, permutation, swaps, blocked);
	if (count < 0)
	{
		// the Blocked of the swaps of Emission::permute
		this->m_blocked[0] = blocked[0];
		this->m_blocked[1] = blocked[1];
		return BLOCKED;
	}
	size_t const top = this->m_dataSize - 1;
	for (int64_t i = 0; i < count; i++)
	{
		StackSlot const slot = this->m_data[top - swaps[i]];
		this->m_data[top - swaps[i]] = this->m_data[top];
		this->m_data[top] = slot;
		record(this, Swap, swaps[i]);
	}
	return OK;
}

/// Builds the target bottom-up. Every offset either holds its slot already, gets a retained slot that is
/// floating above it, or gets a freshly generated slot.
/// Once everything is generated the rest is one final permutation.
///
/// Loop invariant: every offset below `targetOffset` is final, i.e., holds the slot bound for it.
UNIT static Status buildBottomUp(struct Emission *this)
{
	for (StackOffset targetOffset = {0}; targetOffset.value < this->m_targetSize; ++targetOffset.value)
	{
		// the offset exists and already holds the slot bound for it: nothing to do
		if (targetOffset.value < this->m_dataSize && isFinal(this, targetOffset))
			continue;

		// all is generated, the final permutation
		if (this->m_pendingGenerations == 0)
		{
			yulAssert(this->m_dataSize == this->m_targetSize);
			// every slot goes to the offset it is bound for
			return permuteDestinations(this);
		}

		// a target offset that needs something DUPed urgently before it goes out of dup reach
		StackOffset urgentToDup = NONE;
		for (StackOffset offset = targetOffset; offset.value < this->m_targetSize; ++offset.value)  // going bottom-up so we can start from targetOffset
		{
			// only offsets no slot is bound for yet (ie that need to be duped) can be urgent
			if (hasValue(positionOf(this, offset)))
				continue;
			StackSlot const slot = this->m_target[offset.value];
			if (isJunk(slot) || canBeFreelyGenerated(slot) || isSpilled(this, slot))
				continue;
			StackOffset const sourceCopy = shallowestCopyPosition(this, slot);
			if (hasValue(sourceCopy))
			{
				if (!isDupReachable(this, sourceCopy))
					return blockDupUnreachable(this, sourceCopy);
				// a copy sitting at the offset being filled floats to the top when it is, so no hurry
				if (depthOf(this, sourceCopy).value == m_maxDupDepth && sourceCopy.value != targetOffset.value && !hasValue(urgentToDup))
					urgentToDup = offset;
			}
		}

		if (
			hasValue(urgentToDup) &&  // if there is a slot that is about to go out of dup range but demands more copies
			urgentToDup.value != targetOffset.value &&  // and it's not the target offset anyways
			this->m_dataSize - targetOffset.value < m_maxSwapDepth  // and duping it doesn't make the target go out of swap range
		)
		{
			// generate it
			Status const blocked = generate(this, urgentToDup);
			if (blocked != OK)
				return blocked;
			// and revisit the current target in the next iteration (with unsigned wrapping this is also fine for 0)
			--targetOffset.value;
			continue;
		}

		// a slot whose offset is exactly where the result of a dup would end up is in place for free,
		// as long as nothing is urgent and targetOffset stays in reach for the slot generated after it
		StackOffset const sourceTop = {this->m_dataSize};
		if (
			!hasValue(urgentToDup) &&  // nothing urgent
			sourceTop.value > targetOffset.value &&  // the new top sits above the current targetOffset
			sourceTop.value < this->m_targetSize &&  // the new top is in the target offset range
			!hasValue(positionOf(this, sourceTop)) &&  // no slot is bound for the offset at the source top yet
			sourceTop.value - targetOffset.value < m_maxSwapDepth  // targetOffset stays in swap reach
		)
		{
			// we generate the slot demanded at source top
			Status const blocked = generate(this, sourceTop);
			if (blocked != OK)
				return blocked;
			// revisit target offset
			--targetOffset.value;
			continue;
		}

		if (
			hasValue(positionOf(this, targetOffset))  // a slot is bound for the target: retained or generated already
		)
		{
			// We go bottom-up, so the slot that should go into targetOffset is somewhere above
			// Any equal slot that is not in place will do the trick: the one at `targetOffset` itself, else the shallowest one
			StackOffset const boundForTarget = positionOf(this, targetOffset);
			yulAssert(
				hasValue(boundForTarget) && boundForTarget.value >= targetOffset.value,
				"slot bound for the offset being filled is missing or already below it"
			);
			StackOffset const sourceForTargetOffset = boundForTarget;
			StackOffset pos = sourceForTargetOffset;
			if (slotEquals(this->m_data[targetOffset.value], this->m_data[sourceForTargetOffset.value]))
				// if the slot currently occupying targetOffset happens to be an equal copy of that value we're done
				// and can set `pos` directly to the target offset
				pos = targetOffset;
			else
				// otherwise search if there is an equal, movable copy shallower than carrier
				for (
					size_t i = 0; i < depthOf(this, sourceForTargetOffset).value; ++i  // stackOffsets() | reverse | take(depthOf(...))
				)
				{
					StackOffset const candidate = {this->m_dataSize - 1 - i};
					if (slotEquals(this->m_data[candidate.value], this->m_data[sourceForTargetOffset.value]) && !isFinal(this, candidate))
					{
						pos = candidate;
						break;
					}
				}

			// we picked a valid `pos`
			yulAssert(slotEquals(this->m_data[pos.value], this->m_data[sourceForTargetOffset.value]));

			// update the destinations if needed
			swapDestinations(this, pos, sourceForTargetOffset);

			// we're already done
			if (pos.value == targetOffset.value)
				continue;

			// if `pos` is not already at the top of the stack, swap it up
			if (pos.value != this->m_dataSize - 1)
			{
				if (!isSwapReachable(this, pos))
					return blockSwapUnreachable(this, pos);  // bail
				Status const status = swapWith(this, pos);
				if (status != OK)
					return status;
			}
		}
		else
		{
			// the slot needs to be DUPed
			Status const blocked = generate(this, targetOffset);
			if (blocked != OK)
				return blocked;

			// `generate` might have already placed the slot into the target offset, then we're done for this offset
			yulAssert(targetOffset.value < this->m_dataSize);  // Lean
			if (isFinal(this, targetOffset))
				continue;
		}

		// we might have to swap the top down into the target offset
		yulAssert(targetOffset.value < this->m_dataSize);  // Lean
		yulAssert(!isFinal(this, targetOffset));
		if (targetOffset.value != this->m_dataSize - 1)
		{
			if (!isSwapReachable(this, targetOffset))
				return blockSwapUnreachable(this, targetOffset);
			Status const status = swapWith(this, targetOffset);
			if (status != OK)
				return status;
		}
	}
	yulAssert(this->m_dataSize == this->m_targetSize);
	return OK;
}

/*
 * The Emission constructor and Emission::run for a source stack without surplus:
 * data holds the m source slots and dest[i] is the target offset of source slot i.
 * Write the operations to ops and return their number, write the blocked offset
 * and excess and return BLOCKED, or return ASSERTION. data is the working stack:
 * on success it holds the n slots of the result, otherwise its content is
 * undefined.
 *
 * m <= n <= MAX_N, data has room for n slots, dest holds distinct offsets below
 * n, every variable id in target is an index of spilled, and ops has room for
 * 6n entries (72n bytes).
 */
int64_t build_bottom_up(uint64_t m, uint64_t n, StackSlot *data,
			const StackSlot *target, const uint64_t *dest,
			const uint8_t *spilled, struct op *ops, uint64_t *blocked)
{
	struct Emission emission;
	emission.m_target = target;
	emission.m_targetSize = n;
	emission.m_spills = spilled;
	emission.m_data = data;
	emission.m_dataSize = m;
	for (size_t i = 0; i < n; i++)
		emission.m_positionOf[i] = NONE;
	for (size_t i = 0; i < m; i++)
		bind(&emission, (StackOffset){i}, (StackOffset){dest[i]});
	emission.m_pendingGenerations = n - m;
	emission.m_traceSize = 0;
	emission.m_trace = ops;
	emission.m_blocked = blocked;
	Status const status = buildBottomUp(&emission);
	return status == OK ? (int64_t)emission.m_traceSize : status;
}
