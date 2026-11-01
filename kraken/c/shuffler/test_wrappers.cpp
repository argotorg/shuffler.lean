// C entry points for the test harnesses and their assembly contracts.
// Include the implementation to test its internal classes in the same translation unit.
#include "stack/Shuffler.cpp"

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

/// Emission::run, Shuffler.cpp's Emission::run and emit, for a source stack of m slots and a target of n slots: data
/// holds the source slots and dest[i] is the target offset of source slot i, or none (SIZE_MAX); the planned mapping is
/// this mapping. Writes the operations to ops and returns their number, also when a slot is out of reach. Then blocked
/// gets its offset and its excess, which is positive, else 0 and 0. Returns -2 for a failed assertion, also of a check
/// of State.Valid before buildBottomUp; then data and ops can hold the operations before it, and blocked, height and
/// dest are not written. If the result is not -2, height gets the height of the working stack, data holds its slots,
/// and the first height entries of dest hold their destinations; the other entries of dest are not written.
///
/// dest holds distinct offsets below n, spilled has idCount bytes, and every variable id of target is below idCount.
/// m, n <= 1024; else, or if a variable id of target is not below idCount, the result is -2 and nothing is written.
/// data and dest have room for max(m, n) entries: removeSurplus lowers the height from m to h, permuteAtLowestHeight
/// keeps h, and buildBottomUp raises it only while pendingGenerations is not 0, and height + pendingGenerations = n.
///
/// ops has room for 4m + 6n entries. The count is at most 2m + 6n - 2h, with h the height after removeSurplus:
/// - removeSurplus: each pass pops a slot, after at most one swap: at most 2(m - h);
/// - permuteAtLowestHeight: permute makes at most 2h - 1 passes, each with at most one swap: at most 2h;
/// - buildBottomUp starts with pendingGenerations = n - h (the first check). Each iteration of its loop lowers
///   2 pendingGenerations + 2(n - targetOffset), first 4n - 2h, by at least the number of operations it adds
///   (Inv.ops_le, kraken/BbuKraken/ModelLemmas.lean), and the final permute of n slots adds at most 2n - 1: at most
///   6n - 2h.
///
/// Stack use in bbu/*.S: at most 65784 bytes below the stack pointer before the call, with the return address
/// (emit, Emission::run, permuteAtLowestHeight, permute, shallowestCopyPosition).
extern "C" std::int64_t emit(
	std::uint64_t const m,
	std::uint64_t const n,
	StackSlot* const data,
	StackSlot const* const target,
	Optional<StackOffset>* const dest,
	std::uint8_t const* const spilled,
	std::uint64_t const idCount,
	ShuffleOp* const ops,
	std::uint64_t* const blocked,
	std::uint64_t* const height
)
{
	// the mapping has room for maxStackSize offsets
	if (m > maxStackSize || n > maxStackSize)
		return -2;
	// buildBottomUp reads the spill byte of each variable of the target
	for (std::uint64_t i = 0; i < n; ++i)
		if (isVariable(target[i]) && target[i].payload >= idCount)
			return -2;
	Mapping planned{m, n};
	for (StackOffset pos{0}; pos < m; ++pos.value)
		if (Optional<StackOffset> const destination = dest[pos.value])
			planned.bind(pos, *destination);
	Emission emission{Stack{data, m, ops}, target, n, planned, spilled};
	switch (emission.run())
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

/// Shuffler.cpp's Planner::run, the Lean model's Planner.run, for a source stack of m slots and a target of n slots:
/// the variable id is spilled if spilled[id] is not 0, allowed is spillingAllowed, 0 or 1, and strategy the
/// WildcardSlotsStrategy, 0 (Leave) or 1 (Take). Sets the dropped byte of each source slot to 0 or 1 (dropped) and the
/// spill byte of each new spill to 1, and writes sawWildcardCopy, 0 or 1, to saw. Returns the number of operations of
/// the plan, or -1 when resolve finds nothing left to drop. After a plan, data holds its n slots, ops its operations,
/// and sources[j] the source offset bound for target offset j in its mapping, or none (SIZE_MAX). Returns -2 for a
/// failed assertion, also of the check of each target slot; then saw and sources are not written, and spilled,
/// dropped, data and ops can be.
///
/// spilled has idCount bytes and dropped m. m, n <= 1024, allowed <= 1, strategy <= 1 and the id of each variable of
/// the source and the target is below idCount, else the result is -2 and nothing is written. data has room for
/// max(m, n) entries, ops for 4m + 6n (see emit; each attempt starts again at ops[0]), and sources for n.
///
/// Stack use in bbu/*.S: at most 66024 bytes below the stack pointer before the call, with the return address
/// (plan, Planner::run, then the chain of emit from Emission::run).
extern "C" std::int64_t plan(
	std::uint64_t const m,
	std::uint64_t const n,
	StackSlot const* const source,
	StackSlot const* const target,
	std::uint8_t* const spilled,
	std::uint64_t const idCount,
	std::uint8_t const allowed,
	std::uint8_t const strategy,
	std::uint8_t* const dropped,
	std::uint8_t* const saw,
	StackSlot* const data,
	ShuffleOp* const ops,
	Optional<StackOffset>* const sources
)
{
	// the mappings have room for maxStackSize offsets; resolve spills only variables of the source, and the target
	// check and emit read the spill byte of each variable of the target
	if (m > maxStackSize || n > maxStackSize || allowed > 1 || strategy > 1)
		return -2;
	for (std::uint64_t i = 0; i < m; ++i)
		if (isVariable(source[i]) && source[i].payload >= idCount)
			return -2;
	for (std::uint64_t j = 0; j < n; ++j)
		if (isVariable(target[j]) && target[j].payload >= idCount)
			return -2;
	for (std::uint64_t i = 0; i < m; ++i)
		dropped[i] = 0;
	Planner planner{source, m, target, n, SpillSet{spilled}, allowed == 1, dropped};
	std::size_t traceSize = 0;
	switch (planner.run(MappingBuilder::WildcardSlotsStrategy{strategy}, data, ops, sources, traceSize))
	{
	case Status::Done:
		*saw = planner.sawWildcardCopy();
		return static_cast<std::int64_t>(traceSize);
	case Status::Blocked:
		*saw = planner.sawWildcardCopy();
		return -1;
	case Status::AssertionFailed:
		return -2;
	}
	__builtin_unreachable();
}
