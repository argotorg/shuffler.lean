// The unit tests of build_bottom_up.cpp: the stack and mapping operations, the Emission constructor and pop, and
// the entries. The file includes build_bottom_up.cpp, so the tests run the production code, compiled hosted.
// `make unit_test` builds it; Shuffler/Mapping.lean is the model of the mapping checks.
#include "build_bottom_up.cpp"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <optional>
#include <random>
#include <set>
#include <vector>

namespace
{

int failures = 0;

void expect(bool const _ok, char const* const _what, unsigned long const _context = 0)
{
	if (!_ok)
	{
		std::fprintf(stderr, "FAIL: %s (%lu)\n", _what, _context);
		++failures;
	}
}

using Opt = std::optional<std::size_t>;

Opt opt(Optional<StackOffset> const _offset)
{
	return _offset ? Opt{_offset->value} : std::nullopt;
}

/// The variable `_id`: a Value that is not a literal
StackSlot variable(std::uint32_t const _id)
{
	return {_id, StackSlot::Kind::Value, InstOpcode{1}};
}

bool sameSlot(StackSlot const _a, StackSlot const _b)
{
	return _a.payload == _b.payload && _a.kind == _b.kind && _a.valueOpcode == _b.valueOpcode;
}

bool isPop(ShuffleOp const _op)
{
	return _op.kind == ShuffleOp::Kind::Pop && _op.depth == 0 && sameSlot(_op.slot, StackSlot::makeJunk());
}

/// The mapping of Shuffler/Mapping.lean: the destination of each slot of the stack, and the position of the slot
/// bound for each target offset. pop is Mapping.pop: it keeps a position only if it is below the new height.
struct Model
{
	std::vector<Opt> destinationOf;
	std::vector<Opt> positionOf;

	void bind(std::size_t const _pos, std::size_t const _destination)
	{
		destinationOf[_pos] = _destination;
		positionOf[_destination] = _pos;
	}
	void swapDestinations(std::size_t const _a, std::size_t const _b)
	{
		std::swap(destinationOf[_a], destinationOf[_b]);
		for (std::size_t const pos: {_a, _b})
			if (destinationOf[pos])
				positionOf[*destinationOf[pos]] = pos;
	}
	void push(std::size_t const _destination)
	{
		destinationOf.emplace_back();
		bind(destinationOf.size() - 1, _destination);
	}
	void pop()
	{
		destinationOf.pop_back();
		for (Opt& pos: positionOf)
			if (pos && *pos >= destinationOf.size())
				pos.reset();
	}
};

/// `_mapping` on a stack of `_model.destinationOf.size()` slots equals `_model`, and its two sides are inverse
void agrees(Mapping const& _mapping, Model const& _model, unsigned long const _context)
{
	std::size_t const height = _model.destinationOf.size();
	std::size_t const n = _model.positionOf.size();
	for (StackOffset pos{0}; pos < height; ++pos.value)
	{
		Opt const destination = opt(_mapping.destinationOf(pos));
		expect(destination == _model.destinationOf[pos.value], "destinationOf equals the model", _context);
		expect(!destination || (*destination < n && opt(_mapping.positionOf(StackOffset{*destination})) == pos.value),
			"positionOf of destinationOf is the slot", _context);
	}
	for (StackOffset destination{0}; destination < n; ++destination.value)
	{
		Opt const pos = opt(_mapping.positionOf(destination));
		expect(pos == _model.positionOf[destination.value], "positionOf equals the model", _context);
		expect(!pos || (*pos < height && opt(_mapping.destinationOf(StackOffset{*pos})) == destination.value),
			"destinationOf of positionOf is the offset", _context);
	}
}

void stackPop()
{
	StackSlot data[3] = {variable(0), variable(1), variable(2)};
	ShuffleOp trace[3];

	Stack empty{data, 0, trace};
	expect(empty.pop() == Status::AssertionFailed, "pop of an empty stack fails");
	expect(empty.size() == 0 && empty.traceSize() == 0, "a failed pop changes nothing");

	Stack stack{data, 2, trace};
	expect(stack.pop() == Status::Done, "pop of a slot");
	expect(stack.size() == 1 && stack.traceSize() == 1 && isPop(trace[0]), "pop records Pop");
	expect(sameSlot(data[0], variable(0)) && sameSlot(data[1], variable(1)), "pop writes no slot");
	expect(stack.pop() == Status::Done && stack.size() == 0 && stack.traceSize() == 2 && isPop(trace[1]),
		"pop of the last slot");
	expect(stack.pop() == Status::AssertionFailed && stack.size() == 0 && stack.traceSize() == 2,
		"pop after the last slot fails");
}

void mappingConstructor()
{
	for (std::size_t const m: {0, 1, 7, 1024})
		for (std::size_t const n: {0, 1, 7, 1024})
		{
			Mapping mapping{m, n};
			agrees(mapping, Model{std::vector<Opt>(m), std::vector<Opt>(n)}, m * 10000 + n);
		}
}

void mappingPop()
{
	// slot 0 is bound for 2, slot 1 has no destination, slot 2 is bound for 0
	Mapping mapping{3, 4};
	mapping.bind(StackOffset{0}, StackOffset{2});
	mapping.bind(StackOffset{2}, StackOffset{0});
	Model model{std::vector<Opt>(3), std::vector<Opt>(4)};
	model.bind(0, 2);
	model.bind(2, 0);

	// a bound top: its destination has no slot then
	mapping.pop(StackOffset{2});
	model.pop();
	expect(!mapping.positionOf(StackOffset{0}), "pop of a bound top clears positionOf");
	agrees(mapping, model, 2);

	// a top without a destination: nothing changes
	mapping.pop(StackOffset{1});
	model.pop();
	agrees(mapping, model, 1);

	mapping.pop(StackOffset{0});
	model.pop();
	agrees(mapping, model, 0);
	expect(!mapping.positionOf(StackOffset{2}), "pop of the last slot clears positionOf");

	// the highest offsets
	Mapping full{1024, 1024};
	full.bind(StackOffset{1023}, StackOffset{1023});
	full.bind(StackOffset{1022}, StackOffset{0});
	full.pop(StackOffset{1023});
	Model fullModel{std::vector<Opt>(1024), std::vector<Opt>(1024)};
	fullModel.bind(1022, 0);
	fullModel.destinationOf.pop_back();
	agrees(full, fullModel, 1023);
}

/// Random sequences of bind, swapDestinations, push (a bind of the new top, as Emission::push and dup do) and pop.
/// Each operation has the precondition of its Lean model. After each one the mapping equals the model, and
/// positionOf and destinationOf are inverse on [0, height).
void mappingOperations()
{
	std::mt19937_64 random{20261030};
	auto const below = [&](std::size_t const _bound) {
		return std::uniform_int_distribution<std::size_t>{0, _bound - 1}(random);
	};
	for (unsigned long run = 0; run < 3000; ++run)
	{
		// most runs are small, so that the operations meet; some reach the largest stack
		std::size_t const limit = run % 100 == 0 ? 1024 : 1 + run % 9;
		std::size_t const n = below(limit + 1);
		std::size_t const m = below(limit + 1);
		Mapping mapping{m, n};
		Model model{std::vector<Opt>(m), std::vector<Opt>(n)};
		for (std::size_t step = 0; step < 300; ++step)
		{
			std::size_t const height = model.destinationOf.size();
			std::vector<std::size_t> freeDestinations;
			for (std::size_t d = 0; d < n; ++d)
				if (!model.positionOf[d])
					freeDestinations.push_back(d);
			std::vector<std::size_t> unboundSlots;
			for (std::size_t pos = 0; pos < height; ++pos)
				if (!model.destinationOf[pos])
					unboundSlots.push_back(pos);
			switch (below(4))
			{
			case 0:
				if (unboundSlots.empty() || freeDestinations.empty())
					continue;
				{
					std::size_t const pos = unboundSlots[below(unboundSlots.size())];
					std::size_t const destination = freeDestinations[below(freeDestinations.size())];
					mapping.bind(StackOffset{pos}, StackOffset{destination});
					model.bind(pos, destination);
				}
				break;
			case 1:
				if (height == 0)
					continue;
				{
					std::size_t const a = below(height);
					std::size_t const b = below(height);
					mapping.swapDestinations(StackOffset{a}, StackOffset{b});
					model.swapDestinations(a, b);
				}
				break;
			case 2:
				if (height == maxStackSize || freeDestinations.empty())
					continue;
				{
					std::size_t const destination = freeDestinations[below(freeDestinations.size())];
					mapping.bind(StackOffset{height}, StackOffset{destination});
					model.push(destination);
				}
				break;
			default:
				if (height == 0)
					continue;
				mapping.pop(StackOffset{height - 1});
				model.pop();
				break;
			}
			agrees(mapping, model, run);
		}
	}
}

void emission()
{
	StackSlot data[4] = {variable(0), variable(1), variable(2), variable(3)};
	ShuffleOp ops[4];
	StackSlot const target[4] = {variable(0), variable(1), variable(2), variable(3)};
	std::uint8_t const spills[4] = {};
	// slot 0 is bound for 1, slot 1 has no destination, slot 2 is bound for 3: offsets 0 and 2 are generated
	Mapping planned{3, 4};
	planned.bind(StackOffset{0}, StackOffset{1});
	planned.bind(StackOffset{2}, StackOffset{3});
	Emission emission{Stack{data, 3, ops}, target, 4, planned, spills};
	Model model{std::vector<Opt>(3), std::vector<Opt>(4)};
	model.bind(0, 1);
	model.bind(2, 3);
	agrees(emission.mapping(), model, 0);
	expect(emission.pendingGenerations() == 2, "pending: the offsets without a slot");

	expect(emission.pop() == Status::Done, "pop of a bound top");
	model.pop();
	agrees(emission.mapping(), model, 1);
	expect(emission.traceSize() == 1 && isPop(ops[0]), "pop records Pop");
	expect(emission.pendingGenerations() == 2, "pop does not change pending");
	// the working mapping is a copy
	expect(opt(planned.positionOf(StackOffset{3})) == 2 && opt(planned.destinationOf(StackOffset{2})) == 3,
		"pop does not change the planned mapping");

	expect(emission.pop() == Status::Done, "pop of a top without a destination");
	model.pop();
	agrees(emission.mapping(), model, 2);
	expect(emission.pop() == Status::Done, "pop of the last slot");
	model.pop();
	agrees(emission.mapping(), model, 3);
	expect(emission.pop() == Status::AssertionFailed, "pop of an empty stack fails");
	agrees(emission.mapping(), model, 4);
	expect(emission.traceSize() == 3 && emission.pendingGenerations() == 2, "a failed pop changes nothing");

	// pending at the bounds: no slot, and every offset bound
	Mapping none{0, 1024};
	expect(Emission{Stack{data, 0, ops}, target, 1024, none, spills}.pendingGenerations() == 1024, "pending: all");
	Mapping all{3, 3};
	for (std::size_t pos = 0; pos < 3; ++pos)
		all.bind(StackOffset{pos}, StackOffset{2 - pos});
	expect(Emission{Stack{data, 3, ops}, target, 3, all, spills}.pendingGenerations() == 0, "pending: none");
}

/// The slots that are not a variable, with the payload `_payload`: a literal, junk, a function call return label and
/// a function return label
std::vector<StackSlot> nonVariables(std::uint32_t const _payload)
{
	return {
		{_payload, StackSlot::Kind::Value, InstOpcode::Const},
		{_payload, StackSlot::Kind::Junk, InstOpcode::Unreachable},
		{_payload, StackSlot::Kind::FunctionCallReturnLabel, InstOpcode::Unreachable},
		{_payload, StackSlot::Kind::FunctionReturnLabel, InstOpcode::Unreachable},
	};
}

/// SpillSet::add, SpillSet::isSpilled and the free isSpilled: the cases of Shuffler.SpillSet.add and
/// SpillSet.is_spilled
void spillSet()
{
	std::uint8_t spilled[4] = {};
	SpillSet spills{spilled};
	auto const bytes = [&](std::vector<std::uint8_t> const& _expected) {
		return std::equal(_expected.begin(), _expected.end(), spilled, spilled + 4);
	};

	expect(!spills.isSpilled(variable(2)), "a variable is not spilled before its add");
	expect(spills.add(variable(2)) == Status::Done, "add of a new variable");
	expect(bytes({0, 0, 1, 0}), "add sets the byte of the variable");
	expect(spills.isSpilled(variable(2)) && isSpilled(variable(2), spills), "isSpilled after add");
	expect(spills.add(variable(2)) == Status::AssertionFailed, "add of a spilled variable fails");
	expect(bytes({0, 0, 1, 0}), "a failed add changes nothing");

	// a slot that is not a variable, with the payload of a variable that is not spilled (1) and of one that is (2)
	for (std::uint32_t const payload: {1u, 2u})
		for (StackSlot const slot: nonVariables(payload))
		{
			expect(spills.add(slot) == Status::AssertionFailed, "add of a slot that is not a variable fails", payload);
			expect(bytes({0, 0, 1, 0}), "a failed add of a slot that is not a variable changes nothing", payload);
			expect(!spills.isSpilled(slot) && !isSpilled(slot, spills), "a slot that is not a variable is not spilled",
				payload);
		}

	// each opcode but Const makes a variable
	StackSlot const unreachable{3, StackSlot::Kind::Value, InstOpcode::Unreachable};
	expect(spills.add(unreachable) == Status::Done && bytes({0, 0, 1, 1}), "add of a variable with opcode Unreachable");
	expect(spills.isSpilled(unreachable) && spills.isSpilled(variable(3)),
		"isSpilled does not read the opcode of a variable");

	// each byte that is not 0 is a spill
	spilled[0] = 0xff;
	expect(spills.isSpilled(variable(0)), "a byte 0xff is a spill");
	expect(spills.add(variable(0)) == Status::AssertionFailed && bytes({0xff, 0, 1, 1}), "add on a byte 0xff fails");
	expect(spills.add(variable(1)) == Status::Done && bytes({0xff, 1, 1, 1}), "add of the last free variable");
}

/// Random sequences of SpillSet::add on random slots, against the std::set of SpillSet.h: an add of a variable that
/// is not in the set inserts it and changes only its byte; each other add fails and changes nothing. After each add,
/// isSpilled of each slot is the set membership of a variable.
void spillSetOperations()
{
	std::mt19937_64 random{20261030};
	auto const below = [&](std::size_t const _bound) {
		return std::uniform_int_distribution<std::size_t>{0, _bound - 1}(random);
	};
	for (unsigned long run = 0; run < 2000; ++run)
	{
		std::size_t const idCount = 1 + below(run % 50 == 0 ? 300 : 9);
		std::vector<std::uint8_t> spilled(idCount);
		SpillSet spills{spilled.data()};
		std::set<std::uint32_t> model;
		for (std::size_t step = 0; step < 3 * idCount; ++step)
		{
			auto const id = static_cast<std::uint32_t>(below(idCount));
			StackSlot const slot = below(3) == 0 ? nonVariables(id)[below(4)] : variable(id);
			bool const isVariable = slot.isValue() && !slot.isLiteralValue();
			std::vector<std::uint8_t> const before = spilled;
			bool const inserted = isVariable && model.insert(id).second;
			expect(spills.add(slot) == (inserted ? Status::Done : Status::AssertionFailed), "add result", run);
			for (std::size_t other = 0; other < idCount; ++other)
				expect(spilled[other] == (inserted && other == id ? 1 : before[other]), "add changes only its byte", run);
			for (std::uint32_t other = 0; other < idCount; ++other)
			{
				expect(spills.isSpilled(variable(other)) == model.contains(other), "isSpilled is membership", run);
				expect(isSpilled(variable(other), spills) == model.contains(other), "free isSpilled is membership", run);
				for (StackSlot const nonVariable: nonVariables(other))
					expect(!spills.isSpilled(nonVariable), "a slot that is not a variable is not spilled", run);
			}
		}
	}
}

/// spill_set: the bounds of the ids, a failed add, and the results
void spillSetEntry()
{
	StackSlot const literal{9, StackSlot::Kind::Value, InstOpcode::Const};
	StackSlot const adds[3] = {variable(2), literal, variable(0)};
	StackSlot const queries[5] = {variable(0), variable(1), variable(2), literal, StackSlot::makeJunk()};
	std::uint8_t results[6] = {7, 7, 7, 7, 7, 7};
	auto const unwritten = [&] {
		return std::all_of(results, results + 6, [](std::uint8_t const _r) { return _r == 7; });
	};

	// the add of the literal fails, after the add of variable 2
	std::uint8_t spilled[3] = {};
	expect(spill_set(3, spilled, adds, 3, queries, 5, results) == -2, "spill_set: add of a literal fails");
	expect(spilled[0] == 0 && spilled[1] == 0 && spilled[2] == 1, "spill_set: the adds before the failed add");
	expect(unwritten(), "spill_set: no result after a failed add");

	// each variable id of adds and queries must be below idCount; the payload of the other slots is not an id
	std::uint8_t bound[3] = {};
	StackSlot const good[2] = {variable(2), variable(0)};
	StackSlot const high[1] = {variable(3)};
	expect(spill_set(3, bound, high, 1, queries, 0, results) == -2, "spill_set: an add of id idCount");
	expect(spill_set(3, bound, good, 2, high, 1, results) == -2, "spill_set: a query of id idCount");
	expect(bound[0] == 0 && bound[1] == 0 && bound[2] == 0 && unwritten(),
		"spill_set: an id out of bounds writes nothing");
	StackSlot const top[1] = {variable(UINT32_MAX)};
	expect(spill_set(UINT32_MAX, bound, top, 0, top, 1, results) == -2 && unwritten(),
		"spill_set: id UINT32_MAX of UINT32_MAX ids");

	std::uint8_t fresh[3] = {};
	expect(spill_set(3, fresh, good, 2, queries, 5, results) == 0, "spill_set: two adds");
	expect(fresh[0] == 1 && fresh[1] == 0 && fresh[2] == 1, "spill_set: the bytes");
	expect(results[0] == 1 && results[1] == 0 && results[2] == 1 && results[3] == 0 && results[4] == 0 &&
		results[5] == 7, "spill_set: the query results");
	expect(spill_set(3, fresh, good + 1, 1, queries, 0, results) == -2, "spill_set: add of a spilled variable fails");
	expect(spill_set(3, fresh, good, 0, queries, 0, results) == 0, "spill_set: nothing");

	std::uint8_t none[1] = {7};
	StackSlot const highLiteral[1] = {{UINT32_MAX, StackSlot::Kind::Value, InstOpcode::Const}};
	expect(spill_set(0, none, highLiteral, 0, highLiteral, 1, results) == 0 && results[0] == 0,
		"spill_set: no ids, the payload of a literal is not an id");
	expect(spill_set(0, none, queries + 4, 0, queries + 3, 2, results) == 0 && results[0] == 0 && results[1] == 0,
		"spill_set: no ids, a literal and junk");
	expect(spill_set(0, none, queries + 3, 1, queries, 0, results) == -2 && none[0] == 7,
		"spill_set: no ids, add of a literal fails");
}

/// An offset of an entry
Optional<StackOffset> offset(std::size_t const _value)
{
	return StackOffset{_value};
}

Optional<StackOffset> const none = std::nullopt;

/// emission_pop: the bounds, a failed pop, and the result
void emissionPopEntry()
{
	StackSlot data[3] = {variable(0), variable(1), variable(2)};
	StackSlot const target[2] = {variable(0), variable(1)};
	std::uint8_t const spills[3] = {};
	Optional<StackOffset> const dest[3] = {offset(1), none, offset(0)};
	ShuffleOp ops[4];
	Optional<StackOffset> destinationOf[3] = {offset(7), offset(7), offset(7)};
	Optional<StackOffset> positionOf[2] = {offset(7), offset(7)};
	std::uint64_t pending = 7;

	// a C caller gives none as SIZE_MAX
	expect(std::bit_cast<std::uint64_t>(none) == SIZE_MAX, "none is SIZE_MAX");

	// more slots than target offsets: the slot without a destination is surplus
	expect(emission_pop(3, 2, data, target, dest, spills, 1, ops, destinationOf, positionOf, &pending) == 1,
		"emission_pop: one pop");
	expect(isPop(ops[0]), "emission_pop: the operation");
	expect(destinationOf[0] == offset(1) && destinationOf[1] == none && destinationOf[2] == offset(7),
		"emission_pop: destinationOf");
	expect(positionOf[0] == none && positionOf[1] == offset(0), "emission_pop: positionOf");
	expect(pending == 0, "emission_pop: pending");

	expect(emission_pop(3, 2, data, target, dest, spills, 0, ops, destinationOf, positionOf, &pending) == 0,
		"emission_pop: no pop");
	expect(destinationOf[0] == offset(1) && destinationOf[1] == none && destinationOf[2] == offset(0),
		"emission_pop: no pop, destinationOf");
	expect(positionOf[0] == offset(2) && positionOf[1] == offset(0) && pending == 0,
		"emission_pop: no pop, positionOf");

	expect(emission_pop(3, 2, data, target, dest, spills, 3, ops, destinationOf, positionOf, &pending) == 3,
		"emission_pop: every slot");
	expect(positionOf[0] == none && positionOf[1] == none && pending == 0, "emission_pop: every slot, positionOf");
	expect(emission_pop(3, 2, data, target, dest, spills, 4, ops, destinationOf, positionOf, &pending) == -2,
		"emission_pop: a pop of an empty stack fails");
	expect(emission_pop(0, 0, data, target, dest, spills, 1, ops, destinationOf, positionOf, &pending) == -2,
		"emission_pop: a pop of no slot fails");
	expect(emission_pop(0, 0, data, target, dest, spills, 0, ops, destinationOf, positionOf, &pending) == 0,
		"emission_pop: nothing");

	// the bounds of the mapping
	std::vector<StackSlot> big(1025, variable(0));
	std::vector<Optional<StackOffset>> bigDest(1025, none);
	std::vector<ShuffleOp> bigOps(1025);
	std::vector<Optional<StackOffset>> bigOut(1025, none);
	std::vector<std::uint8_t> bigSpills(1);
	expect(emission_pop(1024, 1024, big.data(), big.data(), bigDest.data(), bigSpills.data(), 1024, bigOps.data(),
		bigOut.data(), bigOut.data(), &pending) == 1024, "emission_pop: 1024 slots");
	expect(pending == 1024, "emission_pop: 1024 offsets pending");
	expect(emission_pop(1025, 0, big.data(), big.data(), bigDest.data(), bigSpills.data(), 0, bigOps.data(),
		bigOut.data(), bigOut.data(), &pending) == -2, "emission_pop: 1025 slots");
	expect(emission_pop(0, 1025, big.data(), big.data(), bigDest.data(), bigSpills.data(), 0, bigOps.data(),
		bigOut.data(), bigOut.data(), &pending) == -2, "emission_pop: 1025 offsets");
}

/// The buffers of remove_surplus after a call
struct Surplus
{
	std::int64_t count;
	std::vector<StackSlot> data;
	std::vector<Optional<StackOffset>> dest;
	/// 2m entries, so that AddressSanitizer finds a write past the bound of the contract
	std::vector<ShuffleOp> ops;
	std::uint64_t blocked[2];
	std::uint64_t height;
};

/// remove_surplus on the stack `_stack` with the destinations `_dest`, for a target of `_n` slots
Surplus removeSurplus(std::vector<StackSlot> const& _stack, std::vector<Optional<StackOffset>> const& _dest,
	std::size_t const _n)
{
	Surplus result{0, _stack, _dest, std::vector<ShuffleOp>(2 * _stack.size()), {7, 7}, 7};
	std::vector<StackSlot> const target(_n, variable(0));
	std::uint8_t const spills[1] = {};
	result.count = remove_surplus(_stack.size(), _n, result.data.data(), target.data(), result.dest.data(), spills, 1,
		result.ops.data(), result.blocked, &result.height);
	return result;
}

bool isSwap(ShuffleOp const _op, std::size_t const _depth)
{
	return _op.kind == ShuffleOp::Kind::Swap && _op.depth == _depth && sameSlot(_op.slot, StackSlot::makeJunk());
}

/// `_count` slots from variable `_from` up
std::vector<StackSlot> variables(std::uint32_t const _from, std::size_t const _count)
{
	std::vector<StackSlot> result;
	for (std::size_t i = 0; i < _count; ++i)
		result.push_back(variable(_from + static_cast<std::uint32_t>(i)));
	return result;
}

/// none, then the offsets from 0 to `_count - 1`
std::vector<Optional<StackOffset>> surplusBottom(std::size_t const _count)
{
	std::vector<Optional<StackOffset>> result{none};
	for (std::size_t i = 0; i < _count; ++i)
		result.push_back(offset(i));
	return result;
}

/// remove_surplus: the bounds, the outputs, and the entries of dest above the height
void removeSurplusEntry()
{
	StackSlot const literal{9, StackSlot::Kind::Value, InstOpcode::Const};

	Surplus const empty = removeSurplus({}, {}, 0);
	expect(empty.count == 0 && empty.height == 0 && empty.blocked[0] == 0 && empty.blocked[1] == 0,
		"remove_surplus: an empty stack");

	// no surplus: nothing changes
	Surplus const kept = removeSurplus({variable(1), variable(0)}, {offset(1), offset(0)}, 2);
	expect(kept.count == 0 && kept.height == 2 && kept.blocked[0] == 0 && kept.blocked[1] == 0,
		"remove_surplus: no surplus");
	expect(sameSlot(kept.data[0], variable(1)) && kept.dest[0] == offset(1) && kept.dest[1] == offset(0),
		"remove_surplus: no surplus, the stack");

	// a deep surplus: SWAP2, POP. The entry of dest above the height keeps its value.
	Surplus const deep = removeSurplus({literal, variable(0), variable(1)}, {none, offset(0), offset(1)}, 2);
	expect(deep.count == 2 && isSwap(deep.ops[0], 2) && isPop(deep.ops[1]), "remove_surplus: a deep surplus, ops");
	expect(deep.height == 2 && sameSlot(deep.data[0], variable(1)) && sameSlot(deep.data[1], variable(0)),
		"remove_surplus: a deep surplus, the stack");
	expect(deep.dest[0] == offset(1) && deep.dest[1] == offset(0) && deep.dest[2] == offset(1),
		"remove_surplus: a deep surplus, dest");
	expect(deep.blocked[0] == 0 && deep.blocked[1] == 0, "remove_surplus: a deep surplus, not blocked");

	// a surplus slot equal to the top takes over its destination: no swap
	Surplus const equal = removeSurplus({variable(0), variable(0)}, {none, offset(0)}, 1);
	expect(equal.count == 1 && isPop(equal.ops[0]) && equal.height == 1 && equal.dest[0] == offset(0) &&
		equal.dest[1] == offset(0), "remove_surplus: an equal surplus slot");
	// of two equal surplus slots the shallower one takes the destination: SWAP2. With the deeper one, SWAP1.
	Surplus const shallower = removeSurplus({variable(0), variable(0), variable(1), literal, variable(0)},
		{none, none, offset(1), none, offset(0)}, 2);
	expect(shallower.count == 4 && isPop(shallower.ops[0]) && isPop(shallower.ops[1]) && isSwap(shallower.ops[2], 2) &&
		isPop(shallower.ops[3]), "remove_surplus: the shallower equal surplus slot, ops");
	expect(shallower.height == 2 && sameSlot(shallower.data[0], variable(1)) && shallower.dest[0] == offset(1) &&
		shallower.dest[1] == offset(0), "remove_surplus: the shallower equal surplus slot");

	// a surplus bottom at depth 17 blocks, also after the pop of a surplus top; dest stays
	std::vector<StackSlot> stack = variables(1, 17);
	stack.insert(stack.begin(), literal);
	Surplus const blocked = removeSurplus(stack, surplusBottom(17), 17);
	expect(blocked.count == 0 && blocked.blocked[0] == 0 && blocked.blocked[1] == 1 && blocked.height == 18,
		"remove_surplus: blocked");
	expect(blocked.dest == surplusBottom(17), "remove_surplus: blocked, dest");
	stack.push_back(literal);
	std::vector<Optional<StackOffset>> dest = surplusBottom(17);
	dest.push_back(none);
	Surplus const popped = removeSurplus(stack, dest, 17);
	expect(popped.count == 1 && isPop(popped.ops[0]) && popped.blocked[0] == 0 && popped.blocked[1] == 1 &&
		popped.height == 18, "remove_surplus: blocked after a pop");

	// the bounds of the mapping: 1024 surplus slots, and 1025 slots or target offsets. Then nothing is written.
	Surplus const all = removeSurplus(std::vector<StackSlot>(1024, literal),
		std::vector<Optional<StackOffset>>(1024, none), 1024);
	expect(all.count == 1024 && all.height == 0 && std::all_of(all.ops.begin(), all.ops.begin() + 1024, isPop),
		"remove_surplus: 1024 surplus slots");
	Surplus const tooHigh = removeSurplus(std::vector<StackSlot>(1025, literal),
		std::vector<Optional<StackOffset>>(1025, none), 0);
	expect(tooHigh.count == -2 && tooHigh.height == 7 && tooHigh.blocked[0] == 7 && tooHigh.blocked[1] == 7,
		"remove_surplus: 1025 slots");
	Surplus const tooWide = removeSurplus({literal}, {none}, 1025);
	expect(tooWide.count == -2 && tooWide.height == 7 && tooWide.dest[0] == none, "remove_surplus: 1025 offsets");
}

/// remove_surplus on random states, against the properties of Shuffler.cpp's removeSurplus: it only swaps (SWAP1 to
/// SWAP16) and pops, at most 2m operations; the operations take the stack to the result; each destination stays
/// with a slot equal to the slot that it is bound for at the start, so a pop of a bound slot (a retag) leaves its
/// destination to an equal slot; it ends with no surplus slot, or it blocks at the shallowest surplus slot, and no
/// surplus slot is in swap reach. The order of the operations is the Lean model's, which the differential fuzzer
/// checks.
void removeSurplusProperties()
{
	std::mt19937_64 random{20261030};
	auto const below = [&](std::size_t const _bound) {
		return std::uniform_int_distribution<std::size_t>{0, _bound - 1}(random);
	};
	// the runs that block, that swap, and that retag: the generator has to reach each case
	unsigned long blockedRuns = 0;
	unsigned long swapRuns = 0;
	unsigned long retagRuns = 0;
	for (unsigned long run = 0; run < 20000; ++run)
	{
		std::size_t const m = below(run % 100 == 0 ? 1025 : 41);
		std::size_t const n = below(m + 3);
		// few distinct slots, so that some surplus slots are equal to the top
		std::vector<StackSlot> stack;
		for (std::size_t i = 0; i < m; ++i)
			stack.push_back(below(3) == 0 ? nonVariables(static_cast<std::uint32_t>(below(2)))[below(4)] :
				variable(static_cast<std::uint32_t>(below(4))));
		std::vector<std::size_t> free(n);
		for (std::size_t j = 0; j < n; ++j)
			free[j] = j;
		std::size_t const surplusOdds = 1 + below(4);
		std::vector<Optional<StackOffset>> dest;
		for (std::size_t i = 0; i < m; ++i)
			if (free.empty() || below(surplusOdds) == 0)
				dest.push_back(none);
			else
			{
				std::size_t const k = below(free.size());
				dest.push_back(offset(free[k]));
				free.erase(free.begin() + static_cast<std::ptrdiff_t>(k));
			}

		Surplus const result = removeSurplus(stack, dest, n);
		expect(result.count >= 0 && static_cast<std::size_t>(result.count) <= 2 * m, "removeSurplus: count", run);
		if (result.count < 0)
			continue;
		std::size_t const height = result.height;
		expect(height <= m, "removeSurplus: height", run);
		if (height > m)
			continue;

		// the operations take the stack to the result; `origin` holds the start position of each slot
		std::vector<std::size_t> origin(m);
		for (std::size_t pos = 0; pos < m; ++pos)
			origin[pos] = pos;
		bool swapped = false;
		bool retagged = false;
		for (std::int64_t i = 0; i < result.count; ++i)
		{
			ShuffleOp const op = result.ops[static_cast<std::size_t>(i)];
			if (isPop(op) && !origin.empty())
			{
				retagged = retagged || dest[origin.back()].has_value();
				origin.pop_back();
			}
			else if (op.kind == ShuffleOp::Kind::Swap && 1 <= op.depth && op.depth <= 16 && op.depth < origin.size() &&
				isSwap(op, op.depth))
			{
				std::swap(origin.back(), origin[origin.size() - 1 - op.depth]);
				swapped = true;
			}
			else
				expect(false, "removeSurplus: a SWAP1 to SWAP16 in the stack, or a POP", run);
		}
		expect(origin.size() == height, "removeSurplus: the pops", run);
		for (std::size_t pos = 0; pos < std::min(height, origin.size()); ++pos)
			expect(sameSlot(stack[origin[pos]], result.data[pos]), "removeSurplus: the stack", run);

		// each destination stays with an equal slot; the surplus slots are popped or block
		std::vector<std::size_t> before;
		std::vector<std::size_t> after;
		for (std::size_t pos = 0; pos < m; ++pos)
			if (dest[pos])
				before.push_back(dest[pos]->value);
		std::vector<std::size_t> surplus;
		for (std::size_t pos = 0; pos < height; ++pos)
			if (Optional<StackOffset> const d = result.dest[pos])
			{
				after.push_back(d->value);
				auto const source = std::find(dest.begin(), dest.end(), d);
				expect(source != dest.end() && sameSlot(stack[static_cast<std::size_t>(source - dest.begin())],
					result.data[pos]), "removeSurplus: a destination stays with an equal slot", run);
			}
			else
				surplus.push_back(pos);
		std::sort(before.begin(), before.end());
		std::sort(after.begin(), after.end());
		expect(before == after, "removeSurplus: no destination is lost or doubled", run);
		for (std::size_t pos = height; pos < m; ++pos)
			expect(result.dest[pos] == dest[pos], "removeSurplus: dest above the height is not written", run);

		if (result.blocked[1] == 0)
			expect(result.blocked[0] == 0 && surplus.empty(), "removeSurplus: done, no surplus", run);
		else
		{
			expect(!surplus.empty() && result.blocked[0] == surplus.back(), "removeSurplus: blocked at the shallowest",
				run);
			expect(!surplus.empty() && height - 1 - surplus.back() == 16 + result.blocked[1],
				"removeSurplus: the excess", run);
			expect(!surplus.empty() && height - 1 - surplus.back() > 16, "removeSurplus: no surplus in reach", run);
		}
		blockedRuns += result.blocked[1] != 0;
		swapRuns += swapped;
		retagRuns += retagged;
	}
	expect(blockedRuns > 100, "removeSurplus: blocked runs", blockedRuns);
	expect(swapRuns > 100, "removeSurplus: runs with a swap", swapRuns);
	expect(retagRuns > 100, "removeSurplus: runs with a retag", retagRuns);
}

/// The buffers of permute after a call
struct Permuted
{
	std::int64_t count;
	std::vector<StackSlot> data;
	std::vector<std::uint64_t> perm;
	/// 2h entries, so that AddressSanitizer finds a write past the bound of the contract
	std::vector<ShuffleOp> ops;
	std::uint64_t blocked[2];
	std::vector<Optional<StackOffset>> dest;
};

/// permute on the stack `_stack`, whose slot i goes to the offset `_perm[i]`
Permuted permuted(std::vector<StackSlot> const& _stack, std::vector<std::uint64_t> const& _perm)
{
	Permuted result{0, _stack, _perm, std::vector<ShuffleOp>(2 * _stack.size()), {7, 7},
		std::vector<Optional<StackOffset>>(_stack.size(), offset(7))};
	result.count = permute(_stack.size(), result.data.data(), result.perm.data(), result.ops.data(), result.blocked,
		result.dest.data());
	return result;
}

/// The offsets from `_from` up to `_to`, with the step `_step`
std::vector<std::uint64_t> naturals(std::uint64_t const _from, std::uint64_t const _to, std::int64_t const _step = 1)
{
	std::vector<std::uint64_t> result;
	for (std::uint64_t i = _from;; i += static_cast<std::uint64_t>(_step))
	{
		result.push_back(i);
		if (i == _to)
			return result;
	}
}

/// The offsets 0 to `_count - 1`
std::vector<std::uint64_t> firstOffsets(std::size_t const _count)
{
	std::vector<std::uint64_t> result;
	for (std::uint64_t i = 0; i < _count; ++i)
		result.push_back(i);
	return result;
}

std::vector<Optional<StackOffset>> offsets(std::vector<std::uint64_t> const& _values)
{
	std::vector<Optional<StackOffset>> result;
	for (std::uint64_t const value: _values)
		result.push_back(offset(value));
	return result;
}

/// The operations `_ops` are the swaps of the depths `_depths`
bool areSwaps(Permuted const& _result, std::vector<std::size_t> const& _depths)
{
	if (_result.count != static_cast<std::int64_t>(_depths.size()))
		return false;
	for (std::size_t i = 0; i < _depths.size(); ++i)
		if (!isSwap(_result.ops[i], _depths[i]))
			return false;
	return true;
}

bool sameSlots(std::vector<StackSlot> const& _a, std::vector<StackSlot> const& _b)
{
	return std::equal(_a.begin(), _a.end(), _b.begin(), _b.end(), sameSlot);
}

/// permute: the bounds, the outputs, the regroup of equal slots, and the blocked cases. The cases of
/// Fuzz/port_test.cpp, with the model results of Fuzz/Oracle.lean.
void permuteEntry()
{
	StackSlot const literal{0, StackSlot::Kind::Value, InstOpcode::Const};
	StackSlot const junk = StackSlot::makeJunk();

	Permuted const empty = permuted({}, {});
	expect(empty.count == 0 && empty.blocked[0] == 0 && empty.blocked[1] == 0, "permute: an empty stack");

	// the identity: no operation, and each slot keeps its destination
	Permuted const identity = permuted(variables(0, 3), {0, 1, 2});
	expect(identity.count == 0 && sameSlots(identity.data, variables(0, 3)) && identity.dest == offsets({0, 1, 2}) &&
		identity.blocked[0] == 0 && identity.blocked[1] == 0, "permute: the identity");

	// a swap with the top
	Permuted const top = permuted(variables(0, 3), {2, 1, 0});
	expect(areSwaps(top, {2}) && sameSlots(top.data, {variable(2), variable(1), variable(0)}) &&
		top.dest == offsets({0, 1, 2}) && top.blocked[0] == 0 && top.blocked[1] == 0, "permute: a swap with the top");
	expect(top.perm == naturals(2, 0, -1), "permute: perm is not written");

	// a 3-cycle away from the top: the top goes into the cycle and comes back
	Permuted const cycle = permuted(variables(0, 4), {1, 2, 0, 3});
	expect(areSwaps(cycle, {1, 3, 2, 1}) &&
		sameSlots(cycle.data, {variable(2), variable(0), variable(1), variable(3)}) && cycle.dest == offsets({0, 1, 2, 3}),
		"permute: a 3-cycle away from the top");

	// equal slots that only exchange their destinations: no operation, and the destinations stay
	Permuted const equal = permuted({variable(0), variable(1), variable(0)}, {2, 1, 0});
	expect(equal.count == 0 && equal.dest == offsets({2, 1, 0}) && equal.blocked[1] == 0,
		"permute: equal slots, no operation");
	// the regroup keeps the destinations: equal slots that take each other's offsets keep them
	Permuted const regroup = permuted({junk, junk, literal, literal}, {3, 2, 1, 0});
	expect(areSwaps(regroup, {2, 1, 3}) && sameSlots(regroup.data, {literal, literal, junk, junk}) &&
		regroup.dest == offsets({1, 0, 3, 2}), "permute: the regroup");
	// a misplaced slot equal to the top takes over its destination (a retag): two swaps
	Permuted const retag = permuted({variable(0), variable(1), variable(0)}, {1, 0, 2});
	expect(areSwaps(retag, {1, 2}) && sameSlots(retag.data, {variable(1), variable(0), variable(0)}) &&
		retag.dest == offsets({0, 1, 2}), "permute: a retag");

	// on 18 slots the top goes to offset 0, at depth 17: blocked, nothing changes
	std::vector<std::uint64_t> rotation = naturals(1, 16);
	rotation.insert(rotation.begin(), 17);
	rotation.push_back(0);
	Permuted const blocked = permuted(variables(0, 18), rotation);
	expect(blocked.count == 0 && blocked.blocked[0] == 0 && blocked.blocked[1] == 1 &&
		sameSlots(blocked.data, variables(0, 18)) && blocked.dest == offsets(rotation), "permute: blocked");
	// a SWAP16, then the slot at depth 17 blocks
	std::vector<std::uint64_t> exchange = naturals(0, 17);
	std::swap(exchange[0], exchange[1]);
	Permuted const later = permuted(variables(0, 18), exchange);
	std::vector<std::uint64_t> laterDest = naturals(2, 16);
	laterDest.insert(laterDest.begin(), {1, 17});
	laterDest.push_back(0);
	std::vector<StackSlot> laterData = variables(2, 15);
	laterData.insert(laterData.begin(), {variable(0), variable(17)});
	laterData.push_back(variable(1));
	expect(areSwaps(later, {16}) && later.blocked[0] == 0 && later.blocked[1] == 1, "permute: blocked after a swap");
	expect(sameSlots(later.data, laterData) && later.dest == offsets(laterDest), "permute: blocked after a swap, dest");

	// the bounds of the mapping: the identity and the reversal of 1024 slots, and 1025 slots. Then nothing is written.
	Permuted const all = permuted(variables(0, 1024), naturals(0, 1023));
	expect(all.count == 0 && all.blocked[1] == 0 && all.dest == offsets(naturals(0, 1023)), "permute: 1024 slots");
	Permuted const reversal = permuted(variables(0, 1024), naturals(1023, 0, -1));
	expect(reversal.count == 0 && reversal.blocked[0] == 0 && reversal.blocked[1] == 1007,
		"permute: the reversal of 1024 slots");
	Permuted const tooHigh = permuted(variables(0, 1025), naturals(0, 1024));
	expect(tooHigh.count == -2 && tooHigh.blocked[0] == 7 && tooHigh.blocked[1] == 7 &&
		sameSlots(tooHigh.data, variables(0, 1025)) && tooHigh.dest == std::vector(1025, offset(7)),
		"permute: 1025 slots");
}

/// permute on random permutations, against the properties of Shuffler.cpp's permute: it only swaps (SWAP1 to
/// SWAP16), at most 2h - 1 times; the swaps take the stack to the result; each destination stays with a slot equal to
/// the slot that it is bound for at the start; it ends with the target, the permuted stack, or it blocks at a slot
/// out of swap reach that is not equal to the top. buildBottomUp of the same state, with no slot to generate, gives
/// the same operations. The order of the operations is the Lean model's, which the differential fuzzer checks.
void permuteProperties()
{
	std::mt19937_64 random{20261030};
	auto const below = [&](std::size_t const _bound) {
		return std::uniform_int_distribution<std::size_t>{0, _bound - 1}(random);
	};
	// the runs that block, that swap, that move equal slots, and that end with a destination that is not the
	// offset of its slot: the generator has to reach each case
	unsigned long blockedRuns = 0;
	unsigned long swapRuns = 0;
	unsigned long equalRuns = 0;
	unsigned long keptRuns = 0;
	for (unsigned long run = 0; run < 20000; ++run)
	{
		std::size_t const h = below(run % 100 == 0 ? 1025 : 41);
		// few distinct slots, so that some slots are equal
		std::vector<StackSlot> stack;
		for (std::size_t i = 0; i < h; ++i)
			stack.push_back(below(3) == 0 ? nonVariables(static_cast<std::uint32_t>(below(2)))[below(4)] :
				variable(static_cast<std::uint32_t>(below(4 + below(2) * h))));
		// a shuffle, or a few exchanges of near offsets, so that some deep stacks are in reach
		std::vector<std::uint64_t> perm = firstOffsets(h);
		if (below(2) == 0)
			std::shuffle(perm.begin(), perm.end(), random);
		else if (h > 0)
			for (std::size_t k = below(5); k > 0; --k)
			{
				std::size_t const i = below(h);
				std::swap(perm[i], perm[std::min(h - 1, i + below(18))]);
			}
		std::vector<std::size_t> origin(h);
		for (std::size_t i = 0; i < h; ++i)
			origin[perm[i]] = i;
		// the target: the slot bound for each offset
		std::vector<StackSlot> target(h);
		for (std::size_t i = 0; i < h; ++i)
			target[perm[i]] = stack[i];

		Permuted const result = permuted(stack, perm);
		expect(result.count >= 0 && static_cast<std::size_t>(result.count) <= std::max<std::size_t>(2 * h, 1) - 1,
			"permute: count", run);
		if (result.count < 0)
			continue;
		expect(result.perm == perm, "permute: perm is not written", run);

		// the swaps take the stack to the result; `at` holds the start position of each slot
		std::vector<std::uint64_t> at = firstOffsets(h);
		for (std::int64_t i = 0; i < result.count; ++i)
		{
			ShuffleOp const op = result.ops[static_cast<std::size_t>(i)];
			if (op.kind == ShuffleOp::Kind::Swap && 1 <= op.depth && op.depth <= 16 && op.depth < h && isSwap(op, op.depth))
				std::swap(at.back(), at[h - 1 - op.depth]);
			else
				expect(false, "permute: a SWAP1 to SWAP16 in the stack", run);
		}
		for (std::size_t pos = 0; pos < h; ++pos)
			expect(sameSlot(stack[at[pos]], result.data[pos]), "permute: the stack", run);

		// each destination stays with an equal slot, and no destination is lost or doubled
		std::vector<bool> seen(h, false);
		bool kept = false;
		for (std::size_t pos = 0; pos < h; ++pos)
		{
			Optional<StackOffset> const d = result.dest[pos];
			expect(d.has_value() && d->value < h && !seen[d->value], "permute: dest is a permutation", run);
			if (!d || d->value >= h || seen[d->value])
				continue;
			seen[d->value] = true;
			expect(sameSlot(stack[origin[d->value]], result.data[pos]), "permute: a destination stays with an equal slot",
				run);
			kept = kept || d->value != pos;
		}

		if (result.blocked[1] == 0)
			expect(result.blocked[0] == 0 && sameSlots(result.data, target), "permute: done, the target", run);
		else
		{
			std::size_t const pos = result.blocked[0];
			expect(pos < h && h - 1 - pos == 16 + result.blocked[1], "permute: blocked, the excess", run);
			expect(pos < h && !sameSlot(result.data[pos], result.data[h - 1]), "permute: blocked, not equal to the top",
				run);
		}

		// buildBottomUp with no slot to generate: the same operations, the same stack, the same blocked slot
		{
			std::vector<StackSlot> data = stack;
			std::vector<ShuffleOp> ops(6 * h);
			std::uint64_t blocked[2] = {7, 7};
			std::vector<std::uint8_t> const spilled(4 + h);
			std::vector<Optional<StackOffset>> const dest = offsets(perm);
			std::int64_t const count = build_bottom_up(h, h, data.data(), target.data(), dest.data(), spilled.data(),
				ops.data(), blocked);
			bool const sameOps = count == result.count && count >= 0 && std::equal(ops.begin(), ops.begin() + count,
				result.ops.begin(), [](ShuffleOp const _a, ShuffleOp const _b) {
					return _a.kind == _b.kind && _a.depth == _b.depth && sameSlot(_a.slot, _b.slot);
				});
			expect(sameOps && sameSlots(data, result.data) && blocked[0] == result.blocked[0] &&
				blocked[1] == result.blocked[1], "permute: buildBottomUp gives the same result", run);
		}

		bool equalMoves = false;
		for (std::size_t i = 0; i < h && !equalMoves; ++i)
			for (std::size_t j = i + 1; j < h && !equalMoves; ++j)
				equalMoves = sameSlot(stack[i], stack[j]) && (perm[i] != i || perm[j] != j);
		blockedRuns += result.blocked[1] != 0;
		swapRuns += result.count > 0;
		equalRuns += equalMoves;
		keptRuns += result.blocked[1] == 0 && kept;
	}
	expect(blockedRuns > 100, "permute: blocked runs", blockedRuns);
	expect(swapRuns > 100, "permute: runs with a swap", swapRuns);
	expect(equalRuns > 100, "permute: runs that move equal slots", equalRuns);
	expect(keptRuns > 100, "permute: done runs with a destination that is not the offset of its slot", keptRuns);
}

/// The buffers of permute_at_lowest_height after a call
struct Lowest
{
	std::int64_t count;
	std::vector<StackSlot> data;
	std::vector<Optional<StackOffset>> dest;
	/// 2m entries, so that AddressSanitizer finds a write past the bound of the contract
	std::vector<ShuffleOp> ops;
	std::uint64_t blocked[2];
};

/// permute_at_lowest_height on the stack `_stack` with the destinations `_dest`, for a target of `_n` slots
Lowest atLowestHeight(std::vector<StackSlot> const& _stack, std::vector<Optional<StackOffset>> const& _dest,
	std::size_t const _n)
{
	Lowest result{0, _stack, _dest, std::vector<ShuffleOp>(2 * _stack.size()), {7, 7}};
	std::vector<StackSlot> const target(_n, variable(0));
	std::uint8_t const spills[1] = {};
	result.count = permute_at_lowest_height(_stack.size(), _n, result.data.data(), target.data(), result.dest.data(),
		spills, 1, result.ops.data(), result.blocked);
	return result;
}

/// The operations of `_result` are the swaps of the depths `_depths`
bool swapsAre(Lowest const& _result, std::vector<std::size_t> const& _depths)
{
	if (_result.count != static_cast<std::int64_t>(_depths.size()))
		return false;
	for (std::size_t i = 0; i < _depths.size(); ++i)
		if (!isSwap(_result.ops[i], _depths[i]))
			return false;
	return true;
}

/// The result of a call that fails: -2, and nothing is written
bool failed(Lowest const& _result, std::vector<StackSlot> const& _stack, std::vector<Optional<StackOffset>> const& _dest)
{
	return _result.count == -2 && sameSlots(_result.data, _stack) && _result.dest == _dest && _result.blocked[0] == 7 &&
		_result.blocked[1] == 7;
}

/// permute_at_lowest_height: the bounds, the outputs, parked slots and holes, and the blocked cases. The cases of
/// Fuzz/port_test.cpp, with the model results of Fuzz/Oracle.lean. Also Emission::permuteAtLowestHeight with a
/// mapping that the entry can not make.
void permuteAtLowestHeightEntry()
{
	StackSlot const literal{1, StackSlot::Kind::Value, InstOpcode::Const};

	Lowest const empty = atLowestHeight({}, {}, 0);
	expect(empty.count == 0 && empty.blocked[0] == 0 && empty.blocked[1] == 0,
		"permute_at_lowest_height: an empty stack");

	// all slots final: no operation
	Lowest const inPlace = atLowestHeight(variables(0, 2), offsets({0, 1}), 2);
	expect(inPlace.count == 0 && sameSlots(inPlace.data, variables(0, 2)) && inPlace.dest == offsets({0, 1}) &&
		inPlace.blocked[0] == 0 && inPlace.blocked[1] == 0, "permute_at_lowest_height: all slots final");

	// a slot parked in a hole stays
	Lowest const stays = atLowestHeight({variable(1)}, offsets({1}), 2);
	expect(stays.count == 0 && sameSlots(stays.data, {variable(1)}) && stays.dest == offsets({1}) &&
		stays.blocked[0] == 0 && stays.blocked[1] == 0, "permute_at_lowest_height: a parked slot in a hole");

	// a parked slot that is not in a hole goes to the hole
	Lowest const moves = atLowestHeight({variable(3), variable(1), variable(0)}, offsets({3, 1, 0}), 4);
	expect(swapsAre(moves, {2}) && sameSlots(moves.data, {variable(0), variable(1), variable(3)}) &&
		moves.dest == offsets({0, 1, 3}) && moves.blocked[1] == 0, "permute_at_lowest_height: a parked slot moves");

	// two parked slots take the holes in the order of their offsets, not of their destinations
	Lowest const order = atLowestHeight({variable(5), variable(4), variable(0), variable(1)}, offsets({5, 4, 0, 1}), 6);
	expect(swapsAre(order, {2, 1, 3, 1}) &&
		sameSlots(order.data, {variable(0), variable(1), variable(5), variable(4)}) &&
		order.dest == offsets({0, 1, 5, 4}), "permute_at_lowest_height: two parked slots keep their order");
	Lowest const ascending = atLowestHeight({variable(4), variable(5), variable(0), variable(1)},
		offsets({4, 5, 0, 1}), 6);
	expect(swapsAre(ascending, {2, 1, 3, 1}) &&
		sameSlots(ascending.data, {variable(0), variable(1), variable(4), variable(5)}) &&
		ascending.dest == offsets({0, 1, 4, 5}), "permute_at_lowest_height: two parked slots, ascending");

	// a parked slot that goes into a hole, next to one that stays in a hole
	Lowest const both = atLowestHeight({variable(3), variable(4), variable(0)}, offsets({3, 4, 0}), 5);
	expect(swapsAre(both, {2}) && sameSlots(both.data, {variable(0), variable(4), variable(3)}) &&
		both.dest == offsets({0, 4, 3}), "permute_at_lowest_height: a parked slot moves, one stays");

	// equal slots: permute moves the destinations with them
	Lowest const equal = atLowestHeight({variable(0), variable(0), variable(1)}, offsets({1, 2, 0}), 3);
	expect(swapsAre(equal, {2}) && sameSlots(equal.data, {variable(1), variable(0), variable(0)}) &&
		equal.dest == offsets({0, 2, 1}), "permute_at_lowest_height: equal slots");

	// a slot without a destination: the assertion fails, also for the bottom slot and below a parked slot
	expect(failed(atLowestHeight({variable(0), literal}, {offset(0), none}, 1), {variable(0), literal},
		{offset(0), none}), "permute_at_lowest_height: an unbound top");
	expect(failed(atLowestHeight({literal, variable(0)}, {none, offset(0)}, 1), {literal, variable(0)},
		{none, offset(0)}), "permute_at_lowest_height: an unbound bottom");
	expect(failed(atLowestHeight({variable(2), literal}, {offset(2), none}, 3), {variable(2), literal},
		{offset(2), none}), "permute_at_lowest_height: an unbound slot above a parked slot");

	// 17 slots: a swap at depth 16 is in reach. 18 slots: the swap at depth 17 blocks, and nothing changes.
	std::vector<StackSlot> reach = variables(1, 15);
	reach.insert(reach.begin(), variable(17));
	reach.push_back(variable(0));
	std::vector<std::uint64_t> reachDest = naturals(1, 15);
	reachDest.insert(reachDest.begin(), 17);
	reachDest.push_back(0);
	Lowest const reached = atLowestHeight(reach, offsets(reachDest), 18);
	std::vector<StackSlot> reachedData = variables(0, 16);
	reachedData.push_back(variable(17));
	std::vector<std::uint64_t> reachedDest = naturals(0, 15);
	reachedDest.push_back(17);
	expect(swapsAre(reached, {16}) && sameSlots(reached.data, reachedData) && reached.dest == offsets(reachedDest) &&
		reached.blocked[0] == 0 && reached.blocked[1] == 0, "permute_at_lowest_height: a swap at depth 16");
	std::vector<StackSlot> deep = variables(1, 16);
	deep.insert(deep.begin(), variable(18));
	deep.push_back(variable(0));
	std::vector<std::uint64_t> deepDest = naturals(1, 16);
	deepDest.insert(deepDest.begin(), 18);
	deepDest.push_back(0);
	Lowest const blocked = atLowestHeight(deep, offsets(deepDest), 19);
	expect(blocked.count == 0 && blocked.blocked[0] == 0 && blocked.blocked[1] == 1 && sameSlots(blocked.data, deep) &&
		blocked.dest == offsets(deepDest), "permute_at_lowest_height: blocked");

	// the bounds of the mapping: 1024 slots, and 1025 slots or target offsets. Then nothing is written.
	Lowest const all = atLowestHeight(variables(0, 1024), offsets(naturals(0, 1023)), 1024);
	expect(all.count == 0 && all.blocked[0] == 0 && all.blocked[1] == 0 && all.dest == offsets(naturals(0, 1023)),
		"permute_at_lowest_height: 1024 slots");
	std::vector<StackSlot> parkedHigh = variables(1, 1022);
	parkedHigh.insert(parkedHigh.begin(), variable(1023));
	std::vector<std::uint64_t> parkedHighDest = naturals(1, 1022);
	parkedHighDest.insert(parkedHighDest.begin(), 1023);
	Lowest const high = atLowestHeight(parkedHigh, offsets(parkedHighDest), 1024);
	expect(high.count == 0 && high.blocked[1] == 0 && high.dest == offsets(parkedHighDest),
		"permute_at_lowest_height: a slot parked at offset 1023");
	std::vector<std::uint64_t> rotation = naturals(1, 1023);
	rotation.push_back(0);
	Lowest const rotated = atLowestHeight(variables(0, 1024), offsets(rotation), 1024);
	expect(rotated.count == 0 && rotated.blocked[0] == 0 && rotated.blocked[1] == 1007,
		"permute_at_lowest_height: the rotation of 1024 slots");
	expect(failed(atLowestHeight(variables(0, 1025), offsets(naturals(0, 1024)), 1025), variables(0, 1025),
		offsets(naturals(0, 1024))), "permute_at_lowest_height: 1025 slots");
	expect(failed(atLowestHeight({variable(0)}, {offset(0)}, 1025), {variable(0)}, {offset(0)}),
		"permute_at_lowest_height: 1025 offsets");

	// A mapping that binds both slots for offset 0, and a target of 1 slot: the slot at offset 1 is above the target,
	// and the check of the Lean model fails before the planned mapping is read there. The planned mapping has an
	// entry for offset 1, so that without the check the permutation is {0, 0}, which is not a permutation. The entry
	// can not make this mapping.
	{
		StackSlot data[2] = {variable(0), variable(1)};
		ShuffleOp ops[4];
		StackSlot const target[1] = {variable(0)};
		std::uint8_t const spills[1] = {};
		Mapping planned{2, 2};
		planned.bind(StackOffset{1}, StackOffset{1});
		planned.bind(StackOffset{1}, StackOffset{0});
		planned.bind(StackOffset{0}, StackOffset{0});
		expect(opt(planned.destinationOf(StackOffset{1})) == 0 && opt(planned.positionOf(StackOffset{1})) == 1,
			"permuteAtLowestHeight: a slot above the target, the planned mapping");
		Emission emission{Stack{data, 2, ops}, target, 1, planned, spills};
		expect(emission.permuteAtLowestHeight() == Status::AssertionFailed && emission.traceSize() == 0,
			"permuteAtLowestHeight: a slot above the target");
	}

	// A planned mapping that is not the working mapping: the emission keeps a reference to the planned mapping, so a
	// change after the constructor changes the holes. Then the numbers of parked slots and holes differ, and the
	// assertion fails before any operation. The same emissions with no change are done.
	for (bool const change: {false, true})
	{
		StackSlot data[1] = {variable(0)};
		ShuffleOp ops[2];
		StackSlot const target[2] = {variable(0), variable(0)};
		std::uint8_t const spills[1] = {};
		Status const expected = change ? Status::AssertionFailed : Status::Done;

		// the slot is parked; the change makes offset 0 planned, so the slot is not in a hole, and there is no hole
		Mapping parked{1, 2};
		parked.bind(StackOffset{0}, StackOffset{1});
		Emission parkedEmission{Stack{data, 1, ops}, target, 2, parked, spills};
		if (change)
			parked.bind(StackOffset{0}, StackOffset{0});
		expect(parkedEmission.permuteAtLowestHeight() == expected && parkedEmission.traceSize() == 0,
			"permuteAtLowestHeight: more parked slots than holes", change);

		// the slot is final; the change unbinds offset 0, so it is a hole, and no slot is parked
		Mapping hole{1, 1};
		hole.bind(StackOffset{0}, StackOffset{0});
		Emission holeEmission{Stack{data, 1, ops}, target, 1, hole, spills};
		if (change)
			hole.pop(StackOffset{0});
		expect(holeEmission.permuteAtLowestHeight() == expected && holeEmission.traceSize() == 0,
			"permuteAtLowestHeight: more holes than parked slots", change);
	}
}

/// permute_at_lowest_height on random states, against Shuffler.cpp's permuteAtLowestHeight: the permutation of
/// Shuffler.cpp, made here with std::vector and std::sort, is a permutation of the offsets, and the permute entry
/// with it gives the same operations, stack and blocked slot, and the destinations of the same slots. If it is done,
/// the slot at offset pos is the slot that the permutation sends there: a slot with a destination below the height is
/// at it (or an equal slot is), and a parked slot is in a hole. Each destination stays with an equal slot. A slot
/// without a destination fails the assertion, and then nothing is written.
void permuteAtLowestHeightProperties()
{
	std::mt19937_64 random{20261030};
	auto const below = [&](std::size_t const _bound) {
		return std::uniform_int_distribution<std::size_t>{0, _bound - 1}(random);
	};
	// the runs that fail, that block, that are done with a swap, in which a parked slot moves to a hole, and in
	// which a parked slot stays in its hole: the generator has to reach each case
	unsigned long failedRuns = 0;
	unsigned long blockedRuns = 0;
	unsigned long swapRuns = 0;
	unsigned long moveRuns = 0;
	unsigned long stayRuns = 0;
	for (unsigned long run = 0; run < 20000; ++run)
	{
		std::size_t const h = below(run % 100 == 0 ? 1025 : 41);
		std::size_t const n = h + below(run % 100 == 0 ? 1025 - h : 6);
		// few distinct slots, so that some slots are equal
		std::vector<StackSlot> stack;
		for (std::size_t i = 0; i < h; ++i)
			stack.push_back(below(3) == 0 ? nonVariables(static_cast<std::uint32_t>(below(2)))[below(4)] :
				variable(static_cast<std::uint32_t>(below(4 + below(2) * h))));
		// distinct offsets below n: a sample, or the identity with a few exchanges of near offsets and a few slots
		// parked above the height, so that some deep stacks are in reach
		std::vector<std::uint64_t> values = firstOffsets(n);
		if (below(2) == 0)
		{
			std::shuffle(values.begin(), values.end(), random);
			values.resize(h);
		}
		else
		{
			std::shuffle(values.begin() + static_cast<std::ptrdiff_t>(h), values.end(), random);
			if (h > 0)
				for (std::size_t k = std::min(below(4), n - h); k > 0; --k)
					std::swap(values[below(h)], values[h + k - 1]);
			values.resize(h);
			if (h > 0)
				for (std::size_t k = below(5); k > 0; --k)
				{
					std::size_t const i = below(h);
					std::swap(values[i], values[std::min(h - 1, i + below(18))]);
				}
		}
		std::vector<Optional<StackOffset>> dest = offsets(values);
		bool const unbound = h > 0 && below(20) == 0;
		if (unbound)
			dest[below(h)] = none;

		Lowest const result = atLowestHeight(stack, dest, n);
		if (unbound)
		{
			expect(failed(result, stack, dest), "permuteAtLowestHeight: an unbound slot fails", run);
			++failedRuns;
			continue;
		}
		expect(result.count >= 0 && static_cast<std::size_t>(result.count) <= std::max<std::size_t>(2 * h, 1) - 1,
			"permuteAtLowestHeight: count", run);
		if (result.count < 0)
			continue;

		// the permutation of Shuffler.cpp: a hole is an offset that no slot is bound for
		std::vector<bool> planned(n, false);
		for (std::uint64_t const value: values)
			planned[value] = true;
		std::vector<std::uint64_t> permutation(h);
		std::vector<std::size_t> holes;
		std::vector<std::size_t> parked;
		bool stays = false;
		for (std::size_t pos = 0; pos < h; ++pos)
		{
			bool const isHole = !planned[pos];
			bool const isParked = values[pos] >= h;
			if (!isParked)
				permutation[pos] = values[pos];
			if (isParked && isHole)
				permutation[pos] = pos;
			if (isParked && !isHole)
				parked.push_back(pos);
			if (!isParked && isHole)
				holes.push_back(pos);
			stays = stays || (isParked && isHole);
		}
		expect(parked.size() == holes.size(), "permuteAtLowestHeight: parked slots and holes", run);
		if (parked.size() != holes.size())
			continue;
		std::sort(parked.begin(), parked.end());
		for (std::size_t i = 0; i < parked.size(); ++i)
			permutation[parked[i]] = holes[i];
		std::vector<std::size_t> origin(h, h);
		for (std::size_t pos = 0; pos < h; ++pos)
			origin[permutation[pos]] = pos;
		expect(std::find(origin.begin(), origin.end(), h) == origin.end(), "permuteAtLowestHeight: a permutation", run);

		// permute with this permutation: the same result. Its destinations are the permutation's, so the slot at
		// offset pos has the destination of the slot that permute's destination at pos comes from.
		Permuted const reference = permuted(stack, permutation);
		bool const sameOps = reference.count == result.count && std::equal(result.ops.begin(),
			result.ops.begin() + result.count, reference.ops.begin(), [](ShuffleOp const _a, ShuffleOp const _b) {
				return _a.kind == _b.kind && _a.depth == _b.depth && sameSlot(_a.slot, _b.slot);
			});
		expect(sameOps && sameSlots(result.data, reference.data) && result.blocked[0] == reference.blocked[0] &&
			result.blocked[1] == reference.blocked[1], "permuteAtLowestHeight: permute gives the same result", run);
		for (std::size_t pos = 0; pos < h; ++pos)
		{
			Optional<StackOffset> const d = reference.dest[pos];
			expect(d && d->value < h && result.dest[pos] == dest[origin[d->value]],
				"permuteAtLowestHeight: permute gives the same destinations", run);
		}

		// each destination stays with an equal slot, and no destination is lost or doubled
		std::vector<Optional<StackOffset>> before = dest;
		std::vector<Optional<StackOffset>> after = result.dest;
		auto const byValue = [](Optional<StackOffset> const _a, Optional<StackOffset> const _b) {
			return opt(_a) < opt(_b);
		};
		std::sort(before.begin(), before.end(), byValue);
		std::sort(after.begin(), after.end(), byValue);
		expect(before == after, "permuteAtLowestHeight: no destination is lost or doubled", run);
		for (std::size_t pos = 0; pos < h; ++pos)
		{
			auto const source = std::find(dest.begin(), dest.end(), result.dest[pos]);
			expect(source != dest.end() && sameSlot(stack[static_cast<std::size_t>(source - dest.begin())],
				result.data[pos]), "permuteAtLowestHeight: a destination stays with an equal slot", run);
		}

		if (result.blocked[1] == 0)
		{
			expect(result.blocked[0] == 0, "permuteAtLowestHeight: done", run);
			for (std::size_t pos = 0; pos < h; ++pos)
				expect(sameSlot(result.data[permutation[pos]], stack[pos]), "permuteAtLowestHeight: done, the slots",
					run);
		}
		else
		{
			std::size_t const pos = result.blocked[0];
			expect(pos < h && h - 1 - pos == 16 + result.blocked[1], "permuteAtLowestHeight: blocked, the excess", run);
		}
		blockedRuns += result.blocked[1] != 0;
		swapRuns += result.blocked[1] == 0 && result.count > 0;
		moveRuns += !parked.empty();
		stayRuns += stays;
	}
	expect(failedRuns > 100, "permuteAtLowestHeight: failed runs", failedRuns);
	expect(blockedRuns > 100, "permuteAtLowestHeight: blocked runs", blockedRuns);
	expect(swapRuns > 100, "permuteAtLowestHeight: done runs with a swap", swapRuns);
	expect(moveRuns > 100, "permuteAtLowestHeight: runs in which a parked slot moves", moveRuns);
	expect(stayRuns > 100, "permuteAtLowestHeight: runs in which a parked slot stays", stayRuns);
}

using Strategy = MappingBuilder::WildcardSlotsStrategy;

/// The positions of `_mapping` for its `_n` target offsets
std::vector<Opt> positions(Mapping const& _mapping, std::size_t const _n)
{
	std::vector<Opt> result;
	for (std::size_t j = 0; j < _n; ++j)
		result.push_back(opt(_mapping.positionOf(StackOffset{j})));
	return result;
}

/// The outputs of build_mapping: its result, the position of the slot bound for each target offset, and
/// sawWildcardCopy. Each output has a guard entry after it, which build_mapping must not write.
struct Built
{
	std::int64_t result;
	std::vector<Opt> sources;
	std::uint8_t saw;
};

/// The guard values of the outputs of buildMapping
std::size_t constexpr guardOffset = 4242;
std::uint8_t constexpr guardSaw = 42;

Built buildMapping(
	std::vector<StackSlot> const& _source,
	std::vector<StackSlot> const& _target,
	std::vector<std::uint8_t> const& _dropped,
	std::uint8_t const _strategy
)
{
	std::size_t const n = _target.size();
	std::vector<Optional<StackOffset>> sources(n + 1, offset(guardOffset));
	std::uint8_t saw[2] = {guardSaw, guardSaw};
	std::int64_t const result = build_mapping(
		_source.size(), n, _source.data(), _target.data(), _dropped.data(), _strategy, sources.data(), saw);
	expect(sources[n] == offset(guardOffset) && saw[1] == guardSaw, "build_mapping: writes past the outputs");
	std::vector<Opt> written;
	for (std::size_t j = 0; j < n; ++j)
		written.push_back(opt(sources[j]));
	return {result, written, saw[0]};
}

Built buildMapping(
	std::vector<StackSlot> const& _source,
	std::vector<StackSlot> const& _target,
	std::vector<std::uint8_t> const& _dropped,
	Strategy const _strategy
)
{
	return buildMapping(_source, _target, _dropped, static_cast<std::uint8_t>(_strategy));
}

/// The phases of MappingBuilder one by one, and a failed assertion of map
void mappingBuilderPhases()
{
	StackSlot const junk = StackSlot::makeJunk();
	StackSlot const literal{9, StackSlot::Kind::Value, InstOpcode::Const};
	// v0 in place, v1 two below its target offset, a copy of v2 in a wildcard slot, a literal to absorb
	std::vector<StackSlot> const source{variable(0), variable(2), literal, variable(1), variable(3)};
	std::vector<StackSlot> const target{variable(0), junk, variable(1), variable(2), junk, junk};
	std::uint8_t const dropped[5] = {0, 0, 0, 0, 1};
	for (Strategy const strategy: {Strategy::Leave, Strategy::Take})
	{
		bool const take = strategy == Strategy::Take;
		Mapping mapping{5, 6};
		MappingBuilder builder{source.data(), 5, target.data(), 6, dropped, strategy, mapping};
		expect(builder.mapInPlace() == Status::Done, "MappingBuilder: mapInPlace");
		expect(positions(mapping, 6) == std::vector<Opt>{0, {}, {}, {}, {}, {}}, "MappingBuilder: mapInPlace, the map");
		expect(builder.mapClosestCopies() == Status::Done, "MappingBuilder: mapClosestCopies");
		expect(positions(mapping, 6) == std::vector<Opt>{0, {}, 3, {}, {}, {}},
			"MappingBuilder: mapClosestCopies, the map");
		expect(!builder.sawWildcardCopy(), "MappingBuilder: no wildcard copy before mapWildcardSlotCopies");
		expect(builder.mapWildcardSlotCopies() == Status::Done, "MappingBuilder: mapWildcardSlotCopies");
		expect(builder.sawWildcardCopy(), "MappingBuilder: mapWildcardSlotCopies, a copy in a wildcard slot");
		expect(positions(mapping, 6) == (take ? std::vector<Opt>{0, {}, 3, 1, {}, {}} :
				std::vector<Opt>{0, {}, 3, {}, {}, {}}),
			"MappingBuilder: mapWildcardSlotCopies, the map", take);
		expect(builder.keepWildcardSlots() == Status::Done, "MappingBuilder: keepWildcardSlots");
		expect(positions(mapping, 6) == (take ? std::vector<Opt>{0, {}, 3, 1, {}, {}} :
				std::vector<Opt>{0, 1, 3, {}, {}, {}}),
			"MappingBuilder: keepWildcardSlots, the map", take);
		// the literal at 2 is the only slot left; the dropped v3 is not taken
		expect(builder.absorbSurplus() == Status::Done, "MappingBuilder: absorbSurplus");
		expect(positions(mapping, 6) == (take ? std::vector<Opt>{0, 2, 3, 1, {}, {}} :
				std::vector<Opt>{0, 1, 3, {}, 2, {}}),
			"MappingBuilder: absorbSurplus, the map", take);
		expect(mapping.destinationOf(StackOffset{4}) == none, "MappingBuilder: a dropped slot is not mapped", take);
	}

	// map asserts that the target offset has no source: the caller's mapping binds target offset 0 already
	std::vector<StackSlot> const inPlace{variable(0), variable(1)};
	std::uint8_t const kept[2] = {};
	Mapping bound{2, 2};
	bound.bind(StackOffset{1}, StackOffset{0});
	MappingBuilder builder{inPlace.data(), 2, inPlace.data(), 2, kept, Strategy::Leave, bound};
	expect(builder.mapInPlace() == Status::AssertionFailed, "MappingBuilder: map of a bound target offset fails");
	expect(positions(bound, 2) == std::vector<Opt>{1, {}} && bound.destinationOf(StackOffset{0}) == none,
		"MappingBuilder: a failed map does not bind");
}

/// build_mapping: the bounds, the tie rules, the strategies, function return labels and dropped slots
void buildMappingEntry()
{
	StackSlot const junk = StackSlot::makeJunk();
	StackSlot const label = nonVariables(0)[3];
	auto const literal = [](std::uint32_t const _value) {
		return StackSlot{_value, StackSlot::Kind::Value, InstOpcode::Const};
	};
	auto const fresh = [](Built const& _built) {
		return _built.saw == guardSaw &&
			std::all_of(_built.sources.begin(), _built.sources.end(), [](Opt const _o) { return _o == guardOffset; });
	};

	Built const empty = buildMapping({}, {}, {}, Strategy::Leave);
	expect(empty.result == 0 && empty.sources.empty() && empty.saw == 0, "build_mapping: empty");

	// the bounds: nothing is written
	std::vector<StackSlot> const big(1025, variable(0));
	std::vector<std::uint8_t> const bigDropped(1025);
	Built const tallSource = buildMapping(big, {variable(0)}, bigDropped, Strategy::Leave);
	expect(tallSource.result == -2 && fresh(tallSource), "build_mapping: 1025 source slots");
	Built const tallTarget = buildMapping({variable(0)}, big, bigDropped, Strategy::Leave);
	expect(tallTarget.result == -2 && fresh(tallTarget), "build_mapping: 1025 target slots");
	Built const strategy = buildMapping({variable(0)}, {variable(0)}, {0}, 2);
	expect(strategy.result == -2 && fresh(strategy), "build_mapping: strategy 2");
	Built const strategyMax = buildMapping({variable(0)}, {variable(0)}, {0}, 255);
	expect(strategyMax.result == -2 && fresh(strategyMax), "build_mapping: strategy 255");
	std::vector<StackSlot> const limit(1024, variable(0));
	Built const atLimit = buildMapping(limit, limit, std::vector<std::uint8_t>(1024), Strategy::Take);
	expect(atLimit.result == 0 && atLimit.saw == 0 && atLimit.sources.size() == 1024 &&
			atLimit.sources[0] == 0 && atLimit.sources[1023] == 1023,
		"build_mapping: 1024 slots in place");

	// in place
	Built const inPlace = buildMapping({variable(0), variable(1)}, {variable(0), variable(1)}, {0, 0}, Strategy::Leave);
	expect(inPlace.result == 0 && inPlace.saw == 0 && inPlace.sources == std::vector<Opt>{0, 1},
		"build_mapping: in place");

	// the closest copy: of two at the same distance the shallower one
	Built const copyTie = buildMapping({variable(0), literal(0), variable(0)}, {literal(1), variable(0)}, {0, 0, 0},
		Strategy::Leave);
	expect(copyTie.result == 0 && copyTie.sources == std::vector<Opt>{{}, 2}, "build_mapping: a tie of copies");
	Built const closer = buildMapping({variable(0), literal(0), literal(0), variable(0)}, {literal(1), variable(0)},
		{0, 0, 0, 0}, Strategy::Leave);
	expect(closer.result == 0 && closer.sources == std::vector<Opt>{{}, 0}, "build_mapping: the closer copy");

	// a wildcard absorbs the closest surplus slot: of two at the same distance the deeper one
	Built const surplusTie = buildMapping({literal(0), literal(1), literal(2)}, {literal(9), junk, literal(8)},
		{0, 1, 0}, Strategy::Leave);
	expect(surplusTie.result == 0 && surplusTie.sources == std::vector<Opt>{{}, 0, {}},
		"build_mapping: a tie of surplus slots");
	Built const surplus = buildMapping({literal(0), literal(1)}, {variable(5), variable(6), variable(7), junk}, {0, 0},
		Strategy::Leave);
	expect(surplus.result == 0 && surplus.sources == std::vector<Opt>{{}, {}, {}, 1},
		"build_mapping: the closest surplus slot");

	// a copy in a wildcard slot: Leave keeps it there, Take moves it
	Built const leave = buildMapping({variable(0), variable(1)}, {junk, variable(0)}, {0, 0}, Strategy::Leave);
	expect(leave.result == 0 && leave.saw == 1 && leave.sources == std::vector<Opt>{0, {}}, "build_mapping: Leave");
	Built const take = buildMapping({variable(0), variable(1)}, {junk, variable(0)}, {0, 0}, Strategy::Take);
	expect(take.result == 0 && take.saw == 1 && take.sources == std::vector<Opt>{1, 0}, "build_mapping: Take");
	// a function return label is taken for both strategies, and is not a wildcard copy
	for (Strategy const s: {Strategy::Leave, Strategy::Take})
	{
		Built const returnLabel = buildMapping({label, variable(1)}, {junk, label}, {0, 0}, s);
		expect(returnLabel.result == 0 && returnLabel.saw == 0 && returnLabel.sources == std::vector<Opt>{1, 0},
			"build_mapping: a function return label in a wildcard slot", static_cast<unsigned long>(s));
	}
	// a slot in a wildcard slot stays there, and a wildcard before it does not absorb it
	Built const keep = buildMapping({literal(0), literal(1)}, {junk, junk}, {1, 0}, Strategy::Leave);
	expect(keep.result == 0 && keep.sources == std::vector<Opt>{{}, 1}, "build_mapping: a slot in a wildcard slot");
	// a junk slot in a wildcard slot stays
	Built const junkInPlace = buildMapping({junk, junk}, {junk}, {0, 0}, Strategy::Leave);
	expect(junkInPlace.result == 0 && junkInPlace.sources == std::vector<Opt>{0}, "build_mapping: junk in place");

	// dropped slots are not mapped, whatever their byte
	for (std::uint8_t const byte: {1, 2, 255})
	{
		Built const dropped = buildMapping({variable(0)}, {variable(0)}, {byte}, Strategy::Leave);
		expect(dropped.result == 0 && dropped.sources == std::vector<Opt>{{}}, "build_mapping: a dropped slot", byte);
		Built const wildcard = buildMapping({literal(0)}, {junk}, {byte}, Strategy::Take);
		expect(wildcard.result == 0 && wildcard.sources == std::vector<Opt>{{}},
			"build_mapping: a dropped slot is not absorbed", byte);
	}
	Built const otherCopy = buildMapping({variable(0), variable(0)}, {variable(0)}, {1, 0}, Strategy::Leave);
	expect(otherCopy.result == 0 && otherCopy.sources == std::vector<Opt>{1}, "build_mapping: a copy of a dropped slot");
}

/// build_mapping on random stacks: the mapping is injective, binds equal slots or wildcards and no dropped slot, keeps
/// slots in place and in wildcard slots, leaves copies in wildcard slots for Leave, and leaves no target offset without
/// a source while a slot could serve it. The choice among the candidates is the Lean model's, which the differential
/// fuzzer checks.
void buildMappingProperties()
{
	std::mt19937_64 random{20261030};
	auto const below = [&](std::size_t const _bound) {
		return std::uniform_int_distribution<std::size_t>{0, _bound - 1}(random);
	};
	// few distinct slots, so that copies and equal slots are common
	auto const slot = [&] {
		return below(3) == 0 ? nonVariables(static_cast<std::uint32_t>(below(2)))[below(4)] :
			variable(static_cast<std::uint32_t>(below(3)));
	};
	unsigned long sawRuns = 0;
	unsigned long differRuns = 0;
	unsigned long absorbRuns = 0;
	unsigned long droppedCopyRuns = 0;
	unsigned long keptRuns = 0;
	for (unsigned long run = 0; run < 20000; ++run)
	{
		std::size_t const m = below(run % 100 == 0 ? 1025 : 13);
		std::size_t const n = below(run % 100 == 1 ? 1025 : 13);
		std::vector<StackSlot> source;
		for (std::size_t i = 0; i < m; ++i)
			source.push_back(slot());
		std::vector<StackSlot> target;
		for (std::size_t j = 0; j < n; ++j)
			target.push_back(slot());
		std::size_t const dropOdds = 2 + below(6);
		std::vector<std::uint8_t> dropped;
		for (std::size_t i = 0; i < m; ++i)
			dropped.push_back(below(dropOdds) == 0 ? static_cast<std::uint8_t>(1 + below(255)) : 0);
		auto const wildcardSlot = [&](std::size_t const _o) { return _o < n && target[_o].isJunk(); };

		Built const leave = buildMapping(source, target, dropped, Strategy::Leave);
		Built const take = buildMapping(source, target, dropped, Strategy::Take);
		expect(leave.result == 0 && take.result == 0, "buildMapping: done", run);
		if (leave.result != 0 || take.result != 0)
			continue;
		expect(leave.saw <= 1 && leave.saw == take.saw, "buildMapping: saw is a bool, the same for both", run);
		sawRuns += leave.saw;
		differRuns += leave.sources != take.sources;

		for (Built const* built: {&leave, &take})
		{
			bool const isTake = built == &take;
			std::vector<bool> bound(m);
			std::vector<Opt> destination(m);
			for (std::size_t j = 0; j < n; ++j)
				if (Opt const o = built->sources[j])
				{
					expect(*o < m && !bound[*o], "buildMapping: an injective map into the source", run);
					if (*o >= m || bound[*o])
						continue;
					bound[*o] = true;
					destination[*o] = j;
					expect(dropped[*o] == 0, "buildMapping: a dropped slot is not bound", run);
					expect(target[j].isJunk() || sameSlot(source[*o], target[j]),
						"buildMapping: an equal slot or a wildcard", run);
					absorbRuns += target[j].isJunk() && !sameSlot(source[*o], target[j]);
					if (!isTake && !target[j].isJunk() && !target[j].isFunctionReturnLabel())
						expect(!wildcardSlot(*o), "buildMapping: Leave leaves a copy in a wildcard slot", run);
				}
			for (std::size_t j = 0; j < std::min(m, n); ++j)
				if (sameSlot(source[j], target[j]) && dropped[j] == 0)
					expect(built->sources[j] == j, "buildMapping: a slot in place stays", run);
			// a slot in a wildcard slot stays, unless mapWildcardSlotCopies takes it for a demand
			for (std::size_t j = 0; j < std::min(m, n); ++j)
				if (wildcardSlot(j) && dropped[j] == 0)
				{
					Opt const k = destination[j];
					bool const taken =
						k && *k != j && !target[*k].isJunk() && (isTake || target[*k].isFunctionReturnLabel());
					expect(k == j || taken, "buildMapping: a slot in a wildcard slot stays", run);
					keptRuns += k == j && !sameSlot(source[j], target[j]);
				}
			bool const allBound = [&] {
				for (std::size_t o = 0; o < m; ++o)
					if (dropped[o] == 0 && !bound[o])
						return false;
				return true;
			}();
			for (std::size_t j = 0; j < n; ++j)
				if (!built->sources[j])
				{
					if (target[j].isJunk())
						expect(allBound, "buildMapping: a wildcard without a source, a free slot", run);
					else
						for (std::size_t o = 0; o < m; ++o)
						{
							bool const free = dropped[o] == 0 && !bound[o] && sameSlot(source[o], target[j]);
							bool const left = !isTake && !target[j].isFunctionReturnLabel() && wildcardSlot(o);
							expect(!free || left, "buildMapping: a target offset without a source, a free copy", run);
						}
				}
		}
		for (std::size_t o = 0; o < m; ++o)
			if (dropped[o] != 0)
				for (std::size_t j = 0; j < n; ++j)
					droppedCopyRuns += sameSlot(source[o], target[j]) && leave.sources[j].has_value();
	}
	expect(sawRuns > 1000, "buildMapping: runs with a wildcard copy", sawRuns);
	expect(differRuns > 1000, "buildMapping: runs where Leave and Take differ", differRuns);
	expect(absorbRuns > 1000, "buildMapping: runs that absorb a slot", absorbRuns);
	expect(droppedCopyRuns > 1000, "buildMapping: runs with a dropped slot that has a bound copy", droppedCopyRuns);
	expect(keptRuns > 1000, "buildMapping: runs that keep a slot in a wildcard slot", keptRuns);
}


/// The inputs of resolve: the source and the target, the plan (a destination for each source slot), the working
/// mapping (a destination for each slot of the working stack), the blocked offset and its excess, the spill set (a
/// byte for each variable id), spillingAllowed and the dropped bytes
struct Resolve
{
	std::vector<StackSlot> source;
	std::vector<StackSlot> target;
	std::vector<Optional<StackOffset>> plan;
	std::vector<Optional<StackOffset>> current;
	std::uint64_t offset;
	std::uint64_t excess;
	std::vector<std::uint8_t> spilled;
	std::uint8_t allowed;
	std::vector<std::uint8_t> dropped;
};

/// The outputs of resolve: its result, the spill set and the dropped bytes
struct Resolved
{
	std::int64_t result;
	std::vector<std::uint8_t> spilled;
	std::vector<std::uint8_t> dropped;

	bool operator==(Resolved const&) const = default;
};

/// The byte after the spill set and after the dropped bytes, which resolve must not write
std::uint8_t constexpr guardResolve = 0xa5;

Resolved resolveOn(Resolve const& _in)
{
	std::vector<std::uint8_t> spilled = _in.spilled;
	spilled.push_back(guardResolve);
	std::vector<std::uint8_t> dropped = _in.dropped;
	dropped.push_back(guardResolve);
	std::int64_t const result = resolve(_in.source.size(), _in.target.size(), _in.source.data(), _in.target.data(),
		_in.plan.data(), _in.current.size(), _in.current.data(), _in.offset, _in.excess, spilled.data(),
		_in.spilled.size(), _in.allowed, dropped.data());
	expect(spilled.back() == guardResolve && dropped.back() == guardResolve, "resolve: writes past the buffers");
	spilled.pop_back();
	dropped.pop_back();
	return {result, spilled, dropped};
}

/// The parts of `_s` between the separators: one more than the separators
std::vector<std::string> fields(std::string const& _s, char const _separator)
{
	std::vector<std::string> result{""};
	for (char const c: _s)
		if (c == _separator)
			result.emplace_back();
		else
			result.back() += c;
	return result;
}

/// The words of `_s`: none for the empty string
std::vector<std::string> wordsOf(std::string const& _s)
{
	return _s.empty() ? std::vector<std::string>{} : fields(_s, ' ');
}

/// The slot of a word of Fuzz/Oracle.lean: _ (junk), R (a function return label), vN (the variable N) or lN (the
/// literal N)
StackSlot slotOf(std::string const& _word)
{
	if (_word == "_")
		return StackSlot::makeJunk();
	if (_word == "R")
		return nonVariables(0)[3];
	std::uint32_t const payload = static_cast<std::uint32_t>(std::stoul(_word.substr(1)));
	return _word[0] == 'v' ? variable(payload) : nonVariables(payload)[0];
}

/// The inputs of a "resolve" case of Fuzz/Oracle.lean. The spill set has a byte for each variable id up to the
/// largest one of the case.
Resolve parseResolve(std::string const& _line)
{
	std::vector<std::string> const f = fields(_line, ';');
	Resolve in{};
	in.allowed = f.at(1) == "1";
	for (std::string const& word: wordsOf(f.at(2)))
		in.source.push_back(slotOf(word));
	for (std::string const& word: wordsOf(f.at(3)))
		in.target.push_back(slotOf(word));
	std::size_t idCount = 0;
	for (std::vector<StackSlot> const* stack: {&in.source, &in.target})
		for (StackSlot const slot: *stack)
			if (isVariable(slot))
				idCount = std::max<std::size_t>(idCount, slot.payload + 1);
	for (std::string const& word: wordsOf(f.at(4)))
		idCount = std::max<std::size_t>(idCount, std::stoul(word) + 1);
	in.spilled.assign(idCount, 0);
	for (std::string const& word: wordsOf(f.at(4)))
		in.spilled[std::stoul(word)] = 1;
	for (std::string const& word: wordsOf(f.at(5)))
		in.dropped.push_back(static_cast<std::uint8_t>(std::stoul(word)));
	auto const destinations = [](std::string const& _s) {
		std::vector<Optional<StackOffset>> result;
		for (std::string const& word: wordsOf(_s))
			result.push_back(word == "-" ? none : offset(std::stoul(word)));
		return result;
	};
	in.plan = destinations(f.at(6));
	in.current = destinations(f.at(7));
	std::vector<std::string> const blocked = wordsOf(f.at(8));
	in.offset = std::stoull(blocked.at(0));
	in.excess = std::stoull(blocked.at(1));
	return in;
}

/// `_out` in the result format of Fuzz/Oracle.lean: "ok", success (1 for 0, 0 for -1), the spilled variable ids and
/// the dropped bytes; or "err" for -2. An output outside the contract of resolve is in angle brackets.
std::string show(Resolved const& _out)
{
	if (_out.result == -2)
		return "err";
	if (_out.result != 0 && _out.result != -1)
		return "<result " + std::to_string(_out.result) + ">";
	std::string ids;
	for (std::size_t id = 0; id < _out.spilled.size(); ++id)
		if (_out.spilled[id] > 1)
			return "<spilled byte " + std::to_string(_out.spilled[id]) + ">";
		else if (_out.spilled[id] == 1)
			ids += (ids.empty() ? "" : " ") + std::to_string(id);
	std::string bytes;
	for (std::uint8_t const byte: _out.dropped)
		bytes += (bytes.empty() ? "" : " ") + std::to_string(byte);
	return std::string{"ok "} + (_out.result == 0 ? "1" : "0") + ";" + ids + ";" + bytes;
}

/// resolve on `_line` gives `_model`
void resolves(std::string const& _line, std::string const& _model)
{
	std::string const port = show(resolveOn(parseResolve(_line)));
	if (port != _model)
		std::fprintf(stderr, "resolve: %.300s => %.300s, the model: %.300s\n", _line.c_str(), port.c_str(),
			_model.c_str());
	expect(port == _model, "resolve: the result of the model");
}

/// `_word` `_count` times, separated by spaces
std::string repeated(std::string const& _word, std::size_t const _count)
{
	std::string result;
	for (std::size_t i = 0; i < _count; ++i)
		result += (i > 0 ? " " : "") + _word;
	return result;
}

/// `_prefix` and the numbers from `_from` to `_to`, separated by spaces
std::string numbered(std::string const& _prefix, std::size_t const _from, std::size_t const _to)
{
	std::string result;
	for (std::size_t i = _from; i <= _to; ++i)
		result += (i > _from ? " " : "") + _prefix + std::to_string(i);
	return result;
}

/// resolve against the model: each model result is the output of Fuzz/Oracle.lean (runLine on Planner.resolve) on
/// the case. The plans and the working mappings are made by hand: the port has no Emission.run yet.
void resolveCases()
{
	// each class wins over the higher classes: v9 (0: its target is a wildcard, and the target does not demand it), l1
	// (1), v2 (2: spilled), v3 (3: v3 at 0 is a retained copy) and v4 (4: a new spill). Each unit of excess drops one
	// more; at excess 6 nothing is left to drop, and the drops and the spill of the passes before stay.
	std::string const classes = "v3 v9 l1 v2 v3 v4;v3 _ l1 v2 v3 v4;2;0 0 0 0 0 0;0 1 2 3 4 5;0 1 2 3 4 5;0 ";
	resolves("resolve;1;" + classes + "0", "ok 1;2;0 0 0 0 0 0");
	resolves("resolve;1;" + classes + "1", "ok 1;2;0 1 0 0 0 0");
	resolves("resolve;1;" + classes + "2", "ok 1;2;0 1 1 0 0 0");
	resolves("resolve;1;" + classes + "3", "ok 1;2;0 1 1 1 0 0");
	resolves("resolve;1;" + classes + "4", "ok 1;2;0 1 1 1 1 0");
	resolves("resolve;1;" + classes + "5", "ok 1;2 4;0 1 1 1 1 1");
	resolves("resolve;1;" + classes + "6", "ok 0;2 4;0 1 1 1 1 1");
	resolves("resolve;1;" + classes + "1000", "ok 0;2 4;0 1 1 1 1 1");
	// spillingAllowed 0: v4 has no class, so the fifth pass finds nothing
	resolves("resolve;0;" + classes + "5", "ok 0;2;0 1 1 1 1 0");

	// a tie goes to the higher destination, whatever the order on the working stack
	resolves("resolve;0;v0 l1 l2;v0 l1 l2;;0 0 0;0 1 2;0 1 2;0 1", "ok 1;;0 0 1");
	resolves("resolve;0;v0 l1 l2;v0 l1 l2;;0 0 0;0 1 2;0 2 1;0 1", "ok 1;;0 0 1");
	resolves("resolve;0;v0 l1 l2;v0 l2 l1;;0 0 0;0 2 1;0 1 2;0 1", "ok 1;;0 1 0");
	resolves("resolve;1;v0 v1 v2;v0 v1 v2;;0 0 0;0 1 2;0 1 2;0 1", "ok 1;2;0 0 1");
	resolves("resolve;1;v0 v1 v2;v0 v1 v2;;0 0 0;0 1 2;2 1 0;0 1", "ok 1;1;0 1 0");
	resolves("resolve;1;l0 l0;l0 l0;;0 0;0 1;0 1;0 1", "ok 1;;0 1");

	// R is never dropped
	resolves("resolve;1;v0 R;v0 R;;0 0;0 1;0 1;0 1", "ok 0;;0 0");
	resolves("resolve;1;v0 v5 R;v0 v5 R;;0 0 0;0 1 2;0 1 2;0 1", "ok 1;5;0 1 0");
	resolves("resolve;1;v0 v5 R;v0 v5 R;;0 0 0;0 1 2;0 1 2;0 2", "ok 0;5;0 1 0");

	// class 4 only with spillingAllowed
	resolves("resolve;0;v0 v4;v0 v4;;0 0;0 1;0 1;0 1", "ok 0;;0 0");
	resolves("resolve;1;v0 v4;v0 v4;;0 0;0 1;0 1;0 1", "ok 1;4;0 1");
	resolves("resolve;1;v1000 v7;v1000 v7;;0 0;0 1;0 1;0 1", "ok 1;7;0 1");
	resolves("resolve;1;v1000 v7;v1000 v7;;0 0;0 1;0 1;0 2", "ok 0;7;0 1");
	// a spilled variable is class 2, before a copy (3)
	resolves("resolve;0;v3 v4 v3;v3 v4 v3;4;0 0 0;0 1 2;0 1 2;0 1", "ok 1;4;0 1 0");
	resolves("resolve;0;v3 v4 v3;v3 v4 v3;;0 0 0;0 1 2;0 1 2;0 1", "ok 1;;0 0 1");
	// two copies: the first pass drops one (3), then the other has no copy left and gets a spill (4)
	resolves("resolve;1;v0 v4 v4;v0 v4 v4;;0 0 0;0 1 2;0 1 2;0 1", "ok 1;;0 0 1");
	resolves("resolve;1;v0 v4 v4;v0 v4 v4;;0 0 0;0 1 2;0 1 2;0 2", "ok 1;4;0 1 1");
	resolves("resolve;1;v0 _ v0;v0 _ v0;;0 0 0;0 1 2;0 1 2;0 2", "ok 1;;0 1 1");

	// class 0: the target is a wildcard, and the slot is regenerable (a spill) or not demanded
	resolves("resolve;1;v6 v0 l1;v6 _ l1 v0;0;0 0 0;0 1 2;0 1 2 3;0 1", "ok 1;0;0 1 0");
	resolves("resolve;1;v6 v0 l1;v6 _ l1 v0;;0 0 0;0 1 2;0 1 2 3;0 1", "ok 1;;0 0 1");
	resolves("resolve;0;v6 v0 l1;v6 _ l1 v0;;0 0 0;0 1 2;0 1 2 3;0 2", "ok 0;;0 0 1");
	resolves("resolve;0;v6 v0 l1;v6 _ l1;;0 0 0;0 1 2;0 1 2;0 1", "ok 1;;0 1 0");
	// a demanded variable in a wildcard slot with another retained copy (0); without a retained copy it has no class
	resolves("resolve;0;v0 v0 l1;v0 _ l1;;0 0 0;0 1 2;0 1 2;0 1", "ok 1;;0 1 0");
	resolves("resolve;0;v0 v0 l1;v0 _ l1;;0 0 0;- 1 2;0 1 2;0 1", "ok 1;;0 0 1");
	resolves("resolve;0;v0 v0 l1;v1 _ l1;;0 0 0;- 1 2;0 1 2;0 1", "ok 1;;0 1 0");
	resolves("resolve;1;v0 v0;_ _;;0 0;0 1;0 1;0 1", "ok 1;;0 1");
	resolves("resolve;1;v0 _;v0 _;;0 0;0 1;0 1;0 1", "ok 1;;0 1");

	// another copy counts only if it is retained and not dropped in this call: dropped from an earlier call does
	// not count
	resolves("resolve;1;v0 v4 v4;v0 v4;;0 0 0;0 1 -;0 1;0 1", "ok 1;4;0 1 0");
	resolves("resolve;1;v4 v0 v4;v4 v0 v4;;0 0 0;0 1 2;0 1 2;1 1", "ok 1;;0 0 1");
	resolves("resolve;1;v4 v0 v4;v4 v0 v4;;1 0 0;0 1 2;0 1 2;1 1", "ok 1;;1 0 1");

	// the candidates: the retained slots above the blocked one; generated and surplus slots have no source
	resolves("resolve;0;v0 l1 l2;v0 l1 l2 l3;;0 0 0;0 1 2;0 3 - 1;0 1", "ok 1;;0 1 0");
	resolves("resolve;0;v0 l1 l2;v0 l1 l2 l3;;0 0 0;0 1 2;0 3 - 1;0 2", "ok 0;;0 1 0");
	resolves("resolve;1;v0 l1 l2;v0 l1 l2;;0 0 0;0 1 2;0 1 2;2 1", "ok 0;;0 0 0");
	resolves("resolve;1;v0 v1 v2;v0 v1 v2;;0 0 0;0 1 2;0 1 2;1 1", "ok 1;2;0 0 1");
	resolves("resolve;1;v0 v1 v2;v0 v1 v2;;0 0 0;0 1 2;0 1 2;0 0", "ok 1;;0 0 0");
	// a victim's byte becomes 1; the other bytes stay
	resolves("resolve;0;v0 l1 l2;v0 l1 l2;;7 255 255;0 1 2;0 1 2;0 1", "ok 1;;7 255 1");

	// the stack limit: 1024 distinct variables, all class 4; the two highest destinations go first
	resolves("resolve;1;" + numbered("v", 0, 1023) + ";" + numbered("v", 0, 1023) + ";;" + repeated("0", 1024) + ";" +
			numbered("", 0, 1023) + ";" + numbered("", 0, 1023) + ";0 2",
		"ok 1;1022 1023;" + repeated("0", 1022) + " 1 1");
}

/// Two calls on one spill set: the first spills v4 (class 4); then a copy of v4 is class 2 for the second, so the
/// second drops it before v3 (class 3)
void resolveSharedSpills()
{
	Resolved const first = resolveOn(parseResolve("resolve;1;v0 v4;v0 v4;;0 0;0 1;0 1;0 1"));
	expect(show(first) == "ok 1;4;0 1", "resolve: the first call spills v4");
	Resolve second = parseResolve("resolve;0;v3 v4 v3;v3 v4 v3;;0 0 0;0 1 2;0 1 2;0 1");
	expect(show(resolveOn(second)) == "ok 1;;0 0 1", "resolve: without the spill, v3 (class 3)");
	second.spilled = first.spilled;
	expect(show(resolveOn(second)) == "ok 1;4;0 1 0", "resolve: with the spill of the first call, v4 (class 2)");
}

/// The domain of the resolve entry: outside it the result is -2 and nothing is written
void resolveEntry()
{
	Resolve const base = parseResolve("resolve;1;v0 v4;v0 v4;;0 0;0 1;0 1;0 1");
	expect(show(resolveOn(base)) == "ok 1;4;0 1", "resolve: the base case");
	auto const rejects = [](Resolve const& _in, char const* const _what) {
		Resolved const out = resolveOn(_in);
		expect(out.result == -2 && out.spilled == _in.spilled && out.dropped == _in.dropped, _what);
	};
	for (std::uint64_t const offset: {std::uint64_t{2}, std::uint64_t{3}, UINT64_MAX})
	{
		Resolve in = base;
		in.offset = offset;
		rejects(in, "resolve: an offset not below the working stack");
	}
	Resolve empty = base;
	empty.current.clear();
	empty.offset = 0;
	rejects(empty, "resolve: an empty working stack");
	for (std::uint8_t const allowed: {2, 255})
	{
		Resolve in = base;
		in.allowed = allowed;
		rejects(in, "resolve: spillingAllowed is not 0 or 1");
	}
	Resolve fewIds = base;
	fewIds.spilled.resize(4);
	rejects(fewIds, "resolve: a source variable id not below idCount");
	Resolve noIds = base;
	noIds.spilled.clear();
	rejects(noIds, "resolve: no ids");
	Resolve tallSource = base;
	tallSource.source.assign(1025, variable(0));
	tallSource.plan.assign(1025, none);
	tallSource.dropped.assign(1025, 0);
	rejects(tallSource, "resolve: 1025 source slots");
	Resolve tallTarget = base;
	tallTarget.target.assign(1025, variable(0));
	rejects(tallTarget, "resolve: 1025 target slots");
	Resolve tallStack = base;
	tallStack.current.assign(1025, none);
	rejects(tallStack, "resolve: 1025 slots on the working stack");

	// in the domain: a variable id of the target, and the payload of a literal, above idCount
	Resolve targetId = parseResolve("resolve;1;v0 v4;v0 v4 v9;;0 0;0 1;0 1;0 1");
	targetId.spilled.resize(5);
	expect(show(resolveOn(targetId)) == "ok 1;4;0 1", "resolve: a target variable id above idCount");
	Resolve literal = parseResolve("resolve;1;R l1000;R l1000;;0 0;0 1;0 1;0 1");
	expect(literal.spilled.empty() && show(resolveOn(literal)) == "ok 1;;0 1", "resolve: a literal above idCount");
	// the largest excess: the passes stop when no candidate is left
	Resolve largest = parseResolve(
		"resolve;1;v3 v9 l1 v2 v3 v4;v3 _ l1 v2 v3 v4;2;0 0 0 0 0 0;0 1 2 3 4 5;0 1 2 3 4 5;0 1");
	largest.excess = UINT64_MAX;
	expect(show(resolveOn(largest)) == "ok 0;2 4;0 1 1 1 1 1", "resolve: the excess UINT64_MAX");
}

/// resolve on random cases: the result is 0 or -1; it drops only candidates (the retained slots above the blocked
/// one), never R, one for each unit of excess, and spills only variables that it drops; more excess drops a superset;
/// the order of the working stack above the blocked slot, and spillingAllowed when nothing is spilled, do not change
/// the result; and when it stops, each candidate left is R, or a variable that is not spilled with spillingAllowed 0.
/// The choice among the candidates is the Lean model's, which the differential test checks.
void resolveProperties()
{
	std::mt19937_64 random{20261030};
	auto const below = [&](std::size_t const _bound) {
		return std::uniform_int_distribution<std::size_t>{0, _bound - 1}(random);
	};
	// few distinct slots, so that copies and equal slots are common
	auto const slot = [&] {
		return below(3) == 0 ? nonVariables(static_cast<std::uint32_t>(below(2)))[below(4)] :
			variable(static_cast<std::uint32_t>(below(4)));
	};
	unsigned long stuckRuns = 0;
	unsigned long spillRuns = 0;
	unsigned long multiRuns = 0;
	unsigned long reorderRuns = 0;
	for (unsigned long run = 0; run < 20000; ++run)
	{
		std::size_t const m = below(run % 100 == 0 ? 65 : 9);
		std::size_t const n = below(run % 100 == 0 ? 65 : 9);
		Resolve in{};
		for (std::size_t i = 0; i < m; ++i)
			in.source.push_back(slot());
		for (std::size_t j = 0; j < n; ++j)
			in.target.push_back(slot());
		// the plan: buildMapping's or an injective one at random
		in.plan.assign(m, none);
		std::vector<std::size_t> offsets;
		for (std::size_t j = 0; j < n; ++j)
			offsets.push_back(j);
		std::shuffle(offsets.begin(), offsets.end(), random);
		if (below(2) == 0)
		{
			Built const built = buildMapping(in.source, in.target, std::vector<std::uint8_t>(m), Strategy::Leave);
			expect(built.result == 0, "resolve: buildMapping", run);
			for (std::size_t j = 0; j < n; ++j)
				if (Opt const o = built.sources[j])
					in.plan[*o] = offset(j);
		}
		else
		{
			for (std::size_t i = 0; i < m && i < n; ++i)
				if (below(4) != 0)
					in.plan[i] = offset(offsets[i]);
			std::shuffle(in.plan.begin(), in.plan.end(), random);
		}
		// the working stack: distinct destinations, and some slots without one
		std::shuffle(offsets.begin(), offsets.end(), random);
		std::size_t const h = 1 + below(m + n + 2);
		for (std::size_t pos = 0, next = 0; pos < h; ++pos)
			in.current.push_back(below(4) != 0 && next < n ? offset(offsets[next++]) : none);
		in.offset = below(2) == 0 ? 0 : below(h);
		in.excess = below(m + 3);
		in.allowed = below(2) == 1;
		in.spilled.assign(4 + below(3), 0);
		for (std::uint8_t& byte: in.spilled)
			byte = below(4) == 0;
		// no input byte is 1, so that the victims show
		for (std::size_t i = 0; i < m; ++i)
			in.dropped.push_back(below(2) == 0 ? 0 : static_cast<std::uint8_t>(2 + below(254)));

		Resolved const out = resolveOn(in);
		expect(out.result == 0 || out.result == -1, "resolve: done or stuck", run);
		if (out.result != 0 && out.result != -1)
			continue;
		std::vector<bool> candidate(m);
		for (std::size_t pos = in.offset + 1; pos < h; ++pos)
			if (in.current[pos])
				for (std::size_t i = 0; i < m; ++i)
					if (in.plan[i] == in.current[pos])
						candidate[i] = true;
		std::size_t victims = 0;
		for (std::size_t i = 0; i < m; ++i)
			if (out.dropped[i] == 1)
			{
				++victims;
				expect(candidate[i], "resolve: a victim is a candidate", run);
				expect(!in.source[i].isFunctionReturnLabel(), "resolve: R is never dropped", run);
			}
			else
				expect(out.dropped[i] == in.dropped[i], "resolve: only a victim's byte changes", run);
		expect(out.result == 0 ? victims == in.excess : victims < in.excess, "resolve: one victim for each unit", run);
		std::size_t spills = 0;
		for (std::size_t id = 0; id < in.spilled.size(); ++id)
			if (out.spilled[id] != in.spilled[id])
			{
				++spills;
				expect(in.spilled[id] == 0 && out.spilled[id] == 1 && in.allowed, "resolve: a new spill", run);
				bool victim = false;
				for (std::size_t i = 0; i < m; ++i)
					victim = victim || (out.dropped[i] == 1 && in.source[i] == variable(static_cast<std::uint32_t>(id)));
				expect(victim, "resolve: a new spill is of a victim", run);
			}
		spillRuns += spills > 0;
		multiRuns += victims > 1;
		if (out.result == -1)
		{
			++stuckRuns;
			SpillSet const spilled{const_cast<std::uint8_t*>(out.spilled.data())};
			for (std::size_t i = 0; i < m; ++i)
				if (candidate[i] && out.dropped[i] != 1)
					expect(in.source[i].isFunctionReturnLabel() ||
							(isVariable(in.source[i]) && !spilled.isSpilled(in.source[i]) && !in.allowed),
						"resolve: a candidate left has no class", run);
		}

		// one more unit of excess: the same victims and at most one more, and the same spills and at most one more
		Resolve more = in;
		++more.excess;
		Resolved const moreOut = resolveOn(more);
		if (out.result == -1)
			expect(moreOut == out, "resolve: stuck stays stuck", run);
		std::size_t moreVictims = 0;
		for (std::size_t i = 0; i < m; ++i)
		{
			expect(out.dropped[i] != 1 || moreOut.dropped[i] == 1, "resolve: more excess keeps the victims", run);
			moreVictims += moreOut.dropped[i] == 1;
		}
		expect(moreVictims <= victims + 1, "resolve: more excess drops at most one more", run);
		for (std::size_t id = 0; id < in.spilled.size(); ++id)
			expect(out.spilled[id] == 0 || moreOut.spilled[id] != 0, "resolve: more excess keeps the spills", run);

		// the largest excess stops where the excess m + 1 stops
		Resolve largest = in;
		largest.excess = UINT64_MAX;
		Resolve enough = in;
		enough.excess = m + 1;
		Resolved const enoughOut = resolveOn(enough);
		expect(enoughOut.result == -1 && resolveOn(largest) == enoughOut, "resolve: the excess UINT64_MAX", run);

		// another order above the blocked slot
		Resolve reordered = in;
		std::shuffle(reordered.current.begin() + static_cast<std::ptrdiff_t>(in.offset) + 1, reordered.current.end(),
			random);
		reorderRuns += reordered.current != in.current;
		expect(resolveOn(reordered) == out, "resolve: the order above the blocked slot", run);

		// spillingAllowed matters only for a spill
		if (spills == 0 && in.allowed)
		{
			Resolve forbidden = in;
			forbidden.allowed = 0;
			expect(resolveOn(forbidden) == out, "resolve: spillingAllowed without a spill", run);
		}
	}
	expect(stuckRuns > 1000, "resolve: stuck runs", stuckRuns);
	expect(spillRuns > 1000, "resolve: runs with a new spill", spillRuns);
	expect(multiRuns > 1000, "resolve: runs with more than one victim", multiRuns);
	expect(reorderRuns > 1000, "resolve: runs with another order", reorderRuns);
}
}

int main()
{
	stackPop();
	mappingConstructor();
	mappingPop();
	mappingOperations();
	emission();
	emissionPopEntry();
	spillSet();
	spillSetOperations();
	spillSetEntry();
	removeSurplusEntry();
	removeSurplusProperties();
	permuteEntry();
	permuteProperties();
	permuteAtLowestHeightEntry();
	permuteAtLowestHeightProperties();
	mappingBuilderPhases();
	buildMappingEntry();
	buildMappingProperties();
	resolveCases();
	resolveSharedSpills();
	resolveEntry();
	resolveProperties();
	if (failures > 0)
	{
		std::fprintf(stderr, "%d failures\n", failures);
		return EXIT_FAILURE;
	}
	std::printf("unit_test: all checks pass\n");
	return EXIT_SUCCESS;
}
