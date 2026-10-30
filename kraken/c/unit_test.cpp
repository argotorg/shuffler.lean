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
	if (failures > 0)
	{
		std::fprintf(stderr, "%d failures\n", failures);
		return EXIT_FAILURE;
	}
	std::printf("unit_test: all checks pass\n");
	return EXIT_SUCCESS;
}
