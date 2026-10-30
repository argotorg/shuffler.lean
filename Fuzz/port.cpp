// The kraken/c port in the differential fuzzer. Each unit of the port has one entry in `units`: the kind of its
// cases, a runner that converts a case to the C interface of the port and its result to the result format of
// Fuzz/Oracle.lean, and the part of the model result that the C interface gives.
//
// The port is linked as the asm of kraken/c (the files that the Kraken proofs read), not compiled again.

#include "port.h"
#include "text.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

using fuzztext::join;
using fuzztext::parseNat;
using fuzztext::split;
using fuzztext::words;

namespace
{

/// StackSlot of kraken/c/build_bottom_up.cpp
struct Slot
{
	std::uint32_t payload;
	std::uint8_t kind;
	std::uint8_t valueOpcode;
	/// build_bottom_up does not read them
	std::uint8_t padding[2];
};
static_assert(sizeof(Slot) == 8 && offsetof(Slot, kind) == 4 && offsetof(Slot, valueOpcode) == 5);

enum SlotKind : std::uint8_t { Value = 0, Junk = 1, FunctionCallReturnLabel = 2, FunctionReturnLabel = 3 };
/// InstOpcode: a literal is a Const; a variable gets Phi, which is not Const
enum Opcode : std::uint8_t { Const = 0, Phi = 1, Unreachable = 5 };

/// ShuffleOp of kraken/c/build_bottom_up.cpp
struct Op
{
	std::uint8_t kind;
	std::uint8_t depth;
	/// the guard check of runBuildBottomUp compares whole entries, so the padding is a member
	std::uint8_t padding[2];
	Slot slot;
};
static_assert(sizeof(Op) == 12 && offsetof(Op, depth) == 1 && offsetof(Op, padding) == 2 && offsetof(Op, slot) == 4);

enum OpKind : std::uint8_t { Swap = 0, Dup = 1, Pop = 2, Push = 3, Load = 4, Store = 5 };

/// The port does not read the padding bytes, so they get a value that the encoding does not use
std::uint8_t constexpr padding = 0xa5;

/// "v" n is the variable n, "l" n the literal n, "_" junk and "R" the function return label
Slot parseSlot(std::string const& _token)
{
	if (_token == "_")
		return {0, Junk, Unreachable, {padding, padding}};
	if (_token == "R")
		return {0, FunctionReturnLabel, Unreachable, {padding, padding}};
	if (_token.size() > 1 && (_token[0] == 'v' || _token[0] == 'l'))
		return {parseNat(_token.substr(1)), Value, _token[0] == 'l' ? Const : Phi, {padding, padding}};
	throw std::invalid_argument("not a slot: " + _token);
}

std::vector<Slot> parseStack(std::string const& _s)
{
	std::vector<Slot> stack;
	for (std::string const& token: words(_s))
		stack.push_back(parseSlot(token));
	return stack;
}

/// The inverse of parseSlot; a slot that parseSlot does not give is shown in angle brackets, so that it differs
/// from each model result
std::string showSlot(Slot const _slot)
{
	if (_slot.kind == Junk && _slot.payload == 0 && _slot.valueOpcode == Unreachable)
		return "_";
	if (_slot.kind == FunctionReturnLabel && _slot.payload == 0 && _slot.valueOpcode == Unreachable)
		return "R";
	if (_slot.kind == Value && (_slot.valueOpcode == Const || _slot.valueOpcode == Phi))
		return (_slot.valueOpcode == Const ? "l" : "v") + std::to_string(_slot.payload);
	return "<slot " + std::to_string(_slot.kind) + " " + std::to_string(_slot.valueOpcode) + " " +
		std::to_string(_slot.payload) + ">";
}

std::string showStack(std::vector<Slot> const& _stack)
{
	std::vector<std::string> names;
	for (Slot const& slot: _stack)
		names.push_back(showSlot(slot));
	return join(names);
}

/// The operations in the format of Fuzz/Oracle.lean; an operation that the port must not give is shown in angle
/// brackets
std::string showOps(std::vector<Op> const& _ops)
{
	std::vector<std::string> result;
	for (Op const& op: _ops)
		switch (op.kind)
		{
		case Swap: result.push_back("SWAP" + std::to_string(op.depth)); break;
		case Dup: result.push_back("DUP" + std::to_string(op.depth)); break;
		case Pop: result.push_back("POP"); break;
		case Push: result.push_back("PUSH:" + showSlot(op.slot)); break;
		case Load: result.push_back("LOAD:" + showSlot(op.slot)); break;
		default: result.push_back("<op " + std::to_string(op.kind) + ">"); break;
		}
	return join(result);
}

/// The fields of a model result before its last field: a state result without its destinations
std::string withoutLastField(std::string const& _model)
{
	std::size_t const last = _model.rfind(';');
	return last == std::string::npos ? _model : _model.substr(0, last);
}

}

extern "C" std::int64_t build_bottom_up(
	std::uint64_t m,
	std::uint64_t n,
	Slot* data,
	Slot const* target,
	std::uint64_t const* dest,
	std::uint8_t const* spilled,
	Op* ops,
	std::uint64_t* blocked
);

extern "C" std::int64_t emission_pop(
	std::uint64_t m,
	std::uint64_t n,
	Slot* data,
	Slot const* target,
	std::uint64_t const* dest,
	std::uint8_t const* spilled,
	std::uint64_t count,
	Op* ops,
	std::uint64_t* destinationOf,
	std::uint64_t* positionOf,
	std::uint64_t* pending
);

extern "C" std::int64_t spill_set(
	std::uint64_t idCount,
	std::uint8_t* spilled,
	Slot const* adds,
	std::uint64_t addCount,
	Slot const* queries,
	std::uint64_t queryCount,
	std::uint8_t* results
);

namespace
{

/// The maximal stack size of build_bottom_up (the EVM stack limit)
std::size_t constexpr maxStackSize = 1024;

/// The none of an Optional<StackOffset> of kraken/c/build_bottom_up.cpp
std::uint64_t constexpr none = SIZE_MAX;

std::string showOffset(std::uint64_t const _offset)
{
	return _offset == none ? "-" : std::to_string(_offset);
}

/// The destinations of a case for a stack of `_m` slots and a target of `_n` slots: per slot a target offset, or
/// "-" (none). Throws std::invalid_argument unless the offsets are distinct and below `_n`.
std::vector<std::uint64_t> parseDests(std::string const& _s, std::size_t const _m, std::size_t const _n)
{
	std::vector<std::string> const destWords = words(_s);
	if (destWords.size() != _m)
		throw std::invalid_argument("not one destination per slot: " + _s);
	std::vector<std::uint64_t> dest;
	std::vector<bool> bound(_n);
	for (std::string const& word: destWords)
	{
		if (word == "-")
		{
			dest.push_back(none);
			continue;
		}
		std::uint32_t const d = parseNat(word);
		if (d >= _n || bound[d])
			throw std::invalid_argument("destination out of the target or bound twice: " + word);
		bound[d] = true;
		dest.push_back(d);
	}
	return dest;
}

/// spilled[id] for each variable id of the case: 1 for the ids of the field `_vars`, else 0
std::vector<std::uint8_t> parseSpilled(
	std::string const& _vars,
	std::vector<Slot> const& _source,
	std::vector<Slot> const& _target
)
{
	std::vector<std::uint32_t> spills;
	for (std::string const& word: words(_vars))
		spills.push_back(parseNat(word));
	std::uint32_t maxId = 0;
	for (std::vector<Slot> const* slots: {&_source, &_target})
		for (Slot const& slot: *slots)
			if (slot.kind == Value && slot.valueOpcode == Phi)
				maxId = std::max(maxId, slot.payload);
	for (std::uint32_t const id: spills)
		maxId = std::max(maxId, id);
	std::vector<std::uint8_t> spilled(std::size_t{maxId} + 1);
	for (std::uint32_t const id: spills)
		spilled[id] = 1;
	return spilled;
}

/// The length of the guard area after each output buffer of the port, and its contents
std::size_t constexpr guard = 16;
Slot constexpr guardSlot{0xdeadbeef, 0xee, 0xee, {0xee, 0xee}};
Op constexpr guardOp{0xee, 0xee, {0xee, 0xee}, guardSlot};
std::uint64_t constexpr guardWord = 0xeeeeeeeeeeeeeeee;
std::uint8_t constexpr guardByte = 0xee;

/// Each element of `_buffer` from `_from` has the bytes of `_value`
template <typename T>
bool intact(std::vector<T> const& _buffer, std::size_t const _from, T const& _value)
{
	return std::all_of(_buffer.begin() + static_cast<std::ptrdiff_t>(_from), _buffer.end(), [&](T const& _x) {
		return std::memcmp(&_x, &_value, sizeof _x) == 0;
	});
}

/// A case "bottomup;" stack ";" target ";" dests ";" vars, in the domain of build_bottom_up: every slot has a
/// destination, the destinations are distinct and below the target size, and the target has at most
/// maxStackSize slots.
/// The result is "ok" or "blocked OFFSET EXCESS", the final stack and the operations, or "err".
std::string runBuildBottomUp(std::vector<std::string> const& _fields)
{
	if (_fields.size() != 4)
		throw std::invalid_argument("not a state");
	std::vector<Slot> const source = parseStack(_fields[0]);
	std::vector<Slot> const target = parseStack(_fields[1]);
	std::size_t const m = source.size();
	std::size_t const n = target.size();
	if (n > maxStackSize)
		throw std::invalid_argument("more target slots than the stack limit");
	std::vector<std::uint64_t> const dest = parseDests(_fields[2], m, n);
	if (std::find(dest.begin(), dest.end(), none) != dest.end())
		throw std::invalid_argument("a slot without a destination: " + _fields[2]);
	std::vector<std::uint8_t> const spilled = parseSpilled(_fields[3], source, target);

	// build_bottom_up writes at most n slots and 6 n operations. A guard area after each buffer must stay as it is.
	std::vector<Slot> data(n + guard, guardSlot);
	std::copy(source.begin(), source.end(), data.begin());
	std::vector<Op> ops(6 * n + guard, guardOp);
	std::uint64_t blocked[2] = {0xeeee, 0xeeee};
	std::int64_t const count =
		build_bottom_up(m, n, data.data(), target.data(), dest.data(), spilled.data(), ops.data(), blocked);
	if (!intact(data, n, guardSlot) || !intact(ops, 6 * n, guardOp))
		return "<port wrote past a buffer>";
	if (count == -2)
		return "err";
	if (count < 0 || static_cast<std::uint64_t>(count) > 6 * n)
		return "<port result " + std::to_string(count) + ">";
	ops.resize(static_cast<std::size_t>(count));
	// each operation but a swap pushes one slot
	std::size_t const size = m + static_cast<std::size_t>(std::count_if(ops.begin(), ops.end(), [](Op const& _op) {
		return _op.kind != Swap;
	}));
	if (size > n)
		return "<port stack of " + std::to_string(size) + " slots>";
	data.resize(size);
	// "ok" is 0 and 0, a block has a positive excess
	std::string const status =
		blocked[1] != 0 ? "blocked " + std::to_string(blocked[0]) + " " + std::to_string(blocked[1]) :
		blocked[0] == 0 ? "ok" :
		"<port blocked " + std::to_string(blocked[0]) + " 0>";
	return status + ";" + showStack(data) + ";" + showOps(ops);
}

/// A case "pop;" stack ";" target ";" dests ";" vars ";" count, in the domain of emission_pop: the destinations
/// are distinct and below the target size, or "-", the stack and the target have at most maxStackSize slots, and
/// count is at most one more than the stack size.
/// The result is "ok", the final stack, the operations, the destinations, per target offset the position of the
/// slot bound for it, and the pending generations; or "err".
std::string runPop(std::vector<std::string> const& _fields)
{
	if (_fields.size() != 5)
		throw std::invalid_argument("not a pop case");
	std::vector<Slot> const source = parseStack(_fields[0]);
	std::vector<Slot> const target = parseStack(_fields[1]);
	std::size_t const m = source.size();
	std::size_t const n = target.size();
	if (m > maxStackSize || n > maxStackSize)
		throw std::invalid_argument("more slots than the stack limit");
	std::vector<std::uint64_t> const dest = parseDests(_fields[2], m, n);
	std::vector<std::uint8_t> const spilled = parseSpilled(_fields[3], source, target);
	std::size_t const count = parseNat(_fields[4]);
	if (count > m + 1)
		throw std::invalid_argument("more pops than one more than the stack size: " + _fields[4]);

	// emission_pop does not write data and writes at most count operations, m destinations and n positions. A guard
	// area after each buffer must stay as it is.
	std::vector<Slot> data(m + guard, guardSlot);
	std::copy(source.begin(), source.end(), data.begin());
	std::vector<Slot> const before = data;
	std::vector<Op> ops(count + guard, guardOp);
	std::vector<std::uint64_t> destinationOf(m + guard, guardWord);
	std::vector<std::uint64_t> positionOf(n + guard, guardWord);
	std::uint64_t pending = guardWord;
	std::int64_t const result = emission_pop(
		m,
		n,
		data.data(),
		target.data(),
		dest.data(),
		spilled.data(),
		count,
		ops.data(),
		destinationOf.data(),
		positionOf.data(),
		&pending
	);
	if (std::memcmp(data.data(), before.data(), data.size() * sizeof(Slot)) != 0)
		return "<port wrote data>";
	if (!intact(ops, count, guardOp) || !intact(destinationOf, m, guardWord) || !intact(positionOf, n, guardWord))
		return "<port wrote past a buffer>";
	if (result == -2)
		return "err";
	if (result != static_cast<std::int64_t>(count) || count > m)
		return "<port result " + std::to_string(result) + ">";
	std::size_t const size = m - count;
	if (!intact(destinationOf, size, guardWord))
		return "<port wrote a destination above the stack>";
	data.resize(size);
	ops.resize(count);
	std::vector<std::string> dests;
	for (std::size_t i = 0; i < size; ++i)
		dests.push_back(showOffset(destinationOf[i]));
	std::vector<std::string> sources;
	for (std::size_t j = 0; j < n; ++j)
		sources.push_back(showOffset(positionOf[j]));
	return "ok;" + showStack(data) + ";" + showOps(ops) + ";" + join(dests) + ";" + join(sources) + ";" +
		std::to_string(pending);
}

/// A case "spill;" adds ";" queries. The spill set has one byte for each variable id up to the largest id of the
/// case, and starts empty.
/// The result is "ok", the spilled ids in ascending order and per query 1 if it is spilled, else 0; or "err".
std::string runSpill(std::vector<std::string> const& _fields)
{
	if (_fields.size() != 2)
		throw std::invalid_argument("not a spill case");
	std::vector<Slot> const adds = parseStack(_fields[0]);
	std::vector<Slot> const queries = parseStack(_fields[1]);
	std::size_t const idCount = parseSpilled("", adds, queries).size();

	// spill_set writes at most idCount bytes of spilled and queryCount results. A guard area after each buffer must
	// stay as it is.
	std::vector<std::uint8_t> spilled(idCount + guard, guardByte);
	std::fill_n(spilled.begin(), idCount, 0);
	std::vector<std::uint8_t> results(queries.size() + guard, guardByte);
	std::int64_t const result =
		spill_set(idCount, spilled.data(), adds.data(), adds.size(), queries.data(), queries.size(), results.data());
	if (!intact(spilled, idCount, guardByte) || !intact(results, queries.size(), guardByte))
		return "<port wrote past a buffer>";
	if (result == -2)
		return "err";
	if (result != 0)
		return "<port result " + std::to_string(result) + ">";
	// add writes 1, and isSpilled gives a bool
	std::vector<std::string> ids;
	for (std::size_t id = 0; id < idCount; ++id)
		if (spilled[id] == 1)
			ids.push_back(std::to_string(id));
		else if (spilled[id] != 0)
			return "<port spilled byte " + std::to_string(spilled[id]) + ">";
	std::vector<std::string> bits;
	for (std::size_t i = 0; i < queries.size(); ++i)
		if (results[i] > 1)
			return "<port query result " + std::to_string(results[i]) + ">";
		else
			bits.push_back(std::to_string(results[i]));
	return "ok;" + join(ids) + ";" + join(bits);
}

std::string identity(std::string const& _model)
{
	return _model;
}

/// A unit of the port
struct Unit
{
	/// The kind of its cases, the first field of a case line
	std::string_view kind;
	/// Its result on the fields of a case after the kind
	std::string (*run)(std::vector<std::string> const&);
	/// The part of a model result that it gives
	std::string (*view)(std::string const&);
};

/// The units of the port. A kind without an entry is checked against solc only.
Unit constexpr units[] = {
	// the C interface does not give the destinations
	{"bottomup", runBuildBottomUp, withoutLastField},
	{"pop", runPop, identity},
	{"spill", runSpill, identity},
};

}

std::optional<port::Check> port::check(std::string const& _line, std::string const& _model)
{
	std::vector<std::string> fields = split(_line, ';');
	for (Unit const& unit: units)
		if (!fields.empty() && fields[0] == unit.kind)
		{
			fields.erase(fields.begin());
			return Check{unit.run(fields), unit.view(_model)};
		}
	return std::nullopt;
}
