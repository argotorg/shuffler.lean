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

/// StackSlot of kraken/c/shuffler/StackSlot.h
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

/// ShuffleOp of kraken/c/shuffler/ShuffleTrace.h
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

extern "C" std::int64_t remove_surplus(
	std::uint64_t m,
	std::uint64_t n,
	Slot* data,
	Slot const* target,
	std::uint64_t* dest,
	std::uint8_t const* spilled,
	std::uint64_t idCount,
	Op* ops,
	std::uint64_t* blocked,
	std::uint64_t* height
);

extern "C" std::int64_t permute(
	std::uint64_t h,
	Slot* data,
	std::uint64_t const* perm,
	Op* ops,
	std::uint64_t* blocked,
	std::uint64_t* dest
);

extern "C" std::int64_t permute_at_lowest_height(
	std::uint64_t m,
	std::uint64_t n,
	Slot* data,
	Slot const* target,
	std::uint64_t* dest,
	std::uint8_t const* spilled,
	std::uint64_t idCount,
	Op* ops,
	std::uint64_t* blocked
);

extern "C" std::int64_t build_mapping(
	std::uint64_t m,
	std::uint64_t n,
	Slot const* source,
	Slot const* target,
	std::uint8_t const* dropped,
	std::uint8_t strategy,
	std::uint64_t* sources,
	std::uint8_t* saw
);

extern "C" std::int64_t resolve(
	std::uint64_t m,
	std::uint64_t n,
	Slot const* source,
	Slot const* target,
	std::uint64_t const* plan,
	std::uint64_t h,
	std::uint64_t const* current,
	std::uint64_t offset,
	std::uint64_t excess,
	std::uint8_t* spilled,
	std::uint64_t idCount,
	std::uint8_t allowed,
	std::uint8_t* dropped
);

extern "C" std::int64_t emit(
	std::uint64_t m,
	std::uint64_t n,
	Slot* data,
	Slot const* target,
	std::uint64_t* dest,
	std::uint8_t const* spilled,
	std::uint64_t idCount,
	Op* ops,
	std::uint64_t* blocked,
	std::uint64_t* height
);

extern "C" std::int64_t plan(
	std::uint64_t m,
	std::uint64_t n,
	Slot const* source,
	Slot const* target,
	std::uint8_t* spilled,
	std::uint64_t idCount,
	std::uint8_t allowed,
	std::uint8_t strategy,
	std::uint8_t* dropped,
	std::uint8_t* saw,
	Slot* data,
	Op* ops,
	std::uint64_t* sources
);

namespace
{

/// The maximal stack size of build_bottom_up (the EVM stack limit)
std::size_t constexpr maxStackSize = 1024;

/// The none of an Optional<StackOffset> of kraken/c/shuffler/Freestanding.h
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

/// The status of a state result from the blocked output of the port: "ok" is 0 and 0, a block has a positive excess
std::string showStatus(std::uint64_t const (&_blocked)[2])
{
	return _blocked[1] != 0 ? "blocked " + std::to_string(_blocked[0]) + " " + std::to_string(_blocked[1]) :
		_blocked[0] == 0 ? "ok" :
		"<port blocked " + std::to_string(_blocked[0]) + " 0>";
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
	return showStatus(blocked) + ";" + showStack(data) + ";" + showOps(ops);
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

/// A case "surplus;" stack ";" target ";" dests ";" vars, in the domain of remove_surplus: the destinations are
/// distinct and below the target size, or "-", and the stack and the target have at most maxStackSize slots.
/// The result is "ok" or "blocked OFFSET EXCESS", the final stack, the operations and the destinations; or "err".
std::string runSurplus(std::vector<std::string> const& _fields)
{
	if (_fields.size() != 4)
		throw std::invalid_argument("not a state");
	std::vector<Slot> const source = parseStack(_fields[0]);
	std::vector<Slot> const target = parseStack(_fields[1]);
	std::size_t const m = source.size();
	std::size_t const n = target.size();
	if (m > maxStackSize || n > maxStackSize)
		throw std::invalid_argument("more slots than the stack limit");
	std::vector<std::uint64_t> const dest = parseDests(_fields[2], m, n);
	std::vector<std::uint8_t> const spilled = parseSpilled(_fields[3], source, target);

	// remove_surplus writes at most m slots, 2 m operations and m destinations. A guard area after each buffer must
	// stay as it is.
	std::vector<Slot> data(m + guard, guardSlot);
	std::copy(source.begin(), source.end(), data.begin());
	std::vector<Op> ops(2 * m + guard, guardOp);
	std::vector<std::uint64_t> destinationOf(m + guard, guardWord);
	std::copy(dest.begin(), dest.end(), destinationOf.begin());
	std::uint64_t blocked[2] = {0xeeee, 0xeeee};
	std::uint64_t height = guardWord;
	std::int64_t const count = remove_surplus(
		m,
		n,
		data.data(),
		target.data(),
		destinationOf.data(),
		spilled.data(),
		spilled.size(),
		ops.data(),
		blocked,
		&height
	);
	if (!intact(data, m, guardSlot) || !intact(ops, 2 * m, guardOp) || !intact(destinationOf, m, guardWord))
		return "<port wrote past a buffer>";
	if (count == -2)
		return "err";
	if (count < 0 || static_cast<std::uint64_t>(count) > 2 * m)
		return "<port result " + std::to_string(count) + ">";
	if (height > m)
		return "<port height " + std::to_string(height) + ">";
	auto const above = static_cast<std::ptrdiff_t>(height);
	if (!std::equal(destinationOf.begin() + above, destinationOf.begin() + static_cast<std::ptrdiff_t>(m),
			dest.begin() + above))
		return "<port wrote a destination above the stack>";
	data.resize(height);
	ops.resize(static_cast<std::size_t>(count));
	std::vector<std::string> dests;
	for (std::size_t i = 0; i < height; ++i)
		dests.push_back(showOffset(destinationOf[i]));
	return showStatus(blocked) + ";" + showStack(data) + ";" + showOps(ops) + ";" + join(dests);
}

/// A case "permute;" stack ";" dests, in the domain of permute: the destinations are a permutation of the stack
/// offsets, and the stack has at most maxStackSize slots.
/// The result is "ok" or "blocked OFFSET EXCESS", the final stack, the operations and the destinations; or "err".
std::string runPermute(std::vector<std::string> const& _fields)
{
	if (_fields.size() != 2)
		throw std::invalid_argument("not a permute case");
	std::vector<Slot> const source = parseStack(_fields[0]);
	std::size_t const h = source.size();
	if (h > maxStackSize)
		throw std::invalid_argument("more slots than the stack limit");
	std::vector<std::uint64_t> const perm = parseDests(_fields[1], h, h);
	if (std::find(perm.begin(), perm.end(), none) != perm.end())
		throw std::invalid_argument("not a permutation: " + _fields[1]);

	// permute does not write perm, and writes at most h slots, 2 h operations and h destinations. A guard area after
	// each buffer must stay as it is.
	std::vector<Slot> data(h + guard, guardSlot);
	std::copy(source.begin(), source.end(), data.begin());
	std::vector<std::uint64_t> permutation(h + guard, guardWord);
	std::copy(perm.begin(), perm.end(), permutation.begin());
	std::vector<std::uint64_t> const before = permutation;
	std::vector<Op> ops(2 * h + guard, guardOp);
	std::vector<std::uint64_t> dest(h + guard, guardWord);
	std::uint64_t blocked[2] = {0xeeee, 0xeeee};
	std::int64_t const count = permute(h, data.data(), permutation.data(), ops.data(), blocked, dest.data());
	if (permutation != before)
		return "<port wrote perm>";
	if (!intact(data, h, guardSlot) || !intact(ops, 2 * h, guardOp) || !intact(dest, h, guardWord))
		return "<port wrote past a buffer>";
	if (count == -2)
		return "err";
	if (count < 0 || static_cast<std::uint64_t>(count) > 2 * h)
		return "<port result " + std::to_string(count) + ">";
	data.resize(h);
	ops.resize(static_cast<std::size_t>(count));
	std::vector<std::string> dests;
	for (std::size_t i = 0; i < h; ++i)
		dests.push_back(showOffset(dest[i]));
	return showStatus(blocked) + ";" + showStack(data) + ";" + showOps(ops) + ";" + join(dests);
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

/// A case "lowest;" stack ";" target ";" dests ";" vars, in the domain of permute_at_lowest_height: the destinations
/// are distinct and below the target size, or "-", and the stack and the target have at most maxStackSize slots.
/// The result is "ok" or "blocked OFFSET EXCESS", the final stack, the operations and the destinations; or "err".
std::string runLowest(std::vector<std::string> const& _fields)
{
	if (_fields.size() != 4)
		throw std::invalid_argument("not a state");
	std::vector<Slot> const source = parseStack(_fields[0]);
	std::vector<Slot> const target = parseStack(_fields[1]);
	std::size_t const m = source.size();
	std::size_t const n = target.size();
	if (m > maxStackSize || n > maxStackSize)
		throw std::invalid_argument("more slots than the stack limit");
	std::vector<std::uint64_t> const dest = parseDests(_fields[2], m, n);
	std::vector<std::uint8_t> const spilled = parseSpilled(_fields[3], source, target);

	// permute_at_lowest_height writes at most m slots, 2 m operations and m destinations. A guard area after each
	// buffer must stay as it is.
	std::vector<Slot> data(m + guard, guardSlot);
	std::copy(source.begin(), source.end(), data.begin());
	std::vector<Op> ops(2 * m + guard, guardOp);
	std::vector<std::uint64_t> destinationOf(m + guard, guardWord);
	std::copy(dest.begin(), dest.end(), destinationOf.begin());
	std::uint64_t blocked[2] = {0xeeee, 0xeeee};
	std::int64_t const count = permute_at_lowest_height(
		m,
		n,
		data.data(),
		target.data(),
		destinationOf.data(),
		spilled.data(),
		spilled.size(),
		ops.data(),
		blocked
	);
	if (!intact(data, m, guardSlot) || !intact(ops, 2 * m, guardOp) || !intact(destinationOf, m, guardWord))
		return "<port wrote past a buffer>";
	if (count == -2)
		return "err";
	if (count < 0 || static_cast<std::uint64_t>(count) > 2 * m)
		return "<port result " + std::to_string(count) + ">";
	data.resize(m);
	ops.resize(static_cast<std::size_t>(count));
	std::vector<std::string> dests;
	for (std::size_t i = 0; i < m; ++i)
		dests.push_back(showOffset(destinationOf[i]));
	return showStatus(blocked) + ";" + showStack(data) + ";" + showOps(ops) + ";" + join(dests);
}

/// A case "map;" strategy ";" source ";" target ";" dropped, in the domain of build_mapping: the strategy is "L"
/// (Leave) or "T" (Take), dropped has one byte (at most 255) for each source slot, and the source and the target have
/// at most maxStackSize slots.
/// The result is "ok", sawWildcardCopy (0 or 1) and per target offset the position of the source slot bound for it;
/// or "err".
std::string runMap(std::vector<std::string> const& _fields)
{
	if (_fields.size() != 4)
		throw std::invalid_argument("not a map case");
	if (_fields[0] != "L" && _fields[0] != "T")
		throw std::invalid_argument("not a strategy: " + _fields[0]);
	std::uint8_t const strategy = _fields[0] == "T";
	std::vector<Slot> const source = parseStack(_fields[1]);
	std::vector<Slot> const target = parseStack(_fields[2]);
	std::size_t const m = source.size();
	std::size_t const n = target.size();
	if (m > maxStackSize || n > maxStackSize)
		throw std::invalid_argument("more slots than the stack limit");
	std::vector<std::uint8_t> dropped;
	for (std::string const& word: words(_fields[3]))
	{
		// the length bound keeps parseNat from overflowing
		if (word.size() > 3 || parseNat(word) > 255)
			throw std::invalid_argument("not a byte: " + word);
		dropped.push_back(static_cast<std::uint8_t>(parseNat(word)));
	}
	if (dropped.size() != m)
		throw std::invalid_argument("not one dropped byte per source slot: " + _fields[3]);

	// build_mapping writes at most n positions and one byte. A guard area after each buffer must stay as it is.
	std::vector<std::uint64_t> sources(n + guard, guardWord);
	std::vector<std::uint8_t> saw(1 + guard, guardByte);
	std::int64_t const result = build_mapping(
		m,
		n,
		source.data(),
		target.data(),
		dropped.data(),
		strategy,
		sources.data(),
		saw.data()
	);
	if (!intact(sources, n, guardWord) || !intact(saw, 1, guardByte))
		return "<port wrote past a buffer>";
	if (result == -2)
		return "err";
	if (result != 0)
		return "<port result " + std::to_string(result) + ">";
	if (saw[0] > 1)
		return "<port saw " + std::to_string(saw[0]) + ">";
	std::vector<std::string> positions;
	for (std::size_t j = 0; j < n; ++j)
		positions.push_back(showOffset(sources[j]));
	return "ok " + std::to_string(saw[0]) + ";" + join(positions);
}

/// A case "resolve;" bit ";" source ";" target ";" vars ";" dropped ";" plan ";" current ";" offset " " excess, in
/// the domain of resolve: the bit is spillingAllowed, dropped has one byte (at most 255) for each source slot, plan
/// has a destination for each source slot and current one for each slot of the working stack, the destinations of
/// each are distinct and below the target size, or "-", the source, the target and the working stack have at most
/// maxStackSize slots, and the offset is below the size of the working stack.
/// The result is "ok", success (0 or 1), the spilled variables, ascending, and dropped; or "err".
std::string runResolve(std::vector<std::string> const& _fields)
{
	if (_fields.size() != 8)
		throw std::invalid_argument("not a resolve case");
	if (_fields[0] != "0" && _fields[0] != "1")
		throw std::invalid_argument("not a bit: " + _fields[0]);
	std::uint8_t const allowed = _fields[0] == "1";
	std::vector<Slot> const source = parseStack(_fields[1]);
	std::vector<Slot> const target = parseStack(_fields[2]);
	std::size_t const m = source.size();
	std::size_t const n = target.size();
	std::vector<std::string> const currentWords = words(_fields[6]);
	std::size_t const h = currentWords.size();
	if (m > maxStackSize || n > maxStackSize || h > maxStackSize)
		throw std::invalid_argument("more slots than the stack limit");
	std::vector<std::uint8_t> const spills = parseSpilled(_fields[3], source, target);
	std::size_t const idCount = spills.size();
	std::vector<std::uint8_t> bytes;
	for (std::string const& word: words(_fields[4]))
	{
		// the length bound keeps parseNat from overflowing
		if (word.size() > 3 || parseNat(word) > 255)
			throw std::invalid_argument("not a byte: " + word);
		bytes.push_back(static_cast<std::uint8_t>(parseNat(word)));
	}
	if (bytes.size() != m)
		throw std::invalid_argument("not one dropped byte per source slot: " + _fields[4]);
	std::vector<std::uint64_t> const plan = parseDests(_fields[5], m, n);
	std::vector<std::uint64_t> const current = parseDests(_fields[6], h, n);
	std::vector<std::string> const blocked = words(_fields[7]);
	if (blocked.size() != 2)
		throw std::invalid_argument("not an offset and an excess: " + _fields[7]);
	std::size_t const offset = parseNat(blocked[0]);
	std::size_t const excess = parseNat(blocked[1]);
	if (offset >= h)
		throw std::invalid_argument("the blocked offset is not below the working stack size: " + _fields[7]);

	// resolve writes at most idCount bytes of spilled and m bytes of dropped. A guard area after each buffer must
	// stay as it is.
	std::vector<std::uint8_t> spilled(idCount + guard, guardByte);
	std::copy(spills.begin(), spills.end(), spilled.begin());
	std::vector<std::uint8_t> dropped(m + guard, guardByte);
	std::copy(bytes.begin(), bytes.end(), dropped.begin());
	std::int64_t const result = resolve(
		m,
		n,
		source.data(),
		target.data(),
		plan.data(),
		h,
		current.data(),
		offset,
		excess,
		spilled.data(),
		idCount,
		allowed,
		dropped.data()
	);
	if (!intact(spilled, idCount, guardByte) || !intact(dropped, m, guardByte))
		return "<port wrote past a buffer>";
	if (result == -2)
		return "err";
	if (result != 0 && result != -1)
		return "<port result " + std::to_string(result) + ">";
	// add writes 1
	std::vector<std::string> ids;
	for (std::size_t id = 0; id < idCount; ++id)
		if (spilled[id] == 1)
			ids.push_back(std::to_string(id));
		else if (spilled[id] != 0)
			return "<port spilled byte " + std::to_string(spilled[id]) + ">";
	std::vector<std::string> droppedWords;
	for (std::size_t i = 0; i < m; ++i)
		droppedWords.push_back(std::to_string(dropped[i]));
	return std::string{"ok "} + (result == 0 ? "1" : "0") + ";" + join(ids) + ";" + join(droppedWords);
}

/// A case "emit;" stack ";" target ";" dests ";" vars, in the domain of emit: the destinations are distinct and below
/// the target size, or "-", and the stack and the target have at most maxStackSize slots.
/// The result is "ok" or "blocked OFFSET EXCESS", the final stack, the operations and the destinations; or "err".
std::string runEmit(std::vector<std::string> const& _fields)
{
	if (_fields.size() != 4)
		throw std::invalid_argument("not a state");
	std::vector<Slot> const source = parseStack(_fields[0]);
	std::vector<Slot> const target = parseStack(_fields[1]);
	std::size_t const m = source.size();
	std::size_t const n = target.size();
	if (m > maxStackSize || n > maxStackSize)
		throw std::invalid_argument("more slots than the stack limit");
	std::vector<std::uint64_t> const dest = parseDests(_fields[2], m, n);
	std::vector<std::uint8_t> const spilled = parseSpilled(_fields[3], source, target);

	// emit writes at most max(m, n) slots and destinations, and at most 2m + 6n operations into a buffer of 4m + 6n
	// (see kraken/c/shuffler/test_wrappers.cpp). A guard area after each buffer must stay as it is.
	std::size_t const room = std::max(m, n);
	std::size_t const opsRoom = 4 * m + 6 * n;
	std::vector<Slot> data(room + guard, guardSlot);
	std::copy(source.begin(), source.end(), data.begin());
	std::vector<Op> ops(opsRoom + guard, guardOp);
	std::vector<std::uint64_t> destinationOf(room + guard, guardWord);
	std::copy(dest.begin(), dest.end(), destinationOf.begin());
	std::vector<std::uint64_t> const destinationsBefore = destinationOf;
	std::uint64_t blocked[2] = {0xeeee, 0xeeee};
	std::uint64_t height = guardWord;
	std::int64_t const count = emit(
		m,
		n,
		data.data(),
		target.data(),
		destinationOf.data(),
		spilled.data(),
		spilled.size(),
		ops.data(),
		blocked,
		&height
	);
	if (!intact(data, room, guardSlot) || !intact(ops, opsRoom, guardOp) || !intact(destinationOf, room, guardWord))
		return "<port wrote past a buffer>";
	if (count == -2)
		return "err";
	if (count < 0 || static_cast<std::uint64_t>(count) > 2 * m + 6 * n)
		return "<port result " + std::to_string(count) + ">";
	if (height > room)
		return "<port height " + std::to_string(height) + ">";
	auto const above = static_cast<std::ptrdiff_t>(height);
	if (!std::equal(destinationOf.begin() + above, destinationOf.end(), destinationsBefore.begin() + above))
		return "<port wrote a destination above the stack>";
	data.resize(height);
	ops.resize(static_cast<std::size_t>(count));
	std::vector<std::string> dests;
	for (std::size_t i = 0; i < height; ++i)
		dests.push_back(showOffset(destinationOf[i]));
	return showStatus(blocked) + ";" + showStack(data) + ";" + showOps(ops) + ";" + join(dests);
}

/// A case "plan;" strategy ";" bit ";" source ";" target ";" vars, in the domain of plan: the strategy is L (Leave) or
/// T (Take), the bit is spillingAllowed, and the source and the target have at most maxStackSize slots.
/// The result is "ok", success (0 or 1), sawWildcardCopy (0 or 1), the spilled variables, ascending, and dropped; after
/// a success also the final stack, the operations and the source offset of each target slot; or "err".
std::string runPlan(std::vector<std::string> const& _fields)
{
	if (_fields.size() != 5)
		throw std::invalid_argument("not a plan case");
	if (_fields[0] != "L" && _fields[0] != "T")
		throw std::invalid_argument("not a strategy: " + _fields[0]);
	if (_fields[1] != "0" && _fields[1] != "1")
		throw std::invalid_argument("not a bit: " + _fields[1]);
	std::uint8_t const strategy = _fields[0] == "T";
	std::uint8_t const allowed = _fields[1] == "1";
	std::vector<Slot> const source = parseStack(_fields[2]);
	std::vector<Slot> const target = parseStack(_fields[3]);
	std::size_t const m = source.size();
	std::size_t const n = target.size();
	if (m > maxStackSize || n > maxStackSize)
		throw std::invalid_argument("more slots than the stack limit");
	std::vector<std::uint8_t> const spills = parseSpilled(_fields[4], source, target);
	std::size_t const idCount = spills.size();

	// plan writes at most idCount bytes of spilled, m of dropped, one of saw, max(m, n) slots, 2m + 6n operations
	// into a buffer of 4m + 6n, and n source offsets (see kraken/c/shuffler/test_wrappers.cpp). A guard area after each
	// buffer must stay as it is.
	std::size_t const room = std::max(m, n);
	std::size_t const opsRoom = 4 * m + 6 * n;
	std::vector<std::uint8_t> spilled(idCount + guard, guardByte);
	std::copy(spills.begin(), spills.end(), spilled.begin());
	std::vector<std::uint8_t> dropped(m + guard, guardByte);
	std::vector<std::uint8_t> saw(1 + guard, guardByte);
	std::vector<Slot> data(room + guard, guardSlot);
	std::vector<Op> ops(opsRoom + guard, guardOp);
	std::vector<std::uint64_t> sources(n + guard, guardWord);
	std::int64_t const count = plan(
		m,
		n,
		source.data(),
		target.data(),
		spilled.data(),
		idCount,
		allowed,
		strategy,
		dropped.data(),
		saw.data(),
		data.data(),
		ops.data(),
		sources.data()
	);
	if (!intact(spilled, idCount, guardByte) || !intact(dropped, m, guardByte) || !intact(saw, 1, guardByte) ||
		!intact(data, room, guardSlot) || !intact(ops, opsRoom, guardOp) || !intact(sources, n, guardWord))
		return "<port wrote past a buffer>";
	if (count == -2)
		return intact(saw, 0, guardByte) && intact(sources, 0, guardWord) ? "err" : "<port wrote saw or sources>";
	if (count < -1 || count > static_cast<std::int64_t>(2 * m + 6 * n))
		return "<port result " + std::to_string(count) + ">";
	if (count == -1 && !intact(sources, 0, guardWord))
		return "<port wrote sources>";
	if (saw[0] > 1)
		return "<port saw byte " + std::to_string(saw[0]) + ">";
	// add writes 1
	std::vector<std::string> ids;
	for (std::size_t id = 0; id < idCount; ++id)
		if (spilled[id] == 1)
			ids.push_back(std::to_string(id));
		else if (spilled[id] != 0)
			return "<port spilled byte " + std::to_string(spilled[id]) + ">";
	std::vector<std::string> droppedWords;
	for (std::size_t i = 0; i < m; ++i)
		droppedWords.push_back(std::to_string(dropped[i]));
	std::string const head = std::string{"ok "} + (count >= 0 ? "1" : "0") + ";" + std::to_string(saw[0]) + ";" +
		join(ids) + ";" + join(droppedWords);
	if (count == -1)
		return head;
	data.resize(n);
	ops.resize(static_cast<std::size_t>(count));
	std::vector<std::string> offsets;
	for (std::size_t j = 0; j < n; ++j)
		offsets.push_back(showOffset(sources[j]));
	return head + ";" + showStack(data) + ";" + showOps(ops) + ";" + join(offsets);
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
	{"surplus", runSurplus, identity},
	{"permute", runPermute, identity},
	{"lowest", runLowest, identity},
	{"map", runMap, identity},
	{"resolve", runResolve, identity},
	{"emit", runEmit, identity},
	{"plan", runPlan, identity},
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
