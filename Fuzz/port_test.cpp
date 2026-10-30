// Tests of Fuzz/port.cpp: the port against fixed model results, the part of the model result that the port gives,
// and the cases that are not in the domain of a unit. Each model result is the output of Fuzz/Oracle.lean
// (`runLine`) on the case, at origin/pr31 1da7ff5.

#include "port.h"

#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace
{

int failures = 0;

void expect(bool const _ok, std::string const& _what)
{
	if (!_ok)
	{
		std::cerr << "FAIL: " << _what.substr(0, 300) << '\n';
		++failures;
	}
}

/// The port result and the model result without its destinations are equal, and equal to `_view`
void agrees(std::string const& _line, std::string const& _model, std::string const& _view)
{
	std::optional<port::Check> const check = port::check(_line, _model);
	expect(check.has_value(), "a port unit for: " + _line);
	if (!check)
		return;
	expect(check->model == _view, "model view of " + _line + ": " + check->model);
	expect(check->port == check->model, "port of " + _line + ": " + check->port + " != " + check->model);
}

void throws(std::string const& _line)
{
	try
	{
		port::check(_line, "ok;;;");
		expect(false, "invalid_argument for: " + _line);
	}
	catch (std::invalid_argument const&)
	{
	}
}

std::string vars(int const _from, int const _to)
{
	std::string result;
	for (int i = _from; i <= _to; ++i)
		result += (i > _from ? " v" : "v") + std::to_string(i);
	return result;
}

std::string nats(int const _from, int const _to, int const _step = 1)
{
	std::string result;
	for (int i = _from; _step > 0 ? i <= _to : i >= _to; i += _step)
		result += (i != _from ? " " : "") + std::to_string(i);
	return result;
}

/// `_word` `_count` times, separated by spaces
std::string times(std::string const& _word, int const _count)
{
	std::string result;
	for (int i = 0; i < _count; ++i)
		result += (i > 0 ? " " : "") + _word;
	return result;
}

}

int main()
{
	// the kinds without a port unit
	for (std::string const line: {"map;L;v0;v0;0", "plan;L;0;;;"})
		expect(!port::check(line, "ok;;;").has_value(), "no port unit for: " + line);

	// buildBottomUp: each slot kind, each operation kind, equal slots, blocked with and without operations
	agrees("bottomup;;;;", "ok;;;", "ok;;");
	agrees("bottomup;v0 v1;v1 v0;1 0;", "ok;v1 v0;SWAP1;0 1", "ok;v1 v0;SWAP1");
	agrees("bottomup;v0;v0 v0;0;", "ok;v0 v0;DUP1;0 1", "ok;v0 v0;DUP1");
	agrees("bottomup;;l1 _;;", "ok;l1 _;PUSH:l1 PUSH:_;0 1", "ok;l1 _;PUSH:l1 PUSH:_");
	agrees("bottomup;;v3;;3", "ok;v3;LOAD:v3;0", "ok;v3;LOAD:v3");
	agrees("bottomup;;v1000 l7;;1000", "ok;v1000 l7;LOAD:v1000 PUSH:l7;0 1", "ok;v1000 l7;LOAD:v1000 PUSH:l7");
	agrees("bottomup;R _ l2 v5;R _ l2 v5;0 1 2 3;", "ok;R _ l2 v5;;0 1 2 3", "ok;R _ l2 v5;");
	agrees("bottomup;_ R;R _;1 0;", "ok;R _;SWAP1;0 1", "ok;R _;SWAP1");
	agrees("bottomup;v2 v2;v2 v2;1 0;", "ok;v2 v2;;1 0", "ok;v2 v2;");
	agrees("bottomup;v0 v0 v1;v1 v0 v0;1 2 0;", "ok;v1 v0 v0;SWAP2;0 2 1", "ok;v1 v0 v0;SWAP2");
	agrees("bottomup;l0 v1;v1 v1 l0;2 0;", "ok;v1 v1 l0;SWAP1 DUP2 SWAP1;0 1 2", "ok;v1 v1 l0;SWAP1 DUP2 SWAP1");
	agrees(
		"bottomup;l0 " + vars(1, 15) + ";" + vars(1, 15) + " v1 l0;16 " + nats(0, 14) + ";",
		"ok;" + vars(1, 15) + " v1 l0;SWAP14 SWAP15 DUP16 SWAP1 SWAP2 SWAP3 SWAP4 SWAP5 SWAP6 SWAP7 SWAP8 SWAP9 SWAP10 "
			"SWAP11 SWAP12 SWAP13 SWAP14 SWAP15 SWAP2;" + nats(0, 16),
		"ok;" + vars(1, 15) + " v1 l0;SWAP14 SWAP15 DUP16 SWAP1 SWAP2 SWAP3 SWAP4 SWAP5 SWAP6 SWAP7 SWAP8 SWAP9 SWAP10 "
			"SWAP11 SWAP12 SWAP13 SWAP14 SWAP15 SWAP2"
	);
	// 18 distinct slots in the reverse order: the bottom is out of swap reach
	std::string const reversed = vars(0, 17) + ";" + "v17 v16 v15 v14 v13 v12 v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0";
	agrees(
		"bottomup;" + reversed + ";" + nats(17, 0, -1) + ";",
		"blocked 0 1;" + vars(0, 17) + ";;" + nats(17, 0, -1),
		"blocked 0 1;" + vars(0, 17) + ";"
	);
	// a swap, then the bottom is out of swap reach
	agrees(
		"bottomup;" + vars(0, 17) + ";v1 v0 " + vars(2, 17) + ";1 0 " + nats(2, 17) + ";",
		"blocked 0 1;v0 v17 " + vars(2, 16) + " v1;SWAP16;1 17 " + nats(2, 16) + " 0",
		"blocked 0 1;v0 v17 " + vars(2, 16) + " v1;SWAP16"
	);
	agrees(
		"bottomup;l0 " + vars(1, 16) + ";" + vars(1, 16) + " v1 l0;17 " + nats(0, 15) + ";",
		"blocked 0 1;v1 v16 " + vars(2, 15) + " l0;SWAP15 SWAP16;0 15 " + nats(1, 14) + " 17",
		"blocked 0 1;v1 v16 " + vars(2, 15) + " l0;SWAP15 SWAP16"
	);

	// an assertion of the port is "err" (here: the DUP of a return label), and the view keeps a model "err"
	agrees("bottomup;R;R R;0;", "err", "err");
	// a state that is not Valid (the return label of the target is not bound): the model has no result, the port
	// asserts, and the check sees the difference
	{
		std::optional<port::Check> const check = port::check("bottomup;R;R R;0;", "invalid");
		expect(check && check->port == "err" && check->model == "invalid", "not Valid: port err, model invalid");
	}
	// a wrong model result is not equal to the port result
	{
		std::optional<port::Check> const check = port::check("bottomup;v0 v1;v1 v0;1 0;", "ok;v0 v1;;0 1");
		expect(check && check->port != check->model, "a wrong model result differs");
	}

	// not in the domain of the port unit: a surplus slot, a slot without a destination, a bad slot, a bad
	// destination, too few fields, a destination bound twice, a destination out of the target, more slots than the
	// port's stack limit
	throws("bottomup;v0 v1;v0;0 -;");
	throws("bottomup;v0 v1;v0 v1;0 -;");
	throws("bottomup;x;x;0;");
	throws("bottomup;v0;v0;a;");
	throws("bottomup;v0;v0;0 1;");
	throws("bottomup;;;");
	throws("bottomup;v0 v1;v0 v1;0 0;");
	throws("bottomup;v0;v0;1;");
	throws("bottomup;;;;x");
	{
		std::string target = "_";
		for (int i = 1; i < 1025; ++i)
			target += " _";
		throws("bottomup;;" + target + ";;");
	}

	// State.pop: no pops, a pop of an empty stack, a bound top (its target offset gets no position), an unbound top
	// (no position changes), the pending generations stay, slots without a destination, each slot kind, more slots
	// than target slots, one pop more than the stack size
	agrees("pop;;;;;0", "ok;;;;;0", "ok;;;;;0");
	agrees("pop;;;;;1", "err", "err");
	agrees("pop;;v0 v1;;0 1;0", "ok;;;;- -;2", "ok;;;;- -;2");
	agrees("pop;v0;v0;0;0;1", "ok;;POP;;-;0", "ok;;POP;;-;0");
	agrees("pop;l0;v0;-;0;1", "ok;;POP;;-;1", "ok;;POP;;-;1");
	agrees("pop;v1 v0;v0 v1;1 0;0 1;1", "ok;v1;POP;1;- 0;0", "ok;v1;POP;1;- 0;0");
	agrees("pop;v0 l1 v2;v0 v1 v2;0 - 2;0 1 2;2", "ok;v0;POP POP;0;0 - -;1", "ok;v0;POP POP;0;0 - -;1");
	agrees("pop;v0 v1;v0 v1;0 1;0 1;2", "ok;;POP POP;;- -;0", "ok;;POP POP;;- -;0");
	agrees("pop;v0 v1;v0 v1;0 1;0 1;3", "err", "err");
	agrees("pop;l0 v1;v0 v1;- 1;0 1;0", "ok;l0 v1;;- 1;- 1;1", "ok;l0 v1;;- 1;- 1;1");
	agrees("pop;R _ l2 v5;R _ l2 v5;0 1 2 3;5;2", "ok;R _;POP POP;0 1;0 1 - -;0", "ok;R _;POP POP;0 1;0 1 - -;0");
	agrees("pop;l0 l1 l2;v0;- - -;0;2", "ok;l0;POP POP;-;-;1", "ok;l0;POP POP;-;-;1");
	// the stack limit: 1024 slots, all popped, and one pop more
	{
		std::string const state = "pop;" + vars(0, 1023) + ";" + vars(0, 1023) + ";" + nats(0, 1023) + ";;";
		std::string const result = "ok;;" + times("POP", 1024) + ";;" + times("-", 1024) + ";0";
		agrees(state + "1024", result, result);
		agrees(state + "1025", "err", "err");
	}
	// a wrong model result is not equal to the port result: the position of a popped slot
	{
		std::optional<port::Check> const check = port::check("pop;v0;v0;0;0;1", "ok;;POP;;0;0");
		expect(check && check->port != check->model, "a wrong pop model result differs");
	}

	// not in the domain of the pop unit: too few fields, a bad slot, a bad destination, not one destination per
	// slot, a destination out of the target, a destination bound twice, a bad number of pops, two pops more than
	// the stack size, more stack slots or target slots than the stack limit
	throws("pop;v0;v0;0;0");
	throws("pop;x;v0;0;0;0");
	throws("pop;v0;v0;a;0;0");
	throws("pop;v0;v0;0 -;0;0");
	throws("pop;v0;v0;1;0;0");
	throws("pop;v0 v1;v0 v1;0 0;0 1;0");
	throws("pop;v0;v0;0;0;-1");
	throws("pop;v0;v0;0;0;3");
	throws("pop;;;;;2");
	throws("pop;" + times("_", 1025) + ";;" + times("-", 1025) + ";;0");
	throws("pop;;" + times("_", 1025) + ";;;0");

	// SpillSet: no adds and no queries, an add and its query, the ids in ascending order, a literal, junk and a
	// return label with the payload of a spilled id are not spilled, a query of an id that is not added, a large id
	agrees("spill;;", "ok;;", "ok;;");
	agrees("spill;v0;v0", "ok;0;1", "ok;0;1");
	agrees("spill;v0;", "ok;0;", "ok;0;");
	agrees("spill;;_ R", "ok;;0 0", "ok;;0 0");
	agrees("spill;v2;v0 v1 v2 l2 _ R", "ok;2;0 0 1 0 0 0", "ok;2;0 0 1 0 0 0");
	agrees("spill;v1 v0;v0 v1", "ok;0 1;1 1", "ok;0 1;1 1");
	agrees("spill;v3 v1;l3 l1 v3 v1 v2", "ok;1 3;0 0 1 1 0", "ok;1 3;0 0 1 1 0");
	agrees("spill;;v5 l0", "ok;;0 0", "ok;;0 0");
	agrees("spill;v1000;v1000 v999 l1000", "ok;1000;1 0 0", "ok;1000;1 0 0");
	// an add of a spilled variable, of a literal, of junk and of a return label fails, also after other adds
	agrees("spill;v0 v0;v0", "err", "err");
	agrees("spill;v0 v1 v0;", "err", "err");
	agrees("spill;l0;v0", "err", "err");
	agrees("spill;_;", "err", "err");
	agrees("spill;R;", "err", "err");
	agrees("spill;v0 l1;v0", "err", "err");
	agrees("spill;v0 _ v0;v0", "err", "err");
	// 1024 adds, and a query of one more id
	{
		std::string const result = "ok;" + nats(0, 1023) + ";" + times("1", 1024) + " 0";
		agrees("spill;" + vars(0, 1023) + ";" + vars(0, 1024), result, result);
	}
	// a wrong model result is not equal to the port result: a query result, the spilled ids
	for (std::string const wrong: {"ok;0;0", "ok;;1", "err"})
	{
		std::optional<port::Check> const check = port::check("spill;v0;v0", wrong);
		expect(check && check->port != check->model, "a wrong spill model result differs: " + wrong);
	}

	// not in the domain of the spill unit: too few fields, too many fields, a bad slot
	throws("spill;v0");
	throws("spill;v0;v0;");
	throws("spill;x;");
	throws("spill;;y");

	// removeSurplus: an empty stack, no surplus, a surplus top, a deep surplus (SWAP, then POP), two of them, a
	// surplus slot equal to the top takes over its destination (no operation), also below a surplus slot that is not
	// equal, each slot kind (junk and a return label are not equal to a variable), all slots surplus, more slots
	// than target slots, fewer slots than target slots
	agrees("surplus;;;;", "ok;;;", "ok;;;");
	agrees("surplus;v0 v1;v0 v1;0 1;", "ok;v0 v1;;0 1", "ok;v0 v1;;0 1");
	agrees("surplus;v1 v0;v0 v1;1 0;", "ok;v1 v0;;1 0", "ok;v1 v0;;1 0");
	agrees("surplus;v0 l1;v0;0 -;", "ok;v0;POP;0", "ok;v0;POP;0");
	agrees("surplus;v0 v0;v0;0 -;", "ok;v0;POP;0", "ok;v0;POP;0");
	agrees("surplus;l9 v0 v1;v0 v1;- 0 1;", "ok;v1 v0;SWAP2 POP;1 0", "ok;v1 v0;SWAP2 POP;1 0");
	agrees("surplus;l9 l8 v0 v1;v0 v1;- - 0 1;", "ok;v1 v0;SWAP3 POP SWAP1 POP;1 0",
		"ok;v1 v0;SWAP3 POP SWAP1 POP;1 0");
	agrees("surplus;v0 v0;v0;- 0;", "ok;v0;POP;0", "ok;v0;POP;0");
	agrees("surplus;l5 v0 v0;v0;- - 0;", "ok;v0;POP SWAP1 POP;0", "ok;v0;POP SWAP1 POP;0");
	agrees("surplus;v0 l5 v0;v0;- - 0;", "ok;v0;POP POP;0", "ok;v0;POP POP;0");
	// of two equal surplus slots the shallower one takes the destination; with the deeper one, SWAP1 instead of SWAP2
	agrees("surplus;v0 v0 v1 l1 v0;v0 v1;- - 1 - 0;", "ok;v1 v0;POP POP SWAP2 POP;1 0",
		"ok;v1 v0;POP POP SWAP2 POP;1 0");
	// two retags
	agrees("surplus;v0 l1 v0 l2 v0;v0;- - - - 0;", "ok;v0;POP POP POP POP;0", "ok;v0;POP POP POP POP;0");
	agrees("surplus;R _ v0;v0;- - 0;", "ok;v0;SWAP2 POP POP;0", "ok;v0;SWAP2 POP POP;0");
	agrees("surplus;_ l0 v0 R v0;v0;- - - - 0;", "ok;v0;POP POP SWAP2 POP POP;0", "ok;v0;POP POP SWAP2 POP POP;0");
	agrees("surplus;l0 l1 l2;;- - -;", "ok;;POP POP POP;", "ok;;POP POP POP;");
	agrees("surplus;R _ l2 v5;;- - - -;", "ok;;POP POP POP POP;", "ok;;POP POP POP POP;");
	agrees("surplus;v0 v1 l0 _ R;v0 v1;0 1 - - -;", "ok;v0 v1;POP POP POP;0 1", "ok;v0 v1;POP POP POP;0 1");
	agrees("surplus;v0;v0;-;", "ok;;POP;", "ok;;POP;");
	agrees("surplus;v0;v0 v1;1;", "ok;v0;;1", "ok;v0;;1");
	// the swap reach: a surplus slot at depth 16 is swapped, one at depth 17 blocks, also after a pop; the block is at
	// the shallowest surplus slot; the excess of depth 20; a surplus slot at depth 16 and one below it; a surplus slot
	// at depth 18 that is equal to the top takes over its destination
	{
		std::string const result = "ok;v16 " + vars(1, 15) + ";SWAP16 POP;15 " + nats(0, 14);
		agrees("surplus;l0 " + vars(1, 16) + ";" + vars(1, 16) + ";- " + nats(0, 15) + ";", result, result);
	}
	{
		std::string const result = "blocked 0 1;l0 " + vars(1, 17) + ";;- " + nats(0, 16);
		agrees("surplus;l0 " + vars(1, 17) + ";" + vars(1, 17) + ";- " + nats(0, 16) + ";", result, result);
	}
	{
		std::string const result = "blocked 0 1;l0 " + vars(1, 17) + ";POP;- " + nats(0, 16);
		agrees("surplus;l0 " + vars(1, 17) + " l1;" + vars(1, 17) + ";- " + nats(0, 16) + " -;", result, result);
	}
	{
		std::string const result = "blocked 1 1;l0 l1 " + vars(1, 17) + ";;- - " + nats(0, 16);
		agrees("surplus;l0 l1 " + vars(1, 17) + ";" + vars(1, 17) + ";- - " + nats(0, 16) + ";", result, result);
	}
	{
		std::string const result = "blocked 0 4;l0 " + vars(1, 20) + ";;- " + nats(0, 19);
		agrees("surplus;l0 " + vars(1, 20) + ";" + vars(1, 20) + ";- " + nats(0, 19) + ";", result, result);
	}
	{
		std::string const result = "ok;v15 v16 " + vars(1, 14) + ";SWAP16 POP SWAP16 POP;14 15 " + nats(0, 13);
		agrees("surplus;l0 l1 " + vars(1, 16) + ";" + vars(1, 16) + ";- - " + nats(0, 15) + ";", result, result);
	}
	{
		std::string const result = "ok;v16 " + vars(1, 15) + ";POP SWAP16 POP;15 " + nats(0, 14);
		agrees("surplus;l0 " + vars(1, 16) + " l1;" + vars(1, 16) + ";- " + nats(0, 15) + " -;", result, result);
	}
	{
		std::string const result = "ok;" + vars(0, 16) + ";POP POP;" + nats(0, 16);
		agrees("surplus;" + vars(0, 16) + " l0 v0;" + vars(0, 16) + ";- " + nats(1, 16) + " - 0;", result, result);
	}
	// the stack limit: 1024 surplus slots, and a surplus bottom under 1023 slots
	{
		std::string const result = "ok;;" + times("POP", 1024) + ";";
		agrees("surplus;" + times("l0", 1024) + ";;" + times("-", 1024) + ";", result, result);
	}
	{
		std::string const result = "blocked 0 1007;l0 " + vars(1, 1023) + ";;- " + nats(0, 1022);
		agrees("surplus;l0 " + vars(1, 1023) + ";" + vars(1, 1023) + ";- " + nats(0, 1022) + ";", result, result);
	}
	// a wrong model result is not equal to the port result: an operation, a slot, a destination, the status
	for (std::string const wrong: {"ok;v1 v0;SWAP1 POP;1 0", "ok;v0 v1;SWAP2 POP;1 0", "ok;v1 v0;SWAP2 POP;0 1",
			 "ok;v1 v0;SWAP2 POP;1 -", "blocked 0 1;v1 v0;SWAP2 POP;1 0", "err"})
	{
		std::optional<port::Check> const check = port::check("surplus;l9 v0 v1;v0 v1;- 0 1;", wrong);
		expect(check && check->port != check->model, "a wrong surplus model result differs: " + wrong);
	}

	// not in the domain of the surplus unit: too few fields, too many fields, a bad slot, a bad destination, not one
	// destination per slot, a destination out of the target, a destination bound twice, a bad spilled id, more stack
	// slots or target slots than the stack limit
	throws("surplus;v0;v0;0");
	throws("surplus;v0;v0;0;;");
	throws("surplus;x;v0;0;");
	throws("surplus;v0;y;0;");
	throws("surplus;v0;v0;a;");
	throws("surplus;;;;x");
	throws("surplus;v0;v0;0 -;");
	throws("surplus;v0;v0;1;");
	throws("surplus;v0 v1;v0 v1;0 0;");
	throws("surplus;" + times("_", 1025) + ";;" + times("-", 1025) + ";");
	throws("surplus;;" + times("_", 1025) + ";;");

	// permute: an empty stack, one slot, the identity (no operation), a swap with the top, a 3-cycle away from the
	// top (the top is in place), each slot kind. The regroup of equal slots: two equal slots that only exchange
	// their destinations need no operation, and the mapping keeps the destinations. A misplaced slot equal to the
	// top takes over its destination with no operation (a retag): two swaps for a 3-cycle, three for two 2-cycles.
	agrees("permute;;", "ok;;;", "ok;;;");
	agrees("permute;v0;0", "ok;v0;;0", "ok;v0;;0");
	agrees("permute;v0 v1 v2;0 1 2", "ok;v0 v1 v2;;0 1 2", "ok;v0 v1 v2;;0 1 2");
	agrees("permute;v0 v1 v2;2 1 0", "ok;v2 v1 v0;SWAP2;0 1 2", "ok;v2 v1 v0;SWAP2;0 1 2");
	agrees("permute;v0 v1;1 0", "ok;v1 v0;SWAP1;0 1", "ok;v1 v0;SWAP1;0 1");
	agrees("permute;v0 v1 v2 v3;1 2 0 3", "ok;v2 v0 v1 v3;SWAP1 SWAP3 SWAP2 SWAP1;0 1 2 3",
		"ok;v2 v0 v1 v3;SWAP1 SWAP3 SWAP2 SWAP1;0 1 2 3");
	agrees("permute;v0 v1 v2 v3;2 0 1 3", "ok;v1 v2 v0 v3;SWAP1 SWAP2 SWAP3 SWAP1;0 1 2 3",
		"ok;v1 v2 v0 v3;SWAP1 SWAP2 SWAP3 SWAP1;0 1 2 3");
	agrees("permute;R _ l2 v5;3 2 1 0", "ok;v5 l2 _ R;SWAP3 SWAP1 SWAP2 SWAP1;0 1 2 3",
		"ok;v5 l2 _ R;SWAP3 SWAP1 SWAP2 SWAP1;0 1 2 3");
	agrees("permute;v0 l0;1 0", "ok;l0 v0;SWAP1;0 1", "ok;l0 v0;SWAP1;0 1");
	agrees("permute;v0 v0;1 0", "ok;v0 v0;;1 0", "ok;v0 v0;;1 0");
	agrees("permute;v0 v1 v0;2 1 0", "ok;v0 v1 v0;;2 1 0", "ok;v0 v1 v0;;2 1 0");
	agrees("permute;_ _ l0 l0;3 2 1 0", "ok;l0 l0 _ _;SWAP2 SWAP1 SWAP3;1 0 3 2",
		"ok;l0 l0 _ _;SWAP2 SWAP1 SWAP3;1 0 3 2");
	agrees("permute;v0 v1 v0;1 0 2", "ok;v1 v0 v0;SWAP1 SWAP2;0 1 2", "ok;v1 v0 v0;SWAP1 SWAP2;0 1 2");
	agrees("permute;v0 v1 v0 v1;1 0 3 2", "ok;v1 v0 v1 v0;SWAP1 SWAP2 SWAP3;0 1 2 3",
		"ok;v1 v0 v1 v0;SWAP1 SWAP2 SWAP3;0 1 2 3");
	// the swap reach: on 18 slots the top goes to offset 0 at depth 17 and blocks; a slot at depth 17 blocks after a
	// SWAP16; a SWAP16 on 17 slots; two equal slots at depth 16 and 17 need no swap; a 2-cycle in reach on 18
	// slots; the excess of depth 19
	{
		std::string const result = "blocked 0 1;" + vars(0, 17) + ";;17 " + nats(1, 16) + " 0";
		agrees("permute;" + vars(0, 17) + ";17 " + nats(1, 16) + " 0", result, result);
	}
	{
		std::string const result = "blocked 0 1;l0 " + vars(1, 17) + ";;" + nats(1, 17) + " 0";
		agrees("permute;l0 " + vars(1, 17) + ";" + nats(1, 17) + " 0", result, result);
	}
	{
		std::string const result = "blocked 0 1;v0 v17 " + vars(2, 16) + " v1;SWAP16;1 17 " + nats(2, 16) + " 0";
		agrees("permute;" + vars(0, 17) + ";1 0 " + nats(2, 17), result, result);
	}
	{
		std::string const result = "ok;v16 " + vars(1, 15) + " v0;SWAP16;" + nats(0, 16);
		agrees("permute;" + vars(0, 16) + ";16 " + nats(1, 15) + " 0", result, result);
	}
	{
		std::string const result = "ok;v0 " + vars(0, 16) + ";;1 0 " + nats(2, 17);
		agrees("permute;v0 " + vars(0, 16) + ";1 0 " + nats(2, 17), result, result);
	}
	{
		std::string const result = "ok;v0 v2 v1 " + vars(3, 17) + ";SWAP15 SWAP16 SWAP15;" + nats(0, 17);
		agrees("permute;" + vars(0, 17) + ";0 2 1 " + nats(3, 17), result, result);
	}
	{
		std::string const result = "blocked 0 3;" + vars(0, 19) + ";;19 " + nats(1, 18) + " 0";
		agrees("permute;" + vars(0, 19) + ";19 " + nats(1, 18) + " 0", result, result);
	}
	// the stack limit: the identity, the reversal (it blocks at depth 1023), and a SWAP16 on 1024 slots
	{
		std::string const result = "ok;" + vars(0, 1023) + ";;" + nats(0, 1023);
		agrees("permute;" + vars(0, 1023) + ";" + nats(0, 1023), result, result);
	}
	{
		std::string const result = "blocked 0 1007;" + vars(0, 1023) + ";;" + nats(1023, 0, -1);
		agrees("permute;" + vars(0, 1023) + ";" + nats(1023, 0, -1), result, result);
	}
	{
		std::string const result = "ok;" + vars(0, 1006) + " v1023 " + vars(1008, 1022) + " v1007;SWAP16;" +
			nats(0, 1023);
		agrees("permute;" + vars(0, 1023) + ";" + nats(0, 1006) + " 1023 " + nats(1008, 1022) + " 1007", result,
			result);
	}
	// a wrong model result is not equal to the port result: an operation, a slot, a destination, the status
	for (std::string const wrong: {"ok;v1 v0 v0;SWAP2 SWAP1;0 1 2", "ok;v0 v1 v0;SWAP1 SWAP2;0 1 2",
			 "ok;v1 v0 v0;SWAP1 SWAP2;1 0 2", "ok;v1 v0 v0;SWAP1;0 1 2", "blocked 0 1;v1 v0 v0;SWAP1 SWAP2;0 1 2", "err"})
	{
		std::optional<port::Check> const check = port::check("permute;v0 v1 v0;1 0 2", wrong);
		expect(check && check->port != check->model, "a wrong permute model result differs: " + wrong);
	}

	// not in the domain of the permute unit: too few fields, too many fields, a bad slot, a bad destination, not one
	// destination per slot, a destination out of the stack, a destination bound twice, a slot without a destination
	// (not a permutation), more slots than the stack limit
	throws("permute;v0");
	throws("permute;v0;0;");
	throws("permute;x;0");
	throws("permute;v0;a");
	throws("permute;v0 v1;0");
	throws("permute;v0;0 1");
	throws("permute;v0;1");
	throws("permute;v0 v1;0 0");
	throws("permute;v0 v1;0 -");
	throws("permute;" + vars(0, 1024) + ";" + nats(0, 1024));

	// permuteAtLowestHeight: an empty stack, all slots final, a swap, a parked slot (its destination is above the
	// stack) in a hole (an offset that no slot is bound for) stays, a parked slot that is not in a hole moves to the
	// hole, two parked slots keep their order (not the order of their destinations), a parked slot in a hole and one
	// that moves, each slot kind, equal slots (no swap, and the destinations stay), the spilled variables, an unbound
	// slot (err)
	agrees("lowest;;;;", "ok;;;", "ok;;;");
	agrees("lowest;;v0;;", "ok;;;", "ok;;;");
	agrees("lowest;v0 v1;v0 v1;0 1;", "ok;v0 v1;;0 1", "ok;v0 v1;;0 1");
	agrees("lowest;v1 v0;v0 v1;1 0;", "ok;v0 v1;SWAP1;0 1", "ok;v0 v1;SWAP1;0 1");
	agrees("lowest;v1;v0 v1;1;", "ok;v1;;1", "ok;v1;;1");
	agrees("lowest;v2 v0;v0 v1 v2;2 0;", "ok;v0 v2;SWAP1;0 2", "ok;v0 v2;SWAP1;0 2");
	agrees("lowest;v5 v4 v0 v1;v0 v1 v2 v3 v4 v5;5 4 0 1;", "ok;v0 v1 v5 v4;SWAP2 SWAP1 SWAP3 SWAP1;0 1 5 4",
		"ok;v0 v1 v5 v4;SWAP2 SWAP1 SWAP3 SWAP1;0 1 5 4");
	agrees("lowest;v4 v5 v0 v1;v0 v1 v2 v3 v4 v5;4 5 0 1;", "ok;v0 v1 v4 v5;SWAP2 SWAP1 SWAP3 SWAP1;0 1 4 5",
		"ok;v0 v1 v4 v5;SWAP2 SWAP1 SWAP3 SWAP1;0 1 4 5");
	agrees("lowest;v3 v1 v0;v0 v1 v2 v3;3 1 0;", "ok;v0 v1 v3;SWAP2;0 1 3", "ok;v0 v1 v3;SWAP2;0 1 3");
	agrees("lowest;v3 v4 v0;v0 v1 v2 v3 v4;3 4 0;", "ok;v0 v4 v3;SWAP2;0 4 3", "ok;v0 v4 v3;SWAP2;0 4 3");
	agrees("lowest;R _ l2 v5;v5 l2 _ R;3 2 1 0;", "ok;v5 l2 _ R;SWAP3 SWAP1 SWAP2 SWAP1;0 1 2 3",
		"ok;v5 l2 _ R;SWAP3 SWAP1 SWAP2 SWAP1;0 1 2 3");
	agrees("lowest;v0 v0;v0 v0;1 0;", "ok;v0 v0;;1 0", "ok;v0 v0;;1 0");
	agrees("lowest;v0 v0 v1;v1 v0 v0;1 2 0;", "ok;v1 v0 v0;SWAP2;0 2 1", "ok;v1 v0 v0;SWAP2;0 2 1");
	agrees("lowest;v0;v0;0;0", "ok;v0;;0", "ok;v0;;0");
	agrees("lowest;v3 v0;v0 v1 v2 v3;3 0;7 9", "ok;v0 v3;SWAP1;0 3", "ok;v0 v3;SWAP1;0 3");
	agrees("lowest;v0 l1;v0;0 -;", "err", "err");
	agrees("lowest;l1 v0;v0;- 0;", "err", "err");
	agrees("lowest;v0 v1;v0 v1 v2;0 -;", "err", "err");
	// the swap reach: a swap with a slot at depth 16; at depth 17 it blocks, with a parked slot in the way and without
	{
		std::string const result = "ok;" + vars(0, 15) + " v17;SWAP16;" + nats(0, 15) + " 17";
		agrees("lowest;v17 " + vars(1, 15) + " v0;" + vars(0, 17) + ";17 " + nats(1, 15) + " 0;", result, result);
	}
	{
		std::string const result = "blocked 0 1;v18 " + vars(1, 16) + " v0;;18 " + nats(1, 16) + " 0";
		agrees("lowest;v18 " + vars(1, 16) + " v0;" + vars(0, 18) + ";18 " + nats(1, 16) + " 0;", result, result);
	}
	{
		std::string const result = "blocked 0 1;v17 " + vars(1, 16) + " v0;;17 " + nats(1, 16) + " 0";
		agrees("lowest;v17 " + vars(1, 16) + " v0;" + vars(0, 17) + ";17 " + nats(1, 16) + " 0;", result, result);
	}
	// the stack limit: 1024 final slots, a parked bottom in a hole under 1022 slots, a parked slot that moves to the
	// top, and a rotation of 1024 slots that blocks
	{
		std::string const result = "ok;" + vars(0, 1023) + ";;" + nats(0, 1023);
		agrees("lowest;" + vars(0, 1023) + ";" + vars(0, 1023) + ";" + nats(0, 1023) + ";", result, result);
	}
	{
		std::string const result = "ok;v1023 " + vars(1, 1022) + ";;1023 " + nats(1, 1022);
		agrees("lowest;v1023 " + vars(1, 1022) + ";" + vars(0, 1023) + ";1023 " + nats(1, 1022) + ";", result, result);
	}
	{
		std::string const result = "ok;" + vars(0, 1021) + " v1023;SWAP1;" + nats(0, 1021) + " 1023";
		agrees("lowest;" + vars(0, 1020) + " v1023 v1021;" + vars(0, 1023) + ";" + nats(0, 1020) + " 1023 1021;", result,
			result);
	}
	{
		std::string const result = "blocked 0 1007;" + vars(1, 1023) + " v0;;" + nats(1, 1023) + " 0";
		agrees("lowest;" + vars(1, 1023) + " v0;" + vars(0, 1023) + ";" + nats(1, 1023) + " 0;", result, result);
	}
	// a wrong model result is not equal to the port result: an operation, a slot, a destination, the status
	for (std::string const wrong: {"ok;v0 v2;SWAP2;0 2", "ok;v2 v0;SWAP1;0 2", "ok;v0 v2;SWAP1;2 0",
			 "ok;v0 v2;SWAP1;0 -", "blocked 0 1;v0 v2;SWAP1;0 2", "ok;v0 v2;;0 2", "err"})
	{
		std::optional<port::Check> const check = port::check("lowest;v2 v0;v0 v1 v2;2 0;", wrong);
		expect(check && check->port != check->model, "a wrong lowest model result differs: " + wrong);
	}

	// not in the domain of the lowest unit: too few fields, too many fields, a bad slot, a bad destination, not one
	// destination per slot, a destination out of the target, a destination bound twice, a bad spilled id, more stack
	// slots or target slots than the stack limit
	throws("lowest;v0;v0;0");
	throws("lowest;v0;v0;0;;");
	throws("lowest;x;v0;0;");
	throws("lowest;v0;y;0;");
	throws("lowest;v0;v0;a;");
	throws("lowest;;;;x");
	throws("lowest;v0;v0;0 -;");
	throws("lowest;v0;v0;1;");
	throws("lowest;v0 v1;v0 v1;0 0;");
	throws("lowest;" + times("_", 1025) + ";;" + times("-", 1025) + ";");
	throws("lowest;;" + times("_", 1025) + ";;");

	// run (emit): an empty stack and target, all slots final, operations of removeSurplus, permuteAtLowestHeight and
	// buildBottomUp, each alone and in sequence, each slot kind, equal slots, the spilled variables
	agrees("emit;;;;", "ok;;;", "ok;;;");
	agrees("emit;v0 v1;v0 v1;0 1;", "ok;v0 v1;;0 1", "ok;v0 v1;;0 1");
	agrees("emit;v0;v0;0;0", "ok;v0;;0", "ok;v0;;0");
	agrees("emit;R v0;R v0;0 1;", "ok;R v0;;0 1", "ok;R v0;;0 1");
	agrees("emit;R;R;0;", "ok;R;;0", "ok;R;;0");
	agrees("emit;v0 v0;v0 v0;1 0;", "ok;v0 v0;;1 0", "ok;v0 v0;;1 0");
	agrees("emit;v0 v0;v0;0 -;", "ok;v0;POP;0", "ok;v0;POP;0");
	agrees("emit;v0 v0 v0;v0;- 0 -;", "ok;v0;POP POP;0", "ok;v0;POP POP;0");
	agrees("emit;v1 v0;v0 v1;1 0;", "ok;v0 v1;SWAP1;0 1", "ok;v0 v1;SWAP1;0 1");
	agrees("emit;v0 R;R v0;1 0;", "ok;R v0;SWAP1;0 1", "ok;R v0;SWAP1;0 1");
	agrees("emit;;l3 _;;", "ok;l3 _;PUSH:l3 PUSH:_;0 1", "ok;l3 _;PUSH:l3 PUSH:_;0 1");
	agrees("emit;;v3;;3", "ok;v3;LOAD:v3;0", "ok;v3;LOAD:v3;0");
	agrees("emit;v0;v0 v0;0;", "ok;v0 v0;DUP1;0 1", "ok;v0 v0;DUP1;0 1");
	agrees("emit;R;_ R;1;", "ok;_ R;PUSH:_ SWAP1;0 1", "ok;_ R;PUSH:_ SWAP1;0 1");
	agrees("emit;v7;l1 v7;1;", "ok;l1 v7;PUSH:l1 SWAP1;0 1", "ok;l1 v7;PUSH:l1 SWAP1;0 1");
	agrees("emit;v0;v0;-;0", "ok;v0;POP LOAD:v0;0", "ok;v0;POP LOAD:v0;0");
	agrees("emit;v0 l1;v0 v0;0 -;", "ok;v0 v0;POP DUP1;0 1", "ok;v0 v0;POP DUP1;0 1");
	agrees("emit;v1 l2;v1 v1 l2 v3;0 -;3", "ok;v1 v1 l2 v3;POP DUP1 PUSH:l2 LOAD:v3;0 1 2 3",
		"ok;v1 v1 l2 v3;POP DUP1 PUSH:l2 LOAD:v3;0 1 2 3");
	agrees("emit;l9 v1 v0;v0 v1 v2;- 1 0;2", "ok;v0 v1 v2;SWAP2 POP LOAD:v2;0 1 2",
		"ok;v0 v1 v2;SWAP2 POP LOAD:v2;0 1 2");
	agrees("emit;l5 v0 v0;v0 v0 v0;- 2 0;", "ok;v0 v0 v0;SWAP2 POP DUP1;0 1 2", "ok;v0 v0 v0;SWAP2 POP DUP1;0 1 2");
	agrees("emit;v0 v0 v0;v0 v0 v0 v0;- 0 -;", "ok;v0 v0 v0 v0;POP POP DUP1 DUP1 DUP1;0 1 2 3",
		"ok;v0 v0 v0 v0;POP POP DUP1 DUP1 DUP1;0 1 2 3");
	agrees("emit;R _ l2 v5;v5 l2 _ R;3 2 1 0;", "ok;v5 l2 _ R;SWAP3 SWAP1 SWAP2 SWAP1;0 1 2 3",
		"ok;v5 l2 _ R;SWAP3 SWAP1 SWAP2 SWAP1;0 1 2 3");
	agrees("emit;v0 v1;v1 v0 v2;1 0;2", "ok;v1 v0 v2;SWAP1 LOAD:v2;0 1 2", "ok;v1 v0 v2;SWAP1 LOAD:v2;0 1 2");
	agrees("emit;v2 v0;v0 v1 v2;2 0;1", "ok;v0 v1 v2;SWAP1 LOAD:v1 SWAP1;0 1 2", "ok;v0 v1 v2;SWAP1 LOAD:v1 SWAP1;0 1 2");
	agrees("emit;v3;v0 v1 v2 v3;3;0 1 2", "ok;v0 v1 v2 v3;LOAD:v1 LOAD:v2 LOAD:v0 SWAP3;0 1 2 3",
		"ok;v0 v1 v2 v3;LOAD:v1 LOAD:v2 LOAD:v0 SWAP3;0 1 2 3");
	agrees("emit;v1 R l3;R v1 _ l3;1 0 -;", "ok;R v1 _ l3;POP SWAP1 PUSH:_ PUSH:l3;0 1 2 3",
		"ok;R v1 _ l3;POP SWAP1 PUSH:_ PUSH:l3;0 1 2 3");
	agrees("emit;l9 v2 v0 l8;v0 v1 v2;- 2 0 -;1", "ok;v0 v1 v2;POP SWAP2 POP LOAD:v1 SWAP1;0 1 2",
		"ok;v0 v1 v2;POP SWAP2 POP LOAD:v1 SWAP1;0 1 2");
	agrees("emit;v4 v5 v0 v1;v0 v1 v2 v3 v4 v5;4 5 0 1;2 3",
		"ok;v0 v1 v2 v3 v4 v5;SWAP2 SWAP1 SWAP3 SWAP1 LOAD:v2 SWAP2 LOAD:v3 SWAP2;0 1 2 3 4 5",
		"ok;v0 v1 v2 v3 v4 v5;SWAP2 SWAP1 SWAP3 SWAP1 LOAD:v2 SWAP2 LOAD:v3 SWAP2;0 1 2 3 4 5");
	agrees("emit;v4 v5 v0 v1;v0 v1 v0 v1 v4 v5;4 5 0 1;",
		"ok;v0 v1 v0 v1 v4 v5;SWAP2 SWAP1 SWAP3 SWAP1 DUP4 SWAP2 DUP4 SWAP2;0 1 2 3 4 5",
		"ok;v0 v1 v0 v1 v4 v5;SWAP2 SWAP1 SWAP3 SWAP1 DUP4 SWAP2 DUP4 SWAP2;0 1 2 3 4 5");
	// the third check of State.Valid fails (err): a target slot that is not on the stack after removeSurplus, not
	// spilled and not a literal or junk: a variable, also when other variables are spilled, a variable that
	// removeSurplus pops, a return label that a variable is bound for, a return label that removeSurplus pops, and a
	// return label that is not on the stack (the third check comes before the fourth)
	agrees("emit;;v0;;", "err", "err");
	agrees("emit;l9;v0;-;", "err", "err");
	agrees("emit;v0;v0;-;", "err", "err");
	agrees("emit;v0 l1;v0 v0;- -;", "err", "err");
	agrees("emit;v0 v1;v1 v0 v2;1 0;", "err", "err");
	agrees("emit;v2 v0;v0 v1 v2;2 0;", "err", "err");
	agrees("emit;v4 v5 v0 v1;v0 v1 v2 v3 v4 v5;4 5 0 1;", "err", "err");
	agrees("emit;v0 l9;v0 l9 v1;0 -;", "err", "err");
	agrees("emit;v0 l9;v0 l9 v1;0 -;9", "err", "err");
	agrees("emit;v0;R;0;", "err", "err");
	agrees("emit;v0;v0 R;0;", "err", "err");
	agrees("emit;;R;;", "err", "err");
	agrees("emit;R;R;-;", "err", "err");
	agrees("emit;v1 R l3;R v1 _ l3;1 - -;", "err", "err");
	agrees("emit;l9 v0;v0 v1 R;- 0;1", "err", "err");
	// the fourth check of State.Valid fails (err): a return label of the target that is on the stack, but that no
	// stack slot is bound for
	agrees("emit;R;R R;0;", "err", "err");
	agrees("emit;R v0;R v0 R;0 1;", "err", "err");
	agrees("emit;v0 R;R v0 R;1 0;", "err", "err");
	agrees("emit;R l1;R R;0 -;", "err", "err");
	// the third and the fourth check decide the result: without them, buildBottomUp blocks at the DUP of depth 17 of
	// v0 or R (the model result without v99 is "blocked 0 1")
	agrees("emit;" + vars(0, 16) + ";" + vars(0, 16) + " v99 v0;" + nats(0, 16) + ";", "err", "err");
	agrees("emit;R " + vars(1, 16) + ";R " + vars(1, 16) + " R;" + nats(0, 16) + ";", "err", "err");
	// blocked in removeSurplus: a surplus slot at depth 17, also with a return label in the target that is not on the
	// stack, so that the third check would fail
	{
		std::string const result = "blocked 0 1;l0 " + vars(1, 17) + ";;- " + nats(0, 16);
		agrees("emit;l0 " + vars(1, 17) + ";" + vars(1, 17) + ";- " + nats(0, 16) + ";", result, result);
		agrees("emit;l0 " + vars(1, 17) + ";" + vars(1, 17) + " R;- " + nats(0, 16) + ";", result, result);
	}
	{
		std::string const result = "blocked 0 1;l0 " + vars(0, 16) + ";;- " + nats(0, 16);
		agrees("emit;l0 " + vars(0, 16) + ";" + vars(0, 16) + " v0;- " + nats(0, 16) + ";", result, result);
	}
	// a surplus slot at depth 16: removeSurplus, then permuteAtLowestHeight moves the 15 slots above it down
	{
		std::string const result = "ok;" + vars(1, 16) + ";SWAP16 POP SWAP1 SWAP2 SWAP3 SWAP4 SWAP5 SWAP6 SWAP7 SWAP8 "
			"SWAP9 SWAP10 SWAP11 SWAP12 SWAP13 SWAP14 SWAP15;" + nats(0, 15);
		agrees("emit;l0 " + vars(1, 16) + ";" + vars(1, 16) + ";- " + nats(0, 15) + ";", result, result);
	}
	// blocked in permuteAtLowestHeight: a swap of depth 17 or 18, also with a target that fails the third check, and
	// with a spilled variable that buildBottomUp would load
	{
		std::string const result = "blocked 0 1;v18 " + vars(1, 16) + " v0;;18 " + nats(1, 16) + " 0";
		std::string const stack = "emit;v18 " + vars(1, 16) + " v0;";
		std::string const dests = ";18 " + nats(1, 16) + " 0;";
		agrees(stack + vars(0, 18) + dests, result, result);
		agrees(stack + vars(0, 18) + " v99" + dests, result, result);
		agrees(stack + vars(0, 18) + dests + "17", result, result);
	}
	{
		std::string const result = "blocked 0 1;v17 " + vars(1, 16) + " v0;;17 " + nats(1, 16) + " 0";
		agrees("emit;v17 " + vars(1, 16) + " v0;" + vars(0, 17) + " v0;17 " + nats(1, 16) + " 0;", result, result);
	}
	// blocked in buildBottomUp: a DUP of depth 17, after a POP of removeSurplus, a SWAP of depth 17; a DUP of depth 16
	{
		std::string const result = "blocked 0 1;" + vars(0, 16) + ";;" + nats(0, 16);
		agrees("emit;" + vars(0, 16) + ";" + vars(0, 16) + " v0;" + nats(0, 16) + ";", result, result);
	}
	{
		std::string const result = "blocked 0 1;" + vars(0, 16) + ";POP;" + nats(0, 16);
		agrees("emit;" + vars(0, 16) + " l0;" + vars(0, 16) + " v0;" + nats(0, 16) + " -;", result, result);
	}
	{
		std::string const result = "blocked 1 1;" + vars(0, 17) + ";;" + nats(0, 17);
		agrees("emit;" + vars(0, 17) + ";" + vars(0, 17) + " v1 v0;" + nats(0, 17) + ";", result, result);
	}
	{
		std::string const result = "ok;" + vars(0, 15) + " v0;DUP16;" + nats(0, 16);
		agrees("emit;" + vars(0, 15) + ";" + vars(0, 15) + " v0;" + nats(0, 15) + ";", result, result);
	}
	// the stack limit: 1024 final slots, 1024 surplus slots, 1024 generated slots, 1024 surplus slots then 16 generated
	// slots, 16 surplus slots then 1024 generated slots, a DUP blocked under 1023 slots, a surplus slot blocked under
	// 1023 slots
	{
		std::string const result = "ok;" + vars(0, 1023) + ";;" + nats(0, 1023);
		agrees("emit;" + vars(0, 1023) + ";" + vars(0, 1023) + ";" + nats(0, 1023) + ";", result, result);
	}
	{
		std::string const result = "ok;;" + times("POP", 1024) + ";";
		agrees("emit;" + times("l0", 1024) + ";;" + times("-", 1024) + ";", result, result);
	}
	{
		std::string const result =
			"ok;" + times("l0", 1024) + ";PUSH:l0 " + times("DUP1", 1023) + ";" + nats(0, 1023);
		agrees("emit;;" + times("l0", 1024) + ";;", result, result);
	}
	{
		std::string const result =
			"ok;" + times("l0", 16) + ";" + times("POP", 1024) + " PUSH:l0 " + times("DUP1", 15) + ";" + nats(0, 15);
		agrees("emit;" + times("l1", 1024) + ";" + times("l0", 16) + ";" + times("-", 1024) + ";", result, result);
	}
	{
		std::string const result = "ok;" + times("l0", 1024) + ";" + times("POP", 16) + " PUSH:l0 " +
			times("DUP1", 1023) + ";" + nats(0, 1023);
		agrees("emit;" + times("l1", 16) + ";" + times("l0", 1024) + ";" + times("-", 16) + ";", result, result);
	}
	{
		std::string const result = "blocked 0 1007;" + vars(0, 1022) + ";;" + nats(0, 1022);
		agrees("emit;" + vars(0, 1022) + ";" + vars(0, 1022) + " v0;" + nats(0, 1022) + ";", result, result);
	}
	{
		std::string const result = "blocked 0 1007;l0 " + vars(1, 1023) + ";;- " + nats(0, 1022);
		agrees("emit;l0 " + vars(1, 1023) + ";" + vars(1, 1023) + ";- " + nats(0, 1022) + ";", result, result);
	}
	// a wrong model result is not equal to the port result: an operation, a slot, a destination, the status
	for (std::string const wrong: {"ok;v0 v1 v2;SWAP1 LOAD:v2;0 1 2", "ok;v0 v1 v2;SWAP2 POP LOAD:v1;0 1 2",
			 "ok;v0 v2 v1;SWAP2 POP LOAD:v2;0 1 2", "ok;v0 v1 v2;SWAP2 POP LOAD:v2;0 2 1",
			 "ok;v0 v1;SWAP2 POP LOAD:v2;0 1", "blocked 0 1;v0 v1 v2;SWAP2 POP LOAD:v2;0 1 2", "err"})
	{
		std::optional<port::Check> const check = port::check("emit;l9 v1 v0;v0 v1 v2;- 1 0;2", wrong);
		expect(check && check->port != check->model, "a wrong emit model result differs: " + wrong);
	}
	{
		std::optional<port::Check> const check = port::check("emit;v0;R;0;", "ok;R;;0");
		expect(check && check->port != check->model, "a wrong emit model result differs: ok;R;;0");
	}

	// not in the domain of the emit unit: too few fields, too many fields, a bad slot, a bad destination, not one
	// destination per slot, a destination out of the target, a destination bound twice, a bad spilled id, more stack
	// slots or target slots than the stack limit
	throws("emit;v0;v0;0");
	throws("emit;v0;v0;0;;");
	throws("emit;x;v0;0;");
	throws("emit;v0;y;0;");
	throws("emit;v0;v0;a;");
	throws("emit;;;;x");
	throws("emit;v0;v0;0 -;");
	throws("emit;v0;v0;1;");
	throws("emit;v0 v1;v0 v1;0 0;");
	throws("emit;" + times("_", 1025) + ";;" + times("-", 1025) + ";");
	throws("emit;;" + times("_", 1025) + ";;");

	if (failures > 0)
	{
		std::cerr << failures << " failures\n";
		return EXIT_FAILURE;
	}
	std::cout << "port_test: all checks pass\n";
	return EXIT_SUCCESS;
}
