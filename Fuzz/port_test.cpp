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

}

int main()
{
	// the kinds without a port unit
	for (std::string const line: {"map;L;v0;v0;0", "surplus;v0;v0;0;", "permute;v0;0", "emit;;;;", "plan;L;0;;;"})
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

	// not in the domain of the port unit: a surplus slot, a bad slot, a bad destination, too few fields,
	// a destination bound twice, a destination out of the target, more slots than the port's stack limit
	throws("bottomup;v0 v1;v0;0 -;");
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

	if (failures > 0)
	{
		std::cerr << failures << " failures\n";
		return EXIT_FAILURE;
	}
	std::cout << "port_test: all checks pass\n";
	return EXIT_SUCCESS;
}
