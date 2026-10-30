// Runs the checks of the fuzzer on each case line of stdin (the format of Fuzz/Oracle.lean), for example on all
// small cases of a unit (Fuzz/pop_cases.sh). Prints each difference, in the format of Fuzz/fuzz.cpp, and then the
// number of cases. Exit status: 1 if there is a port difference, 2 if each difference is one of solc and the model,
// else 0.
//
// This file includes fuzz.cpp, so the checks are the checks of the fuzzer.

#include "fuzz.cpp"

int main()
{
	initializeLean();
	std::size_t cases = 0;
	bool portDifference = false;
	bool solcDifference = false;
	for (std::string line; std::getline(std::cin, line); ++cases)
		if (std::optional<std::string> const diff = difference(line))
		{
			std::cout << *diff << '\n';
			(diff->starts_with("port\t") ? portDifference : solcDifference) = true;
		}
	std::cout << cases << " cases\n";
	return portDifference ? 1 : solcDifference ? 2 : 0;
}
