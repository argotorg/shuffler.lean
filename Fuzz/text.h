// The text helpers of the case and result lines (Fuzz/Oracle.lean), for fuzz.cpp and port.cpp.
#pragma once

#include <cstdint>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace fuzztext
{

/// The parts of `_s` between the separators; a separator at the end gives an empty last part
inline std::vector<std::string> split(std::string const& _s, char const _sep)
{
	std::vector<std::string> parts;
	std::stringstream stream(_s);
	for (std::string part; std::getline(stream, part, _sep);)
		parts.push_back(part);
	if (!_s.empty() && _s.back() == _sep)
		parts.emplace_back();
	return parts;
}

inline std::vector<std::string> words(std::string const& _s)
{
	std::vector<std::string> result;
	std::stringstream stream(_s);
	for (std::string word; stream >> word;)
		result.push_back(word);
	return result;
}

inline std::string join(std::vector<std::string> const& _words)
{
	std::string result;
	for (std::size_t i = 0; i < _words.size(); ++i)
		result += (i > 0 ? " " : "") + _words[i];
	return result;
}

inline std::uint32_t parseNat(std::string const& _s)
{
	if (_s.empty() || _s.find_first_not_of("0123456789") != std::string::npos)
		throw std::invalid_argument("not a number: " + _s);
	return static_cast<std::uint32_t>(std::stoul(_s));
}

}
