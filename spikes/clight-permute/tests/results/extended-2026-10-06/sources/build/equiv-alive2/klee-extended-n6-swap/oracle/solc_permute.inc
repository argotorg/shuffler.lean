/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

	[[nodiscard]] std::optional<Blocked> permute(std::vector<std::size_t> _permutation)
	{
		// Equal slots are interchangeable: among them, those already at one of their desired offsets stay, the
		// others take the remaining offsets. Otherwise equal slots would pass each other in cycles.
		{
			std::vector<std::size_t> positions = ranges::views::iota(std::size_t{0}, m_data.size()) | ranges::to<std::vector>;
			// stability needed for reproducibility across platforms (sort doesn't guarantee order for ties)
			// also it keeps chunks of positions that belong to same data in ascending order
			ranges::stable_sort(
				positions,
				[&](std::size_t const _a, std::size_t const _b) { return m_data[_a] < m_data[_b]; }
			);
			for (ranges::subrange const group: positions | ranges::views::chunk_by(
				[&](std::size_t const _a, std::size_t const _b) { return m_data[_a] == m_data[_b]; }
			))
			{
				// the group is empty or contains only a single element (ie no second, equal slot exists)
				if (ranges::distance(group) < 2)
					continue;
				// the group's desired offsets
				std::vector<std::size_t> desired =
					group |
					ranges::views::transform([&_permutation](std::size_t const _pos) { return _permutation[_pos]; }) |
					ranges::to<std::vector>;
				// sorted needed for set operations
				ranges::sort(desired);
				// slots already standing on one of the group's desired offsets stay put
				// stayers = group \cap desired => _permutation[pos] = pos
				std::vector<std::size_t> stayers;
				ranges::set_intersection(group, desired, std::back_inserter(stayers));
				for (std::size_t const pos: stayers)
					_permutation[pos] = pos;
				// the others take the vacant offsets, both sides ascending, so nothing crosses
				// movers = group ∖ desired
				std::vector<std::size_t> movers;
				ranges::set_difference(group, desired, std::back_inserter(movers));
				// vacant = desired ∖ group => _permutation[movers[i]] = vacant[i]
				std::vector<std::size_t> vacant;
				ranges::set_difference(desired, group, std::back_inserter(vacant));

				// desired is built with exactly one entry per group member, so |G| = |D|, i.e.,
				// |movers| =  |G ∖ D| = |G| − |G \cap D| and |vacant| = |D ∖ G| = |D| − |D \cap G|
				yulAssert(movers.size() == vacant.size());
				for (std::size_t i = 0; i < movers.size(); ++i)
					_permutation[movers[i]] = vacant[i];
			}
		}

		auto exchangeWithTop = [this, &_permutation](StackOffset const _pos) -> std::optional<Blocked>
		{
			StackOffset const top{m_data.size() - 1};
			if (m_data[_pos.value] == m_data[top.value])
				m_mapping.swapDestinations(_pos, top);
			else if (!isSwapReachable(_pos))
				return blockSwapUnreachable(_pos);
			else
				swapWith(_pos);
			std::swap(_permutation[_pos.value], _permutation[top.value]);
			return std::nullopt;
		};

		while (true)
		{
			std::size_t const top = m_data.size() - 1;
			if (
				StackOffset const desiredOfTop{_permutation[top]};
				desiredOfTop != top
			)
			{
				// an equal slot standing at the desired offset serves the top's destination just as well
				if (std::optional<Blocked> blocked = exchangeWithTop(desiredOfTop))
					return blocked;
				continue;
			}
			StackOffset misplaced{empty};
			for (std::size_t const pos: ranges::views::iota(std::size_t{0}, top) | ranges::views::reverse)
				if (_permutation[pos] != pos)  // not already in place
				{
					misplaced = StackOffset{pos};  // we found something misplaced
					break;
				}

			if (misplaced == empty)
				return std::nullopt;  // nothing misplaced was found, we're done

			// a misplaced slot equal to the top takes over the top's destination, making the top the misplaced
			// one; it then travels to its destination directly instead of dislodging an in-place slot
			if (std::optional<Blocked> blocked = exchangeWithTop(misplaced))
				return blocked;
		}
	}
