#include <array>
#include <cstdint>
#include <iostream>

/*
 * Independent exhaustive classification over all 25^6 read-zero
 * six-state transition assignments. A read-zero control graph is used
 * ONLY to identify three classes with mathematically sound raw-machine
 * interpretations:
 *   - first repeated control state with all writes zero OR all
 *     directions equal: nonhalting forever;
 *   - first halt with all previous writes zero OR directions equal:
 *     exact halting score equal to number of visited states;
 *   - everything else: explicitly unresolved by this classification.
 *
 * Read-one table entries are arbitrary for either certified class.
 */
int main() {
  constexpr std::uint32_t total = 244140625;
  std::array<std::uint64_t, 7> cycles{}, halts{}, open{};
  for (std::uint32_t code = 0; code < total; ++code) {
    std::uint32_t digits[6], remaining = code;
    for (std::uint32_t j = 0; j < 6; ++j) {
      digits[j] = remaining % 25;
      remaining /= 25;
    }
    std::uint32_t seen = 0, q = 0, distinct = 0;
    bool allZeroWrites = true, sameDirection = true;
    int initialDirection = -1;
    for (;;) {
      const std::uint32_t flag = 1u << q;
      if (seen & flag) {
        (allZeroWrites || sameDirection ? cycles : open)[distinct]++;
        break;
      }
      seen |= flag;
      ++distinct;
      const std::uint32_t action = digits[q];
      if (action == 0) {
        (allZeroWrites || sameDirection ? halts : open)[distinct]++;
        break;
      }
      const bool write = action >= 13;
      allZeroWrites &= !write;
      const std::uint32_t value = write ? action - 13 : action - 1;
      const int direction = static_cast<int>(value % 2);
      if (initialDirection < 0) initialDirection = direction;
      else sameDirection &= direction == initialDirection;
      q = value / 2;
    }
  }
  auto sum = [](const auto& a) {
    std::uint64_t v = 0;
    for (auto x : a) v += x;
    return v;
  };
  for (int k = 1; k <= 6; ++k) {
    std::cout << "k=" << k << " cycle=" << cycles[k]
              << " halt=" << halts[k] << " open=" << open[k] << '\n';
  }
  std::cout << "totals: cycle " << sum(cycles) << " halt " << sum(halts)
            << " open " << sum(open) << '\n';
  if (sum(cycles) != 107196800 || sum(halts) != 21677405 ||
      sum(open) != 115266420 ||
      sum(cycles) + sum(halts) + sum(open) != total) {
    std::cerr << "Census disagrees with the independent closed formulas.\n";
    return 1;
  }
  return 0;
}
