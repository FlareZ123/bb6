#include <array>
#include <cstdint>
#include <iostream>

/*
 * Full 25^6 read-zero census of a one-turn, source-certifiable fresh-ray
 * family, with root A and B..F remaining possible control states.
 *
 * First A/0 instruction: write 0, choose a direction, enter B..F.
 * Afterward the B..F read-zero orbit stays on its five states,
 * always moves oppositely, first closes a control cycle, and writes
 * at least one 1. These conditions establish nonhalting by the
 * unmodified original-machine oneTurnRay_cover source theorem.
 *
 * The prefix contains a direction reversal and a write-one, so it
 * is provably outside the previous all-zero / all-one-direction
 * first-event census. Read-one rows are entirely unrestricted.
 */
int main() {
  constexpr std::uint32_t total = 244140625;
  std::array<std::uint64_t, 6> counts{};
  for (std::uint32_t code = 0; code < total; ++code) {
    std::uint32_t digits[6], n = code;
    for (int i = 0; i < 6; ++i) {
      digits[i] = n % 25;
      n /= 25;
    }
    const std::uint32_t first = digits[0];
    if (first < 1 || first >= 13) continue;
    const std::uint32_t initialDir = (first - 1) % 2;
    std::uint32_t q = (first - 1) / 2;
    if (q == 0) continue;
    std::uint32_t seen = 0, k = 0;
    bool writesOne = false;
    for (;;) {
      if (seen & (1u << q)) {
        if (writesOne) ++counts[k];
        break;
      }
      seen |= 1u << q;
      ++k;
      const std::uint32_t action = digits[q];
      if (action == 0) break;
      const std::uint32_t value = action >= 13 ? action - 13 : action - 1;
      if (value % 2 == initialDir) break;
      writesOne |= action >= 13;
      q = value / 2;
      if (q == 0) break;
    }
  }
  const std::array<std::uint64_t, 6> expected =
      {0, 3906250, 3750000, 1575000, 360000, 37200};
  std::uint64_t found = 0;
  for (int k = 1; k <= 5; ++k) {
    std::cout << "q-states=" << k << " count=" << counts[k] << '\n';
    found += counts[k];
  }
  std::cout << "total-readzero=" << found
            << " total-all-tables=" << found * 244140625 << '\n';
  return counts == expected && found == 9628450 ? 0 : 1;
}
