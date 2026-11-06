#include <array>
#include <cstdint>
#include <iostream>

int main() {
  constexpr std::uint32_t states = 6;
  constexpr std::uint32_t base = 25;
  constexpr std::uint32_t total = 244140625;
  std::array<std::uint64_t, 7> cycles{}, halts{}, writes{};
  for (std::uint32_t code = 0; code < total; ++code) {
    std::uint32_t digits[6], remaining = code;
    for (std::uint32_t j = 0; j < states; ++j) {
      digits[j] = remaining % base;
      remaining /= base;
    }
    std::uint32_t seen = 0, q = 0, distinct = 0;
    for (;;) {
      const std::uint32_t flag = 1u << q;
      if (seen & flag) { cycles[distinct]++; break; }
      seen |= flag;
      distinct++;
      const std::uint32_t action = digits[q];
      if (action == 0) { halts[distinct]++; break; }
      if (action >= 13) { writes[distinct]++; break; }
      q = (action - 1) / 2;
    }
  }

  auto totalCount = [](const std::array<std::uint64_t, 7>& counts) {
    std::uint64_t ans = 0;
    for (auto v : counts) ans += v;
    return ans;
  };
  const std::array<std::uint64_t, 7> expectedCycles =
    {0, 19531250, 15625000, 7500000, 2400000, 480000, 46080};
  const std::array<std::uint64_t, 7> expectedHalts =
    {0, 9765625, 3906250, 1250000, 300000, 48000, 3840};
  const std::array<std::uint64_t, 7> expectedWrites =
    {0, 117187500, 46875000, 15000000, 3600000, 576000, 46080};

  for (std::uint32_t k = 1; k <= states; ++k) {
    std::cout << "distinct=" << k << " cycle=" << cycles[k]
      << " halt=" << halts[k] << " first-one=" << writes[k] << '\n';
  }
  std::cout << "cycle=" << totalCount(cycles)
    << " halt=" << totalCount(halts)
    << " first-one=" << totalCount(writes)
    << " all=" << totalCount(cycles) + totalCount(halts) + totalCount(writes)
    << '\n';
  if (cycles != expectedCycles || halts != expectedHalts ||
      writes != expectedWrites ||
      totalCount(cycles) + totalCount(halts) + totalCount(writes) != total) {
    std::cerr << "Exhaustive census disagrees with symbolic formula.\n";
    return 1;
  }
  return 0;
}
