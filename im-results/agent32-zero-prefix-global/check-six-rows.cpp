#include <array>
#include <cstdint>
#include <iostream>

/*
 * All 244,140,625 six-state read-zero assignments, with all six read-one
 * slots arbitrary. Three source-certifiable sufficient predicates:
 * pristine-control zero-writing cycle, physically encountered halt with
 * score <=6, or a finite actual all-zero-read blank-root prefix of <=6
 * moves reaching a still-blank half-ray with fixed-direction closed
 * read-zero control graph. No read-one instruction is ever assumed.
 *
 * This independent finite-state C++ enumeration is NOT a Lean proof of
 * the exact number emitted by the separate proof-carrying ZeroRowAudit.
 */
static inline std::uint32_t next(std::uint32_t a) {
  return (a >= 13 ? a - 13 : a - 1) / 2;
}
static inline bool right(std::uint32_t a) {
  return ((a >= 13 ? a - 13 : a - 1) % 2) != 0;
}
static inline bool pristineCycle(const std::uint32_t d[6]) {
  unsigned s = 0, seen = 0;
  for (;;) {
    if (seen & (1u << s)) return true;
    seen |= 1u << s;
    const auto a = d[s];
    if (a == 0 || a >= 13) return false;
    s = next(a);
  }
}
static inline bool closedRayCycle(const std::uint32_t d[6],
                                  unsigned state, bool direction) {
  unsigned seen = 0;
  for (;;) {
    if (seen & (1u << state)) return true;
    seen |= 1u << state;
    const auto a = d[state];
    if (a == 0 || right(a) != direction) return false;
    state = next(a);
  }
}
static inline bool freshRay(unsigned ones, int head, bool direction) {
  const unsigned position = static_cast<unsigned>(head + 6);
  const unsigned forwardMask = direction
      ? (8191u & ~((1u << position) - 1))
      : ((1u << (position + 1)) - 1);
  return (ones & forwardMask) == 0;
}

int main() {
  constexpr std::uint32_t total = 244140625;
  std::array<std::uint64_t, 4> count{};
  std::array<std::uint64_t, 7> rayAt{}, haltScore{};
  std::uint64_t openNeedsReadOne = 0, openAtPrefixLimit = 0;
  for (std::uint32_t code = 0; code < total; ++code) {
    std::uint32_t rows[6], n = code;
    for (int j = 0; j < 6; ++j) {
      rows[j] = n % 25;
      n /= 25;
    }
    if (pristineCycle(rows)) {
      ++count[0];
      continue;
    }
    unsigned state = 0, ones = 0;
    int head = 0;
    bool classified = false;
    for (unsigned step = 0; step <= 6; ++step) {
      const unsigned bit = 1u << (head + 6);
      if (ones & bit) {
        ++openNeedsReadOne;
        break;
      }
      if ((freshRay(ones, head, true) &&
           closedRayCycle(rows, state, true)) ||
          (freshRay(ones, head, false) &&
           closedRayCycle(rows, state, false))) {
        ++count[2];
        ++rayAt[step];
        classified = true;
        break;
      }
      if (step == 6) {
        ++openAtPrefixLimit;
        break;
      }
      const auto action = rows[state];
      if (action == 0) {
        ++count[1];
        ++haltScore[step + 1];
        classified = true;
        break;
      }
      if (action >= 13) ones |= bit;
      else ones &= ~bit;
      head += right(action) ? 1 : -1;
      state = next(action);
    }
    if (!classified) ++count[3];
  }

  std::cout << "pristine-cycle=" << count[0]
            << " short-halt=" << count[1]
            << " prefix-ray=" << count[2]
            << " open=" << count[3] << '\n';
  const std::uint64_t certified = count[0] + count[1] + count[2];
  std::cout << "certified-readzero=" << certified << "/" << total
            << " certified-full=" << certified * total << '\n';
  for (std::size_t step = 0; step <= 6; ++step) {
    std::cout << "step=" << step << " ray-entries=" << rayAt[step]
              << " halts-score=" << haltScore[step] << '\n';
  }
  std::cout << "open-first-unknown-read-one=" << openNeedsReadOne
            << " open-prefix-limit-six=" << openAtPrefixLimit << '\n';
  constexpr std::array<std::uint64_t, 4> expected =
      {45582330, 23011245, 74467400, 101079650};
  return count == expected && certified == 143060975 &&
         openNeedsReadOne == 95287330 && openAtPrefixLimit == 5792320 ? 0 : 1;
}
