#include <array>
#include <cstdint>
#include <iostream>

// Independent audit of the entire four-free-zero-row subcube for each
// three-input lasso family. The classifier matches check-six-rows.cpp's
// finite predicates on actual blank tape, with all read-one rows unknown.
static unsigned successor(unsigned a) {
  return (a >= 13 ? a - 13 : a - 1) / 2;
}
static bool right(unsigned a) {
  return ((a >= 13 ? a - 13 : a - 1) % 2) != 0;
}
static bool pristineCycle(const std::array<unsigned, 6>& d) {
  unsigned state = 0, seen = 0;
  for (;;) {
    if ((seen & (1u << state)) != 0) return true;
    seen |= 1u << state;
    const unsigned action = d[state];
    if (action == 0 || action >= 13) return false;
    state = successor(action);
  }
}
static bool closedRayCycle(const std::array<unsigned, 6>& d,
                            unsigned state, bool direction) {
  unsigned seen = 0;
  for (;;) {
    if ((seen & (1u << state)) != 0) return true;
    seen |= 1u << state;
    const unsigned action = d[state];
    if (action == 0 || right(action) != direction) return false;
    state = successor(action);
  }
}
static bool freshRay(unsigned ones, int head, bool direction) {
  const unsigned pos = static_cast<unsigned>(head + 6);
  const unsigned forwardMask = direction
      ? (8191u & ~((1u << pos) - 1))
      : ((1u << (pos + 1)) - 1);
  return (ones & forwardMask) == 0;
}

static bool opensAtReadOneTwo(const std::array<unsigned, 6>& d) {
  if (pristineCycle(d)) return false;
  unsigned state = 0, ones = 0;
  int head = 0;
  for (unsigned step = 0; step <= 6; ++step) {
    const unsigned bit = 1u << (head + 6);
    if ((ones & bit) != 0) return step == 2;
    if ((freshRay(ones, head, true) && closedRayCycle(d, state, true)) ||
        (freshRay(ones, head, false) && closedRayCycle(d, state, false)))
      return false;
    if (step == 6) return false;
    const unsigned action = d[state];
    if (action == 0) return false;
    if (action >= 13) ones |= bit;
    else ones &= ~bit;
    head += right(action) ? 1 : -1;
    state = successor(action);
  }
  return false;
}

int main() {
  constexpr unsigned freeCount = 25u * 25u * 25u * 25u;
  std::uint64_t witnessed = 0;
  for (unsigned q = 1; q < 6; ++q) {
    for (unsigned dir = 0; dir < 2; ++dir) {
      for (unsigned code = 0; code < freeCount; ++code) {
        std::array<unsigned,6> rows{};
        rows[0] = 13u + 2u*q + dir;
        rows[q] = 1u + (1u-dir);
        unsigned rem = code;
        for (unsigned i = 1; i < 6; ++i) {
          if (i == q) continue;
          rows[i] = rem % 25u;
          rem /= 25u;
        }
        if (!opensAtReadOneTwo(rows)) {
          std::cerr << "unexpected certificate: q=" << q << " dir=" << dir
                    << " code=" << code << '\n';
          return 1;
        }
        ++witnessed;
      }
    }
  }
  std::cout << "read-zero assignments always open at genuine A/1 after "
            << "two moves=" << witnessed << '\n';
  std::cout << "disjoint full-table lasso cylinders="
            << 20ull * 3814697265625ull << '\n';
  return witnessed == 3906250ull ? 0 : 1;
}
