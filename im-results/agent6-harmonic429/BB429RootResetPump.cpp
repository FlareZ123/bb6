#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
using i64 = std::int64_t;

enum class Tag { F, R2, R1, R0, E1, Eeven, Eodd, O2, Oeven1, Oeven, Oodd, Halt };
struct Step { i64 u, w; Tag tag; };

// Direct transcription of BB429Rank.next, with Nat subtractions safe in the
// corresponding branches (the four equality cases are tested before d=u-w/2).
static Step next(i64 u, i64 w) {
  if (w >= 2*u + 3) return {2*u+3, w-2*u-3, Tag::F};
  if (w == 2*u + 2) return {0, 4*u+18, Tag::R2};
  if (w == 2*u + 1) return {11, 4*u+2, Tag::R1};
  if (w == 2*u) return {0, 4*u+12, Tag::R0};
  const i64 d = u - w/2;
  if ((w & 1) == 0) {
    if (d == 1) return {0, 2*w+12, Tag::E1};
    if ((d & 1) == 0) return {11, 2*u+w-2, Tag::Eeven};
    return {0, 2*u+w+10, Tag::Eodd};
  }
  if (d == 1) return {u, w, Tag::Halt};
  if (d == 2) return {0, 2*w+8, Tag::O2};
  if ((d & 1) == 0) {
    if (w == 1) return {11, 2*u+10, Tag::Oeven1};
    return {d+7, 2*w-4, Tag::Oeven};
  }
  return {d+3, 2*w, Tag::Oodd};
}

static const char* name(Tag t) {
  switch(t) {
    case Tag::F: return "F"; case Tag::R2: return "R2"; case Tag::R1: return "R1";
    case Tag::R0: return "R0"; case Tag::E1: return "E1"; case Tag::Eeven: return "Eeven";
    case Tag::Eodd: return "Eodd"; case Tag::O2: return "O2"; case Tag::Oeven1: return "Oeven1";
    case Tag::Oeven: return "Oeven"; case Tag::Oodd: return "Oodd"; case Tag::Halt: return "Halt";
  }
  return "?";
}

int main() {
  constexpr i64 targetW = 530028452;
  constexpr i64 targetEndW = 805306268;
  constexpr i64 expectedPrefix = 149997313;
  constexpr i64 expectedCycles = 3128157;
  i64 u=0, w=0, steps=0;

  // Reproduce the finite blank-root prefix to the start of the pump.
  while (!(u==0 && w==targetW)) {
    Step s=next(u,w);
    if (s.tag==Tag::Halt) {
      std::cerr << "unexpected halt before target at step " << steps
                << " state=" << u << "," << w << "\n";
      return 1;
    }
    u=s.u; w=s.w; ++steps;
    if (steps > expectedPrefix) {
      std::cerr << "target state not reached at expected prefix\n";
      return 1;
    }
  }
  if (steps != expectedPrefix) {
    std::cerr << "prefix step mismatch: " << steps << "\n";
    return 1;
  }

  const i64 startW=w;
  // Check every transition in the 3,128,157-cycle F^26 Eodd phase.
  for (i64 cycle=0; cycle<expectedCycles; ++cycle) {
    if (u!=0 || w<402653100 || w>805306272 || w%4!=0) {
      std::cerr << "macro precondition failure at cycle " << cycle
                << " state=" << u << "," << w << "\n";
      return 1;
    }
    for (int j=0; j<26; ++j) {
      Step s=next(u,w);
      if (s.tag!=Tag::F) {
        std::cerr << "expected F at cycle " << cycle << " offset " << j
                  << " got " << name(s.tag) << "\n";
        return 1;
      }
      u=s.u; w=s.w; ++steps;
    }
    Step s=next(u,w);
    if (s.tag!=Tag::Eodd) {
      std::cerr << "expected Eodd at cycle " << cycle << " got " << name(s.tag)
                << " state=" << u << "," << w << "\n";
      return 1;
    }
    u=s.u; w=s.w; ++steps;
    if (u!=0 || w!=startW+88*(cycle+1)) {
      std::cerr << "return mismatch at cycle " << cycle
                << " state=" << u << "," << w << "\n";
      return 1;
    }
  }
  if (w!=targetEndW || steps!=234457552) {
    std::cerr << "final mismatch state=" << u << "," << w
              << " steps=" << steps << "\n";
    return 1;
  }
  std::cout << "prefix: (0,0) -> (0," << startW << ") in "
            << expectedPrefix << " steps\n";
  std::cout << "verified cycles: " << expectedCycles
            << " x (F^26 Eodd), each 27 steps, W += 88\n";
  std::cout << "final: (0," << w << ") at step " << steps << "\n";
}
