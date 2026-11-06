// Independent C++17 full-state bitmask BFS for the D E-boundary marker.
// Compile as a normal C++17 translation unit and run without arguments.
// It proves finite closure at right-window radius seven by explicit state
// enumeration, using a separate representation from abstract_e_seam.py.
#include <cstdint>
#include <iostream>
#include <queue>
#include <stdexcept>
#include <unordered_set>
#include <vector>

struct Rule {
  int write, move, next;
};
constexpr Rule rules[6][2] = {
    {{1, 1, 1}, {0, 1, 4}},  {{1, -1, 2}, {0, 1, 0}},
    {{1, -1, 0}, {1, -1, 3}}, {{1, -1, 2}, {1, -1, 5}},
    {{0, -1, 2}, {0, -1, 1}}, {{1, -1, 4}, {0, 0, -1}}
};

void audit(int m, int radius) {
  std::vector<int> left = {0, 0};
  for (int i = 0; i < m; ++i) {
    left.push_back(1);
    left.push_back(0);
  }
  left.push_back(1);
  left.push_back(1);
  const int low = -static_cast<int>(left.size()), marker = low + 1;
  if (radius - low + 1 > 54 || radius - low >= 32) {
    throw std::runtime_error("packed-state range exceeded");
  }
  std::uint64_t base = 0;
  for (int j = 0; j < static_cast<int>(left.size()); ++j) {
    const int cell = -j - 1;
    if (left[j]) base |= std::uint64_t(1) << (cell - low);
  }
  const auto pack = [low](int head, int state, std::uint64_t bits) {
    return (bits << 8) | (std::uint64_t(head - low) << 3)
           | std::uint64_t(state);
  };
  const auto headOf = [low](std::uint64_t key) {
    return int((key >> 3) & 31) + low;
  };
  const auto stateOf = [](std::uint64_t key) { return int(key & 7); };
  const auto tapeOf = [](std::uint64_t key) { return key >> 8; };

  std::unordered_set<std::uint64_t> seen;
  std::queue<std::uint64_t> work;
  for (unsigned right = 0; right < (1U << radius); ++right) {
    const auto start = pack(0, 4, base | (std::uint64_t(right) << (1 - low)));
    if (seen.insert(start).second) work.push(start);
  }
  std::uint64_t transitions = 0;
  int firstMarkerStates = 0;
  while (!work.empty()) {
    const auto key = work.front();
    work.pop();
    const int head = headOf(key), state = stateOf(key);
    const auto bits = tapeOf(key);
    const int scanned = int((bits >> (head - low)) & 1);
    if (head == marker) {
      if (state != 2 || scanned != 1) {
        throw std::runtime_error("forbidden marker entry");
      }
      ++firstMarkerStates;
      continue;
    }
    if (state == 5 && scanned) continue;
    if (state == 5 && !scanned
        && (bits & ((std::uint64_t(1) << (head - low)) - 1)) == 0) {
      continue;
    }
    const Rule instruction = rules[state][scanned];
    if (instruction.next < 0) {
      throw std::runtime_error("unexpected undefined entry");
    }
    const auto cellMask = std::uint64_t(1) << (head - low);
    const auto newBits = instruction.write
        ? bits | cellMask : bits & ~cellMask;
    const int newHead = head + instruction.move;
    if (newHead < low) throw std::runtime_error("crossed marker");
    const int possibilities = (newHead > radius) ? 6 : 1;
    for (int stateChoice = 0; stateChoice < possibilities; ++stateChoice) {
      const auto successor = (newHead > radius)
          ? pack(radius, stateChoice, newBits)
          : pack(newHead, instruction.next, newBits);
      ++transitions;
      if (seen.insert(successor).second) work.push(successor);
    }
  }
  std::cout << "m=" << m << " radius=" << radius
            << " reachable=" << seen.size()
            << " firstMarkerStates=" << firstMarkerStates
            << " transitions=" << transitions << "\n";
}

int main() {
  audit(3, 7);
  audit(7, 7);
}
