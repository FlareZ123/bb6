// Reproducible *experimental* blank-run exposure scan for six-state, two-symbol
// partial transition tables. A '-' action stops at the first undefined query.
// This program does not certify nonhalting when the cutoff is reached.
#include <algorithm>
#include <cstdlib>
#include <deque>
#include <iostream>
#include <stdexcept>
#include <string>

int main(int argc, char** argv) {
  if (argc < 2 || argc > 3) {
    std::cerr << "usage: exposure_scan MACHINE_TABLE [MAX_STEPS=100000000]\n";
    return 2;
  }
  std::string table = argv[1];
  table.erase(std::remove(table.begin(), table.end(), '_'), table.end());
  if (table.size() != 36) throw std::runtime_error("expected 12 three-byte transitions");
  const unsigned long long cap = argc == 3 ? std::stoull(argv[2]) : 100000000ULL;
  std::deque<char> left, right;
  unsigned q = 0;
  for (unsigned long long t = 0; t <= cap; ++t) {
    const char scanned = left.empty() ? '0' : left.front();
    if (scanned != '0' && scanned != '1') throw std::runtime_error("invalid symbol");
    const unsigned slot = 2*q + (scanned-'0');
    const std::string mv = table.substr(3*slot, 3);
    if (mv == "---") {
      std::cout << "UNDEFINED t=" << t << " slot=" << char('A'+q) << scanned
                << " left=" << left.size() << " right=" << right.size() << '\n';
      return 0;
    }
    if (t == cap) break;
    if ((mv[0]!='0' && mv[0]!='1') || (mv[1]!='L' && mv[1]!='R') || mv[2]<'A' || mv[2]>'F')
      throw std::runtime_error("invalid transition");
    if (!left.empty()) left.pop_front();
    if (mv[1] == 'L') right.push_front(mv[0]);
    else {
      const char next = right.empty() ? '0' : right.front();
      if (!right.empty()) right.pop_front();
      left.push_front(mv[0]);
      left.push_front(next);
    }
    q = mv[2]-'A';
  }
  std::cout << "CUTOFF t=" << cap << " state=" << char('A'+q)
            << " left=" << left.size() << " right=" << right.size() << '\n';
}
