#include <bits/stdc++.h>
using namespace std;

struct Tr { int write, dir, next; bool halt = false; };

static const Tr T[6][2] = {
  {{1, 1, 1, false}, {0, -1, 4, false}}, // A
  {{0, 1, 2, false}, {1, 1, 2, false}},  // B
  {{0, 1, 3, false}, {1, -1, 0, false}}, // C
  {{1, -1, 3, false}, {0, -1, 0, false}},// D
  {{1, -1, 5, false}, {1, -1, 2, false}},// E
  {{0, 0, 0, true},  {0, -1, 0, false}} // F
};

// DFA for Danger(P) = P in (11[01])+.
// q0: block boundary; q1: saw first 1; q2: saw 11; q3: dead.
static int delta(int q, int b) {
  if (q == 0) return b ? 1 : 3;
  if (q == 1) return b ? 2 : 3;
  if (q == 2) return 0;
  return 3;
}

int main(int argc, char** argv) {
  uint64_t N = argc > 1 ? stoull(argv[1]) : 50000000ULL;
  uint64_t haltAt = UINT64_MAX;
  unordered_set<long long> ones;
  ones.reserve(100000);
  vector<int> prefix, dfa{0};
  long long head = 0, lo = 0, badPairs = 0;
  int state = 0;

  uint64_t A = 0, A1 = 0, A0 = 0;
  uint64_t d3A1 = 0, A1Danger = 0;
  uint64_t prefixBad = 0, firstBad = 0;
  uint64_t d0Current1 = 0, d0Right100 = 0, d1A0Right000 = 0;
  uint64_t d3A1Right1Zero = 0, d3A1PrefixNot101 = 0;
  uint64_t A0AppendDanger = 0, A0SameDanger = 0, A0DropDanger = 0;\n  uint64_t A1Pop2DropDanger = 0, A1Pop3_11AppendDanger = 0, A1Pop3_10SameDanger = 0;

  auto bit = [&](long long x) -> int { return (int)ones.count(x); };
  auto danger = [&]() -> bool {
    return !prefix.empty() && prefix.size() % 3 == 0 && dfa.back() == 0;
  };
  auto dangerAppend1 = [&]() -> bool {
    return (prefix.size() + 1) % 3 == 0 && dfa.back() == 2;
  };
  auto dangerDropLast = [&]() -> bool {
    return prefix.size() > 1 && (prefix.size() - 1) % 3 == 0
      && dfa[prefix.size() - 1] == 0;
  };

  for (uint64_t t = 0; t < N; ++t) {
    if (state == 0) {
      ++A;
      size_t d = prefix.size();
      int current = bit(head);
      int r1 = bit(head + 1), r2 = bit(head + 2), r3 = bit(head + 3);
      if (current) ++A1; else ++A0;

      if (d == 0) {
        if (current) ++d0Current1;
        if (r1 == 1 && r2 == 0 && r3 == 0) ++d0Right100;
      }
      if (d == 1 && !current && r1 == 0 && r2 == 0 && r3 == 0)
        ++d1A0Right000;

      if (current) {
        if (danger()) ++A1Danger;

        // A/1 pop-2: P = R ++ 101 with R dangerous, and r1=0
        // makes the successor violate the A/0 drop-last clause.
        if (d >= 6 && (d - 3) % 3 == 0 && dfa[d - 3] == 0
            && prefix[d - 3] == 1 && prefix[d - 2] == 0
            && prefix[d - 1] == 1 && r1 == 0)
          ++A1Pop2DropDanger;

        // A/1 pop-3 through suffix 011: P = R ++ 11011
        // makes the successor violate the A/0 append clause.
        if (d >= 8 && (d - 5) % 3 == 0 && dfa[d - 5] == 0
            && prefix[d - 5] == 1 && prefix[d - 4] == 1
            && prefix[d - 3] == 0 && prefix[d - 2] == 1
            && prefix[d - 1] == 1)
          ++A1Pop3_11AppendDanger;

        // A/1 pop-3 through suffix 010: P = R ++ 010
        // makes the successor violate the A/0 same-prefix clause.
        if (d >= 6 && (d - 3) % 3 == 0 && dfa[d - 3] == 0
            && prefix[d - 3] == 0 && prefix[d - 2] == 1
            && prefix[d - 1] == 0)
          ++A1Pop3_10SameDanger;
        if (d == 3) {
          ++d3A1;
          if (!r1) ++d3A1Right1Zero;
          if (!(prefix[0] == 1 && prefix[1] == 0 && prefix[2] == 1))
            ++d3A1PrefixNot101;
        }
      } else {
        // A/0 -> C/1: prefix becomes prefix ++ [1], head becomes r1.
        if (r1 == 1 && r2 == 1 && dangerAppend1()) ++A0AppendDanger;
        // A/0 -> C/0 -> D/1: prefix is unchanged, head returns to h.
        if (r1 == 1 && r2 == 0 && r3 == 0 && danger()) ++A0SameDanger;
        // A/0 -> C/0 -> D/0^*: prefix drops its last bit.
        if (r1 == 0 && r2 == 0 && r3 == 0 && !prefix.empty()
            && prefix.back() == 1 && dangerDropLast()) ++A0DropDanger;
      }

      if (badPairs != 0) ++prefixBad;
      if (d > 0 && prefix[0] != 1) ++firstBad;
    }

    int symbol = bit(head);
    Tr tr = T[state][symbol];
    if (tr.halt) { haltAt = t; break; }

    if (tr.dir == 1) {
      if (!prefix.empty() && prefix.back() == 0 && tr.write == 0)
        ++badPairs;
      prefix.push_back(tr.write);
      dfa.push_back(delta(dfa.back(), tr.write));
      if (tr.write) ones.insert(head); else ones.erase(head);
      ++head;
    } else if (tr.dir == -1) {
      if (!prefix.empty()) {
        int last = prefix.back();
        prefix.pop_back();
        dfa.pop_back();
        if (!prefix.empty() && prefix.back() == 0 && last == 0)
          --badPairs;
      } else {
        lo = head - 1;
      }
      if (tr.write) ones.insert(head); else ones.erase(head);
      --head;
      if (head < lo) {
        lo = head;
        prefix.clear();
        dfa.assign(1, 0);
        badPairs = 0;
      }
    }
    state = tr.next;
  }

  cout << "steps=" << N << " haltAt=";
  if (haltAt == UINT64_MAX) cout << "none"; else cout << haltAt;
  cout << " A=" << A << " A1=" << A1 << " A0=" << A0 << "\n";
  cout << "prefixBad=" << prefixBad << " firstBad=" << firstBad
       << " d0Current1=" << d0Current1 << " d0Right100=" << d0Right100
       << " d1A0Right000=" << d1A0Right000 << "\n";
  cout << "d3A1=" << d3A1 << " d3A1Right1Zero=" << d3A1Right1Zero
       << " d3A1PrefixNot101=" << d3A1PrefixNot101
       << " A1Danger=" << A1Danger << "\n";
  cout << "A0AppendDanger=" << A0AppendDanger
       << " A0SameDanger=" << A0SameDanger
       << " A0DropDanger=" << A0DropDanger << "\n";
  cout << "A1Pop2DropDanger=" << A1Pop2DropDanger
       << " A1Pop3_11AppendDanger=" << A1Pop3_11AppendDanger
       << " A1Pop3_10SameDanger=" << A1Pop3_10SameDanger << "\n";
}
