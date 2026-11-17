// Enumerate no-short selected-gap words and their unique initial residue.
//
// A word g_0,...,g_{k-1} has g_i >= 3 and total span G.  Its selected starts
// are s_0=0,...,s_{k-1}<G, with terminal s_k=G.  Put
//   S = sum_i 2^{s_i},  T = sum_i s_i 2^{s_i},  D = G*S-T,
//   Delta = 2^G - 7*S.
// The exact carry recurrence gives
//   2^G b_k = S*C_0 + T - 1,
//   2^G(C_k - 7*b_k) = Delta*(C_0+G) + 7(D+1),
// where C_k=C_0+G.  Requiring the final state to be extendable, i.e.
// 8 | C_k-7*b_k, fixes C_0 modulo 2^{G+3}; Delta is always odd:
//   C_0 = -G - 7(D+1)/Delta  (mod 2^{G+3}).
// We enumerate all compositions of G into parts >=3 and choose the least
// representative C_0 >=17 (for BB(6), C_0=n+3 with n>=14).
//
// This is exploratory finite computation, not a proof of a uniform bound.
// Output columns: G, word count, minimum C_0, residue, C_0/2^(G/2),
// minimizing gap word, and its final q_k=C_k-7*b_k.

#include <bits/stdc++.h>
using namespace std;
using u64 = uint64_t;

static u64 mask;
static u64 inv_odd_mod_2m(u64 a) {
  u64 x = 1;
  // Newton iteration doubles the number of correct low bits each round.
  for (int i = 0; i < 6; ++i) x *= 2 - a * x;
  return x & mask;
}

struct Best {
  u64 C0 = UINT64_MAX;
  u64 residue = 0;
  vector<int> gaps;
  u64 q_end = 0;
};

int main(int argc, char **argv) {
  int Gmin = argc > 2 ? atoi(argv[1]) : 3;
  int Gmax = argc > 2 ? atoi(argv[2]) : (argc > 1 ? atoi(argv[1]) : 57);
  if (Gmin < 3 || Gmax < Gmin || Gmax > 57) {
    cerr << "range must satisfy 3 <= Gmin <= Gmax <= 57.\n";
    return 2;
  }

  for (int G = Gmin; G <= Gmax; ++G) {
    const u64 twoG = 1ULL << G;
    mask = (1ULL << (G + 3)) - 1;
    Best best;
    u64 word_count = 0;
    vector<int> gaps;

    function<void(int, u64, u64)> visit = [&](int s, u64 S, u64 T) {
      for (int g = 3; g <= G - s; ++g) {
        const int next = s + g;
        gaps.push_back(g);
        if (next == G) {
          ++word_count;
          const u64 Delta = twoG - 7 * S;
          if (Delta == 0 || !(Delta & 1)) {
            cerr << "invalid Delta at G=" << G << "\n";
            exit(3);
          }
          const u64 D = (u64)G * S - T;
          const u64 rhs = (0ULL - Delta * (u64)G - 7ULL * (D + 1)) & mask;
          const u64 residue = (rhs * inv_odd_mod_2m(Delta)) & mask;
          // Any extendable no-short word starts in n == 14 (mod 16).
          if ((residue & 15ULL) != 1ULL) {
            cerr << "unexpected C_0 residue mod 16 at G=" << G << "\n";
            exit(4);
          }
          const u64 C0 = residue >= 17 ? residue : residue + (1ULL << (G + 3));
          if (C0 < best.C0) {
            best.C0 = C0;
            best.residue = residue;
            best.gaps = gaps;
          }
        } else {
          const u64 bit = 1ULL << next;
          visit(next, S + bit, T + (u64)next * bit);
        }
        gaps.pop_back();
      }
    };

    // Initial selected position s_0=0.
    visit(0, 1, 0);

    // Check the minimizing word directly through the integer recurrence.
    u64 C = best.C0;
    int64_t b = -1;
    for (int g : best.gaps) {
      const u64 numerator = C + (u64)b;
      if (numerator % (1ULL << g) != 0) {
        cerr << "integrality check failed at G=" << G << "\n";
        return 5;
      }
      b = (int64_t)(numerator >> g);
      C += (u64)g;
      const int64_t q = (int64_t)C - 7 * b;
      if (q <= 0 || q % 8 != 0) {
        cerr << "extendability check failed at G=" << G << "\n";
        return 6;
      }
      best.q_end = (u64)q;
    }

    cout << G << '\t' << word_count << '\t' << best.C0 << '\t'
         << best.residue << '\t'
         << setprecision(9) << fixed
         << (double)best.C0 / pow(2.0, G / 2.0) << '\t';
    for (size_t i = 0; i < best.gaps.size(); ++i) {
      if (i) cout << ',';
      cout << best.gaps[i];
    }
    cout << '\t' << best.q_end << '\n';
  }
}
