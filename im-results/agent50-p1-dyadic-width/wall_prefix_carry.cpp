// Exact 2-adic wall-prefix residue enumerator for n = 16*q + 2.
// For K >= 4, W_K(q) holds iff there is A subset {0,...,K-1}, 0 in A,
// with sum_{s in A} (16*q + 5 + s) * 2^s == 1 (mod 2^K).
//
// For S=sum 2^s and T=sum s*2^s, S is odd and
// 16*q == (1-T)*S^{-1} - 5 (mod 2^K).
// Enumerate every A by Gray code; Newton iteration computes S^{-1} modulo 2^K.
// This is exact integer arithmetic, not floating point.

#include <bits/stdc++.h>
using namespace std;

int main(int argc, char** argv) {
  if (argc < 2) {
    cerr << "usage: wall_prefix_carry K [threads] [--list]\n";
    return 2;
  }
  const int K = atoi(argv[1]);
  const int threads = argc >= 3 ? max(1, atoi(argv[2])) : 1;
  const bool emit_list = argc >= 4 && string(argv[3]) == "--list";
  if (K < 4 || K > 32) {
    cerr << "K must be in [4,32] for this build\n";
    return 2;
  }

  const uint64_t mod_mask = (1ULL << K) - 1;
  const uint64_t q_size = 1ULL << (K - 4);
  const uint64_t words = (q_size + 63) / 64;
  const uint64_t total = 1ULL << (K - 1);

  vector<vector<uint64_t>> local(threads, vector<uint64_t>(words, 0));
  vector<thread> workers;
  for (int tid = 0; tid < threads; ++tid) {
    const uint64_t lo = total * tid / threads;
    const uint64_t hi = total * (tid + 1) / threads;
    workers.emplace_back([&, tid, lo, hi]() {
      uint64_t gray = lo ^ (lo >> 1);
      uint64_t S = 1 + (gray << 1);
      uint64_t T = 0;
      for (uint64_t g = gray; g; g &= g - 1) {
        const int bit = __builtin_ctzll(g);
        const int s = bit + 1;
        T += (uint64_t)s * (1ULL << s);
      }
      uint64_t previous_gray = gray;
      auto& bits = local[tid];

      for (uint64_t i = lo; i < hi; ++i) {
        if (i > lo) {
          gray = i ^ (i >> 1);
          const uint64_t diff = gray ^ previous_gray;
          const int bit = __builtin_ctzll(diff);
          const int s = bit + 1;
          const uint64_t term = 1ULL << s;
          if (gray & diff) {
            S += term;
            T += (uint64_t)s * term;
          } else {
            S -= term;
            T -= (uint64_t)s * term;
          }
          previous_gray = gray;
        }

        // Newton: each iteration doubles the number of correct low bits.
        uint64_t inverse = 1;
        for (int precision = 1; precision < K; precision *= 2)
          inverse = (inverse * (2 - S * inverse)) & mod_mask;

        const uint64_t rhs = ((1 - T) * inverse - 5) & mod_mask;
        if ((rhs & 15) == 0) {
          const uint64_t q = rhs >> 4;
          bits[q >> 6] |= 1ULL << (q & 63);
        }
      }
    });
  }
  for (auto& worker : workers) worker.join();

  vector<uint64_t> seen(words, 0);
  uint64_t count = 0;
  for (uint64_t w = 0; w < words; ++w) {
    for (int tid = 0; tid < threads; ++tid)
      seen[w] |= local[tid][w];
    count += __builtin_popcountll(seen[w]);
  }

  cout << "K=" << K << " survivors=" << count
       << " modulus=" << q_size
       << " fraction=" << setprecision(15)
       << (double)count / (double)q_size << "\n";

  if (emit_list) {
    for (uint64_t q = 0; q < q_size; ++q)
      if ((seen[q >> 6] >> (q & 63)) & 1ULL)
        cout << q << "\n";
  }
}
