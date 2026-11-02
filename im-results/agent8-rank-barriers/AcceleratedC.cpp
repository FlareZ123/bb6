// Exact accelerated transition simulator for Cryptids' BB(6) machine
// 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC
// Compile: g++ -std=c++17 -O3 -Wall -Wextra AcceleratedC.cpp -o accelerated
// Usage: ./accelerated 1000000000000000000 1000000000000000000
// This is computational evidence; formal sweep proof is in Sweep.lean.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <string>

using u64 = std::uint64_t;
using u128 = unsigned __int128;

static u128 parse128(const char* p) {
  u128 n = 0;
  while (*p >= '0' && *p <= '9') n = 10 * n + (*p++ - '0');
  return n;
}

static std::string repr(u128 n) {
  std::string s;
  do {
    s.push_back(char('0' + n % 10));
    n /= 10;
  } while (n);
  std::reverse(s.begin(), s.end());
  return s;
}

int main(int argc, char** argv) {
  u64 a = 5, k = 0, c = 1;
  u128 n = 0;
  const u128 limit = argc > 1 ? parse128(argv[1]) : 1000000000ULL;
  const u128 interval = argc > 2 ? parse128(argv[2]) : 1000000000ULL;
  u128 checkpoint = interval;
  u64 events = 0, sweeps = 0;
  u64 critical_odd = 0, critical_even = 0, zero_zero = 0, zero_nonzero = 0;
  auto started = std::chrono::steady_clock::now();
  while (n < limit) {
    // All arithmetic is exact while this guard holds.
    if ((a | k | c) >= (1ULL << 60)) {
      std::printf("COUNTER_LIMIT n=%s a=%llu k=%llu c=%llu\n",
        repr(n).c_str(), (unsigned long long)a,
        (unsigned long long)k, (unsigned long long)c);
      return 2;
    }
    if (a == 0 && c == 5) {
      if (k & 1) ++critical_odd;
      else ++critical_even;
    }
    if (a == 0 && c == 0) {
      if (k == 0) ++zero_zero;
      else ++zero_nonzero;
    }
    if (c == 2) {
      std::printf("HALT n=%s a=%llu k=%llu c=%llu events=%llu sweeps=%llu\n",
        repr(n).c_str(), (unsigned long long)a, (unsigned long long)k,
        (unsigned long long)c, (unsigned long long)events, (unsigned long long)sweeps);
      return 0;
    }
    if (c >= 4 && a > 0) {
      u64 q = std::min(a, c - 3);
      if (limit - n < q) q = (u64)(limit - n);
      a -= q;
      k += q;
      c -= q;
      n += q;
      ++sweeps;
    } else {
      if (c == 1) {
        ++k;
        c = 0;
      } else if (c == 3) {
        k += 2;
        c = 1;
      } else if (c == 0) {
        if (a == 0) {
          a = 1;
          c = 2 * k + 2;
          k = 0;
        } else if (a == 1) {
          if (k == 0) {
            a = 5;
            c = 1;
          } else {
            a = 2;
            c = 2 * k - 1;
            k = 2;
          }
        } else {
          a -= 2;
          c = 2 * k + 1;
          k = 1;
        }
      } else { // c >= 4 and a == 0
        if ((k & 1) == 0) {
          a = 2 * k + 2;
          k = 2;
          c -= 3;
        } else {
          a = 2 * k + 3;
          k = 0;
        }
      }
      ++n;
      ++events;
    }
    if (interval && n >= checkpoint) {
      double elapsed = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - started).count();
      std::printf("CHECK n=%s a=%llu k=%llu c=%llu events=%llu sweeps=%llu sec=%.3f\n",
        repr(n).c_str(), (unsigned long long)a, (unsigned long long)k,
        (unsigned long long)c, (unsigned long long)events,
        (unsigned long long)sweeps, elapsed);
      std::fflush(stdout);
      checkpoint += interval;
    }
  }
  std::printf("NO_HALT_THROUGH n=%s a=%llu k=%llu c=%llu events=%llu sweeps=%llu\n",
    repr(n).c_str(), (unsigned long long)a, (unsigned long long)k,
    (unsigned long long)c, (unsigned long long)events, (unsigned long long)sweeps);
  std::printf("CRITICAL odd=%llu even=%llu zero_zero=%llu zero_nonzero=%llu\n",
    (unsigned long long)critical_odd, (unsigned long long)critical_even,
    (unsigned long long)zero_zero, (unsigned long long)zero_nonzero);
}
