#include <gmpxx.h>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>

// Independent GMP reimplementation of the r=5 cancellation-feeder parent audit.
// No floating point is used. Compile with: g++ -O3 r5_cancellation_parent_reaudit.cpp -lgmpxx -lgmp -o r5_audit

static std::vector<int> primes_up_to(int n) {
  std::vector<bool> sieve(n + 1, true); sieve[0] = sieve[1] = false;
  for (int p = 2; p * p <= n; ++p) if (sieve[p])
    for (int q = p * p; q <= n; q += p) sieve[q] = false;
  std::vector<int> out; for (int p = 2; p <= n; ++p) if (sieve[p]) out.push_back(p);
  return out;
}

int main() {
  using namespace std;
  auto start = chrono::steady_clock::now();
  constexpr uint64_t r = 5, nine = 59049, v = (nine + 3) / 2, K = r * (nine + 5) - 1;
  mpz_class twoK, twoV, den, bias;
  mpz_setbit(twoK.get_mpz_t(), K); mpz_setbit(twoV.get_mpz_t(), v);
  mpz_setbit(den.get_mpz_t(), v + 1); den += 3;
  bias = 3 * twoV + v + 3;
  mpz_class q, rem, numerator = twoK - bias;
  mpz_fdiv_qr(q.get_mpz_t(), rem.get_mpz_t(), numerator.get_mpz_t(), den.get_mpz_t());
  if (rem != 0 || q < 0) return 2;
  mpz_class x = twoV * (2 * q + 3);
  if (mpz_sizeinbase(x.get_mpz_t(), 2) != K || x >= twoK) return 3;
  mpz_class N0 = 2 * x + 3;

  // If p | (2^(u+1)+3), then 2^(u+1) == -3 (mod p).
  // A witness rejects u when additionally p does not divide N_u=2x+3-2u.
  std::vector<int> witness(K + 1, -1); int useful = 0;
  for (int p : primes_up_to(10000)) {
    if (p <= 3) continue;
    int z = 1, e = -1, order = -1;
    for (int j = 1; j < p; ++j) {
      z = (2 * z) % p;
      if (z == p - 3 && e < 0) e = j;
      if (z == 1) { order = j; break; }
    }
    if (order < 0 || e < 0) continue;
    ++useful;
    const int u0 = (e - 1) % order;
    const int xp = mpz_fdiv_ui(x.get_mpz_t(), p);
    for (int u = u0; u <= (int)K; u += order) {
      if (witness[u] < 0 && ((2 * xp + 3 - 2 * (u % p)) % p + p) % p != 0)
        witness[u] = p;
    }
  }

  uint64_t badLow = 0, badHigh = 0, lowChecks = 0, highChecks = 0;
  uint64_t lowDivisible = 0, highDivisible = 0; unsigned maxDigits = 0;
  std::vector<int> highSurvivors;
  for (uint64_t u = 0; u <= K; ++u) if (witness[u] >= 0) {
    if (u <= v) ++badLow; else ++badHigh;
  }
  // Low valuations are checked by exact integer division.
  for (uint64_t u = 0; u <= v; ++u) if (witness[u] < 0) {
    mpz_class N = N0 - 2 * u, D; mpz_setbit(D.get_mpz_t(), u + 1); D += 3;
    mpz_class rr; mpz_mod(rr.get_mpz_t(), N.get_mpz_t(), D.get_mpz_t());
    ++lowChecks; if (rr == 0) ++lowDivisible;
  }

  // For u>v, expand N in base B=2^(u+1). Since B == -3 (mod B+3),
  // S=sum_i d_i*(-3)^i is congruent to N. There are <=10 digits and
  // |S|<B*3^10; since 3^11<B, D|S iff |S|=floor(|S|/B)*(B+3).
  std::vector<mpz_class> coeff(10); coeff[0] = 1;
  for (int i = 1; i < 10; ++i) coeff[i] = -3 * coeff[i - 1];
  for (uint64_t u = v + 1; u <= K; ++u) if (witness[u] < 0) {
    mpz_class N = N0 - 2 * u, B; mpz_setbit(B.get_mpz_t(), u + 1);
    mpz_class mask = B - 1, t = N, S = 0, digit; unsigned digits = 0;
    while (t > 0) {
      mpz_and(digit.get_mpz_t(), t.get_mpz_t(), mask.get_mpz_t());
      S += digit * coeff[digits];
      mpz_fdiv_q_2exp(t.get_mpz_t(), t.get_mpz_t(), u + 1);
      if (++digits > 10) return 4;
    }
    maxDigits = std::max(maxDigits, digits);
    mpz_class absS = S < 0 ? -S : S, quotient;
    mpz_fdiv_q_2exp(quotient.get_mpz_t(), absS.get_mpz_t(), u + 1);
    mpz_class D = B + 3; ++highChecks;
    if (absS == quotient * D) ++highDivisible; else highSurvivors.push_back((int)u);
  }
  if (lowDivisible || highDivisible || maxDigits > 10) return 5;
  // Direct-division cross-check at deterministic points in the high survivor set.
  if (!highSurvivors.empty()) {
    const size_t n = highSurvivors.size();
    for (size_t i : {size_t(0), n/7, n/5, n/3, n/2, 2*n/3, 4*n/5, 6*n/7, n-1}) {
      uint64_t u = highSurvivors[i]; mpz_class N = N0 - 2*u, D;
      mpz_setbit(D.get_mpz_t(), u + 1); D += 3;
      mpz_class rr; mpz_mod(rr.get_mpz_t(), N.get_mpz_t(), D.get_mpz_t());
      if (rr == 0) return 6;
    }
  }
  cout << "K=" << K << " v=" << v << " qbits=" << mpz_sizeinbase(q.get_mpz_t(), 2)
       << " xbits=" << mpz_sizeinbase(x.get_mpz_t(), 2) << "\n";
  cout << "primes=" << primes_up_to(10000).size() << " useful=" << useful
       << " modular_rejections=" << badLow + badHigh << " (low=" << badLow
       << ", high=" << badHigh << ")\n";
  cout << "low_checks=" << lowChecks << " low_divisible=" << lowDivisible
       << " high_checks=" << highChecks << " high_divisible=" << highDivisible
       << " high_survivors=" << highSurvivors.size() << " max_digits=" << maxDigits << "\n";
  cout << "seconds=" << chrono::duration<double>(chrono::steady_clock::now() - start).count() << "\n";
  return 0;
}