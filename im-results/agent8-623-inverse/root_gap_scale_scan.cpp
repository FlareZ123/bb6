#include <gmpxx.h>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <limits>

static inline bool odd(const mpz_class& x) {
  return mpz_odd_p(x.get_mpz_t()) != 0;
}

bool evalA(mpz_class& a, mpz_class& k, mpz_class& m) {
  while (true) {
    mpz_class q = k / 3;
    unsigned r = mpz_fdiv_ui(k.get_mpz_t(), 3);
    if (r == 2) {
      a += 1;
      k = q;
      return true;
    }
    if (a == 0) {
      if (r == 0) return false;
      k = q;
      return true;
    }
    if (r == 0) {
      a -= 1;
      k = q;
      m += 2;
      return true;
    }
    a -= 1;
    m += 2 * q + 3;
    k = q;
  }
}

bool drainB(mpz_class& a, mpz_class& b, mpz_class& d) {
  while (b > 0) {
    mpz_class oldb = b;
    mpz_class k = b - 1;
    mpz_class m = d + 2 * b + 3;
    if (!evalA(a, k, m)) return false;
    b = k;
    d = m;
    if (b >= oldb) return false;
  }
  return true;
}

bool nextState(mpz_class& a, mpz_class& d) {
  if (a == 0) {
    if (odd(d)) {
      mpz_class aa = d + 1, bb = 2, dd = 2;
      if (!drainB(aa, bb, dd)) return false;
      a = aa;
      d = dd;
      return true;
    }
    a = d;
    d = 7;
    return true;
  }
  if (odd(d) && a >= d + 5) {
    mpz_class aa = a - d - 5, bb = d + 3, dd = 5;
    if (!drainB(aa, bb, dd)) return false;
    a = aa;
    d = dd;
    return true;
  }
  if (!odd(d) && a >= d + 3) {
    mpz_class aa = a - d - 2, bb = d + 2, dd = 2;
    if (!drainB(aa, bb, dd)) return false;
    a = aa;
    d = dd;
    return true;
  }
  if (odd(a)) return false;
  if (a == d + 2) {
    mpz_class aa = 0, bb = a, dd = 2;
    if (!drainB(aa, bb, dd)) return false;
    a = aa;
    d = dd;
    return true;
  }
  if (odd(d)) {
    mpz_class aa = d + 4 - a, bb = a - 1, dd = 3;
    if (!drainB(aa, bb, dd)) return false;
    a = aa;
    d = dd;
    return true;
  }
  mpz_class aa = d + 1 - a, kk = a, mm = 2 * a + 5;
  if (!evalA(aa, kk, mm)) return false;
  mpz_class bb = kk, dd = mm;
  if (!drainB(aa, bb, dd)) return false;
  a = aa;
  d = dd;
  return true;
}

long double log2abs(const mpz_class& x) {
  if (x == 0) return -std::numeric_limits<long double>::infinity();
  mpz_class z = x < 0 ? -x : x;
  mp_exp_t e = 0;
  double m = mpz_get_d_2exp(&e, z.get_mpz_t());
  return static_cast<long double>(e) + std::log2(static_cast<long double>(m));
}

int main(int argc, char** argv) {
  uint64_t steps = argc > 1 ? std::stoull(argv[1]) : 20000;
  mpz_class a = 0, d = 7;
  long double max_eg_n = -1e99L, max_em_n = -1e99L;
  long double min_rel = 1e99L, min_sq = 1e99L;
  uint64_t i_eg = 0, i_em = 0, i_rel = 0, i_sq = 0;
  mpz_class eg_at, em_at, eg_m, em_m;
  uint64_t mismatch = 0, zero = 0;

  for (uint64_t i = 0; i < steps; ++i) {
    mpz_class olda = a, oldd = d;
    if (!nextState(a, d)) {
      std::cout << "HALT " << i << "\n";
      return 0;
    }
    if (i < 9) continue;

    mpz_class m, g, mn, gn;
    if (olda >= oldd) {
      m = oldd;
      g = olda - 4 * oldd;
    } else {
      m = olda;
      g = oldd - 4 * olda;
    }
    if (a >= d) {
      mn = d;
      gn = a - 4 * d;
    } else {
      mn = a;
      gn = d - 4 * a;
    }

    if (g == 0) ++zero;
    mpz_class pg, pm;
    if (g > 0) {
      pg = g - 9 * m;
      pm = 3 * m;
    } else {
      pg = -4 * g - 9 * m;
      pm = 3 * m + g;
    }
    mpz_class eg = gn - pg, em = mn - pm;
    unsigned n = mpz_sizeinbase(m.get_mpz_t(), 3);
    if (n == 0) n = 1;

    long double leg = log2abs(eg) - std::log2(static_cast<long double>(n));
    long double lem = log2abs(em) - std::log2(static_cast<long double>(n));
    if (leg > max_eg_n) {
      max_eg_n = leg;
      i_eg = i;
      eg_at = eg;
      eg_m = m;
    }
    if (lem > max_em_n) {
      max_em_n = lem;
      i_em = i;
      em_at = em;
      em_m = m;
    }

    long double lr = log2abs(g) - log2abs(m);
    if (lr < min_rel) {
      min_rel = lr;
      i_rel = i;
    }
    long double ls = 2 * log2abs(g) - log2abs(m);
    if (ls < min_sq) {
      min_sq = ls;
      i_sq = i;
    }
    bool expectedLeft = g > 0;
    bool actualLeft = a >= d;
    if (expectedLeft != actualLeft) ++mismatch;
  }

  std::cout << "DONE steps=" << steps << " mismatch=" << mismatch
            << " zero=" << zero << "\n";
  std::cout << "max |eg|/ternaryDigits log2=" << static_cast<double>(max_eg_n)
            << " index=" << i_eg
            << " error_bits=" << mpz_sizeinbase(eg_at.get_mpz_t(), 2)
            << " m_bits=" << mpz_sizeinbase(eg_m.get_mpz_t(), 2) << "\n";
  std::cout << "max |em|/ternaryDigits log2=" << static_cast<double>(max_em_n)
            << " index=" << i_em
            << " error_bits=" << mpz_sizeinbase(em_at.get_mpz_t(), 2)
            << " m_bits=" << mpz_sizeinbase(em_m.get_mpz_t(), 2) << "\n";
  std::cout << "min |g|/m log2=" << static_cast<double>(min_rel)
            << " index=" << i_rel << "\n";
  std::cout << "min g^2/m log2=" << static_cast<double>(min_sq)
            << " index=" << i_sq << "\n";
}
