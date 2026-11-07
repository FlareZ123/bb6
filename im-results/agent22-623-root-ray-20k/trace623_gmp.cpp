#include <gmpxx.h>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <limits>
#include <string>

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
  mpz_class aa = d + 1 - a;
  mpz_class kk = a;
  mpz_class mm = 2 * a + 5;
  if (!evalA(aa, kk, mm)) return false;
  mpz_class bb = kk, dd = mm;
  if (!drainB(aa, bb, dd)) return false;
  a = aa;
  d = dd;
  return true;
}

long double log2int(const mpz_class& x) {
  if (x == 0) return -std::numeric_limits<long double>::infinity();
  mpz_class z = x < 0 ? -x : x;
  mp_exp_t exponent = 0;
  double mantissa = mpz_get_d_2exp(&exponent, z.get_mpz_t());
  return static_cast<long double>(exponent) +
         std::log2(static_cast<long double>(mantissa));
}

int main(int argc, char** argv) {
  const uint64_t steps = argc > 1 ? std::stoull(argv[1]) : 20000;
  mpz_class a = 0, d = 7;
  long double min_log = std::numeric_limits<long double>::infinity();
  long double min_after_16 = min_log;
  uint64_t min_at = 0, min_after_16_at = 0;
  uint64_t old_count = 0, failed_square = 0;

  for (uint64_t i = 0; i < steps; ++i) {
    mpz_class gap, scale;
    bool old_ray = false;

    if (odd(d) && a >= 2 * d + 9) {
      gap = a - 4 * d - 9;
      scale = d;
      old_ray = true;
    } else if (!odd(d) && a >= 2 * d + 5) {
      gap = a - 4 * d - 5;
      scale = d;
      old_ray = true;
    } else if (odd(d) && d >= 2 * a + 1) {
      gap = d - 4 * a - 1;
      scale = 4 * a;
      old_ray = true;
    } else if (!odd(d) && d >= 2 * a + 2) {
      gap = d - 4 * a - 2;
      scale = 4 * a;
      old_ray = true;
    }

    if (old_ray) {
      ++old_count;
      mpz_class abs_gap = gap < 0 ? -gap : gap;
      if (abs_gap * abs_gap < scale) ++failed_square;
      if (abs_gap != 0 && scale != 0) {
        const long double ratio_log =
            2 * log2int(abs_gap) - log2int(scale);
        if (ratio_log < min_log) {
          min_log = ratio_log;
          min_at = i;
        }
        if (i >= 16 && ratio_log < min_after_16) {
          min_after_16 = ratio_log;
          min_after_16_at = i;
        }
      }
    }

    if (i % 10000 == 0) {
      std::cout << "i=" << i
                << " a_bits=" << mpz_sizeinbase(a.get_mpz_t(), 2)
                << " d_bits=" << mpz_sizeinbase(d.get_mpz_t(), 2)
                << " old=" << old_count
                << " failed_square=" << failed_square
                << " min_log2=" << static_cast<double>(min_log)
                << "@" << min_at
                << " min_after_16=" << static_cast<double>(min_after_16)
                << "@" << min_after_16_at << "\n";
    }

    if (!nextState(a, d)) {
      std::cout << "HALT at state index " << i << "\n";
      return 0;
    }
  }

  std::cout << "DONE steps=" << steps
            << " old=" << old_count
            << " failed_square=" << failed_square
            << " min_log2=" << static_cast<double>(min_log)
            << "@" << min_at
            << " min_after_16=" << static_cast<double>(min_after_16)
            << "@" << min_after_16_at
            << " final_a_bits=" << mpz_sizeinbase(a.get_mpz_t(), 2)
            << " final_d_bits=" << mpz_sizeinbase(d.get_mpz_t(), 2)
            << "\n";
}
