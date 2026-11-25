// Exhaustive small-range check of the formally proved wider reverse-block
// quotient window. This is not the full BB(6) scan or a performance benchmark.
//
// For every q<=96, k<=8 satisfying 2^(k+1)<=q+k, every endpoint z,
// every k-bit block word y, and both strict modes, compare the two-candidate
// wide search against enumeration of all B<2^k. Also compare the legacy
// floor(X/q), floor(X/q)-1 search whenever k*2^k<=q.

#include <cstdint>
#include <iostream>

using U = uint64_t;

static inline U digitWeight(U b) {
    return (b & 0xAAAAAAAAAAAAAAAAull)
         + 2 * (b & 0xCCCCCCCCCCCCCCCCull)
         + 4 * (b & 0xF0F0F0F0F0F0F0F0ull)
         + 8 * (b & 0xFF00FF00FF00FF00ull)
         + 16 * (b & 0xFFFF0000FFFF0000ull)
         + 32 * (b & 0xFFFFFFFF00000000ull);
}

static U corr(int k, U b) {
    return k == 0 ? 0 : 2 * corr(k - 1, b / 2) + U(k) * (b % 2);
}

static int wideParent(int q, int k, int z, U y, bool strict) {
    const U F = U(q) + U(k);
    const U X = (U(z) << k) + y;
    U b = X / F;
    const U maxB = (U(1) << k) - 1;
    for (int i = 0; i < 2; ++i, ++b) {
        if (b <= maxB) {
            const U f = U(q) * b + digitWeight(b);
            if (f <= X) {
                const U c = X - f;
                if (strict ? (c >= 1 && c + 3 <= U(q)) : c < U(q))
                    return int(c);
            }
        }
    }
    return -1;
}

static int oldParent(int q, int k, int z, U y, bool strict) {
    const U X = (U(z) << k) + y;
    U b = X / U(q);
    const U maxB = (U(1) << k) - 1;
    for (int i = 0; i < 2; ++i) {
        if (b <= maxB) {
            const U f = U(q) * b + digitWeight(b);
            if (f <= X) {
                const U c = X - f;
                if (strict ? (c >= 1 && c + 3 <= U(q)) : c < U(q))
                    return int(c);
            }
        }
        if (b == 0) break;
        --b;
    }
    return -1;
}

static int bruteParent(int q, int k, int z, U y, bool strict) {
    const U F = U(q) + U(k);
    const U X = (U(z) << k) + y;
    const U maxB = (U(1) << k) - 1;
    for (U B = 0; B <= maxB; ++B) {
        const U lhs = X + corr(k, B);
        if (lhs < F * B) continue;
        const U r = lhs - F * B;
        if (r < U(q) && (!strict || (r >= 1 && r + 3 <= U(q))))
            return int(r);
    }
    return -1;
}

int main() {
    uint64_t cases = 0, oldOverlapCases = 0, widerOnlyCases = 0;
    for (int q = 1; q <= 96; ++q) {
        for (int k = 1; k <= 8; ++k) {
            const bool wideFit = (U(1) << (k + 1)) <= U(q + k);
            const bool oldFit = U(k) * (U(1) << k) <= U(q);
            if (!wideFit) continue;
            for (int z = 0; z < q + k; ++z) {
                for (U y = 0; y < (U(1) << k); ++y) {
                    for (bool strict : {false, true}) {
                        const int brute = bruteParent(q, k, z, y, strict);
                        const int wide = wideParent(q, k, z, y, strict);
                        if (brute != wide) {
                            std::cerr << "wide mismatch q=" << q << " k=" << k
                                      << " z=" << z << " y=" << y
                                      << " strict=" << strict << " brute=" << brute
                                      << " wide=" << wide << "\n";
                            return 1;
                        }
                        ++cases;
                        if (oldFit) {
                            const int old = oldParent(q, k, z, y, strict);
                            if (old != brute) {
                                std::cerr << "old mismatch q=" << q << " k=" << k
                                          << " z=" << z << " y=" << y
                                          << " strict=" << strict << " brute=" << brute
                                          << " old=" << old << "\n";
                                return 1;
                            }
                            ++oldOverlapCases;
                        } else {
                            ++widerOnlyCases;
                        }
                    }
                }
            }
        }
    }

    std::cout << "PASS wide cases=" << cases
              << " old-overlap cases=" << oldOverlapCases
              << " wider-only cases=" << widerOnlyCases << "\n";

    for (U F : {U(4000000), U(68000000)}) {
        int oldK = 0, wideCappedK = 0, wideTheoreticalK = 0;
        for (int k = 1; k < 63; ++k) {
            if (U(k) * (U(1) << k) <= F - U(k)) oldK = k;
            if (k < 25 && (U(1) << (k + 1)) <= F) wideCappedK = k;
            if ((U(1) << (k + 1)) <= F) wideTheoreticalK = k;
        }
        std::cout << "F=" << F << " old_k=" << oldK
                  << " wide_k_with_current_cap24=" << wideCappedK
                  << " wide_k_without_cap=" << wideTheoreticalK << "\n";
    }
}
