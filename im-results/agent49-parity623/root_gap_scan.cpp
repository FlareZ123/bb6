#include <boost/multiprecision/cpp_int.hpp>
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <optional>
#include <string>
#include <utility>
using boost::multiprecision::cpp_int;

struct State { cpp_int a, d; };
struct Eval { cpp_int a, b, d; };

static inline bool odd(const cpp_int& x) { return static_cast<bool>(x & 1); }

std::optional<Eval> evalA(cpp_int a, cpp_int k, cpp_int m) {
    while (true) {
        int digit = static_cast<int>((k % 3).convert_to<unsigned>());
        cpp_int q = k / 3;
        if (digit == 2) return Eval{a + 1, q, m};
        if (a == 0) {
            if (digit == 0) return std::nullopt;
            return Eval{cpp_int(0), q, m};
        }
        if (digit == 0) return Eval{a - 1, q, m + 2};
        a -= 1;
        m += 2 * q + 3;
        k = q;
    }
}

std::optional<State> drainB(cpp_int a, cpp_int b, cpp_int d) {
    while (b > 0) {
        auto e = evalA(a, b - 1, d + 2 * b + 3);
        if (!e || e->b >= b) return std::nullopt;
        a = e->a;
        b = e->b;
        d = e->d;
    }
    return State{a, d};
}

std::optional<State> next(const State& s) {
    const cpp_int& a = s.a;
    const cpp_int& d = s.d;
    if (a == 0) {
        if (odd(d)) return drainB(d + 1, 2, 2);
        return State{d, 7};
    }
    if (odd(d) && a >= d + 5) return drainB(a - d - 5, d + 3, 5);
    if (!odd(d) && a >= d + 3) return drainB(a - d - 2, d + 2, 2);
    if (odd(a)) return std::nullopt;
    if (a == d + 2) return drainB(0, a, 2);
    if (odd(d)) return drainB(d + 4 - a, a - 1, 3);
    auto e = evalA(d + 1 - a, a, 2 * a + 5);
    if (!e) return std::nullopt;
    return drainB(e->a, e->b, e->d);
}

unsigned bitLength(const cpp_int& x) {
    if (x == 0) return 0;
    return boost::multiprecision::msb(x) + 1;
}

struct Best {
    bool set = false;
    cpp_int num = 0, den = 1;
    std::uint64_t i = 0;
    cpp_int a = 0, d = 0, gap = 0, scale = 0;
    std::string sector;
};

void update(Best& best, const cpp_int& gap, const cpp_int& scale,
            std::uint64_t i, const State& s, const std::string& sector) {
    cpp_int num = gap * gap;
    if (!best.set || num * best.den < best.num * scale) {
        best.set = true;
        best.num = num;
        best.den = scale;
        best.i = i;
        best.a = s.a;
        best.d = s.d;
        best.gap = gap;
        best.scale = scale;
        best.sector = sector;
    }
}

int main(int argc, char** argv) {
    std::uint64_t steps = 20000;
    if (argc > 1) steps = std::stoull(argv[1]);
    State s{0, 7};
    Best canAll, oldAll, canTail, oldTail;
    std::uint64_t maxBitDiff = 0, maxBitIndex = 0;
    for (std::uint64_t i = 0; i <= steps; ++i) {
        if (i >= 9) {
            std::string sector;
            cpp_int canGap, oldGap, scale;
            if (odd(s.d) && s.a >= s.d + 5) {
                sector = "LO";
                canGap = s.a - 4 * s.d;
                oldGap = canGap - 9;
                scale = s.d;
                if (s.a - s.d - 5 < bitLength(s.d + 3) + 2)
                    { std::cerr << "cone budget fail at " << i << "\n"; return 2; }
            } else if (!odd(s.d) && s.a >= s.d + 3) {
                sector = "LE";
                canGap = s.a - 4 * s.d;
                oldGap = canGap - 5;
                scale = s.d;
                if (s.a - s.d - 2 < bitLength(s.d + 2) + 2)
                    { std::cerr << "cone budget fail at " << i << "\n"; return 2; }
            } else if (s.a > 0 && !odd(s.a) && s.a <= s.d && odd(s.d)) {
                sector = "RO";
                canGap = s.d - 4 * s.a;
                oldGap = (canGap - 1) / 2;
                scale = s.a;
                if (s.d + 4 - s.a < bitLength(s.a - 1) + 2)
                    { std::cerr << "cone budget fail at " << i << "\n"; return 2; }
            } else if (s.a > 0 && !odd(s.a) && s.a <= s.d && !odd(s.d)) {
                sector = "RE";
                canGap = s.d - 4 * s.a;
                oldGap = (canGap - 2) / 2;
                scale = s.a;
                if (s.d + 1 - s.a < bitLength(s.a) + 2)
                    { std::cerr << "cone budget fail at " << i << "\n"; return 2; }
            } else {
                std::cerr << "sector fail at " << i << "\n";
                return 2;
            }
            if (canGap * canGap < 5 * scale) {
                std::cerr << "canonical gap bound fail at " << i << "\n";
                return 3;
            }
            if (oldGap * oldGap < 5 * scale) {
                std::cerr << "old gap bound fail at " << i << "\n";
                return 3;
            }
            update(canAll, canGap, scale, i, s, sector);
            update(oldAll, oldGap, scale, i, s, sector);
            if (i >= 16) {
                if (canGap * canGap < 17 * scale) {
                    std::cerr << "canonical tail >=17 fail at " << i << "\n";
                    return 3;
                }
                if (oldGap * oldGap < 22 * scale) {
                    std::cerr << "old tail >=22 fail at " << i << "\n";
                    return 3;
                }
                update(canTail, canGap, scale, i, s, sector);
                update(oldTail, oldGap, scale, i, s, sector);
            }
        }
        if (i == steps) break;
        auto n = next(s);
        if (!n) {
            std::cerr << "halt at transition " << i << "\n";
            return 4;
        }
        auto diff = bitLength(n->a) > bitLength(n->d)
            ? bitLength(n->a) - bitLength(n->d)
            : bitLength(n->d) - bitLength(n->a);
        if (diff > maxBitDiff) { maxBitDiff = diff; maxBitIndex = i + 1; }
        s = std::move(*n);
    }
    auto show = [](const char* name, const Best& b) {
        std::cout << name << "=" << b.num << "/" << b.den
                  << " index=" << b.i << " sector=" << b.sector
                  << " gap=" << b.gap << " scale=" << b.scale
                  << " a_bits=" << bitLength(b.a)
                  << " d_bits=" << bitLength(b.d) << "\n";
    };
    std::cout << "states=" << (steps + 1) << " checked=9.." << steps << "\n";
    show("canonical_min", canAll);
    show("old_ray_min", oldAll);
    show("canonical_tail_min", canTail);
    show("old_ray_tail_min", oldTail);
    std::cout << "max_coordinate_bitlength_difference=" << maxBitDiff
              << " at_index=" << maxBitIndex << "\n";
}
