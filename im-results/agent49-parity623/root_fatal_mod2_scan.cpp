#include <boost/multiprecision/cpp_int.hpp>
#include <cstdint>
#include <iostream>
#include <map>
#include <optional>
#include <set>
#include <vector>

using boost::multiprecision::cpp_int;

struct State { cpp_int a, d; };
struct Eval { cpp_int a, b, d; };

static bool odd(const cpp_int& x) { return static_cast<bool>(x & 1); }

std::optional<Eval> evalA(cpp_int a, cpp_int k, cpp_int m) {
    while (true) {
        int r = (k % 3).convert_to<int>();
        cpp_int q = k / 3;
        if (r == 2) return Eval{a + 1, q, m};
        if (a == 0) {
            if (r == 0) return std::nullopt;
            return Eval{0, q, m};
        }
        if (r == 0) return Eval{a - 1, q, m + 2};
        a -= 1;
        m += 2 * q + 3;
        k = q;
    }
}

std::optional<State> drainB(cpp_int a, cpp_int b, cpp_int d) {
    while (b > 0) {
        auto p = evalA(a, b - 1, d + 2 * b + 3);
        if (!p || p->b >= b) return std::nullopt;
        a = p->a;
        b = p->b;
        d = p->d;
    }
    return State{a, d};
}

std::optional<State> next(const State& s) {
    const auto& a = s.a;
    const auto& d = s.d;
    if (a == 0) {
        if (odd(d)) return drainB(d + 1, 2, 2);
        return State{d, 7};
    }
    if (odd(d) && a >= d + 5) return drainB(a - d - 5, d + 3, 5);
    if (!odd(d) && a >= d + 3) return drainB(a - d - 2, d + 2, 2);
    if (odd(a)) return std::nullopt;
    if (a == d + 2) return drainB(0, a, 2);
    if (odd(d)) return drainB(d + 4 - a, a - 1, 3);
    auto p = evalA(d + 1 - a, a, 2 * a + 5);
    if (!p) return std::nullopt;
    return drainB(p->a, p->b, p->d);
}

std::uint64_t powmod(std::uint64_t a, std::uint64_t e, std::uint64_t mod) {
    std::uint64_t r = 1;
    while (e) {
        if (e & 1) r = static_cast<__uint128_t>(r) * a % mod;
        a = static_cast<__uint128_t>(a) * a % mod;
        e >>= 1;
    }
    return r;
}

struct KData {
    unsigned k;
    std::uint64_t mod;
    std::set<std::pair<std::uint64_t, std::uint64_t>> pairs;
    std::map<std::pair<std::uint64_t, std::uint64_t>, std::uint64_t> pByPair;
    std::uint64_t count = 0, first = 0, firstP = 0;
};

int main(int argc, char** argv) {
    std::uint64_t steps = 10000;
    if (argc > 1) steps = std::stoull(argv[1]);

    std::vector<KData> levels;
    for (unsigned k = 4; k <= 16; ++k) {
        const std::uint64_t mod = 1ULL << k;
        const std::uint64_t modp = 1ULL << (k + 1);
        const std::uint64_t period = 1ULL << (k - 1);
        KData kd{k, mod, {}, {}, 0, 0, 0};

        // p is even and is periodic modulo 2^(k-1) for the pair (a_p,d_p).
        // The p=0 residue represents any positive p divisible by the period.
        for (std::uint64_t p = 0; p < period; p += 2) {
            const std::uint64_t z = powmod(3, p, modp);
            const std::uint64_t a = ((z + modp - 5) % modp) / 2 % mod;
            std::int64_t dn = 13 * static_cast<std::int64_t>(z)
                            - 4 * static_cast<std::int64_t>(p) + 7;
            dn %= static_cast<std::int64_t>(modp);
            if (dn < 0) dn += static_cast<std::int64_t>(modp);
            const std::uint64_t d = static_cast<std::uint64_t>(dn / 2) % mod;
            kd.pairs.insert({a, d});
            kd.pByPair[{a, d}] = p;
        }
        levels.push_back(std::move(kd));
    }

    State s{0, 7};
    for (std::uint64_t i = 0; i <= steps; ++i) {
        for (auto& level : levels) {
            const auto a = (s.a % level.mod).convert_to<std::uint64_t>();
            const auto d = (s.d % level.mod).convert_to<std::uint64_t>();
            const auto it = level.pByPair.find({a, d});
            if (it != level.pByPair.end()) {
                if (level.count == 0) {
                    level.first = i;
                    level.firstP = it->second;
                }
                ++level.count;
            }
        }
        if (i == steps) break;
        auto n = next(s);
        if (!n) {
            std::cout << "halt at " << i << "\n";
            return 2;
        }
        s = std::move(*n);
    }

    for (const auto& level : levels) {
        std::cout << "mod2^" << level.k
                  << " tuned_pair_matches=" << level.count;
        if (level.count)
            std::cout << " first=" << level.first
                      << " p_residue=" << level.firstP;
        std::cout << " family_size=" << level.pairs.size() << "\n";
    }
}
