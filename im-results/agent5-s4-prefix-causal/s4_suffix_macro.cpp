// Exact S4 18-digit period-renormalization certificate and authentic-root test.
// C++20. A 20,971,520-return P block compresses to 386 G gates on the suffix.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

using std::uint64_t;
using Prefix = std::array<uint64_t, 18>;
using Tail = std::vector<uint64_t>;
constexpr uint64_t B = 327680;
constexpr uint64_t T = 64 * B;
constexpr int C[3] = {509, 290, 219};
constexpr Prefix ROOT = {
    283, 906, 982, 3490, 3734, 5935, 13580, 109210, 171050,
    366446, 435688, 443554, 1702180, 1770018, 211301, 281569, 35137, 35134
};
constexpr Tail::size_type K = 18;

// Total finite-prefix gp, not the partial full-stack G.
void gp(Prefix& x, int c) {
    uint64_t a = x[0] + c;
    for (size_t i = 0; i < K; i++) {
        if (i == K - 1) {
            x[i] = a / 2 + ((a & 1) ? 0 : 2);
            return;
        }
        if (!(a & 1)) {
            x[i] = a / 2 + 2;
            x[i + 1] += a / 2;
            return;
        }
        x[i] = a / 2;
        a = x[i + 1] + a / 2 + 1;
    }
}

// Boundary action on arbitrary suffix: 0 identity, 1 add to head, 2 G_d.
struct Boundary { int kind; uint64_t d; };
Boundary boundary(const Prefix& x, int c) {
    uint64_t a = x[0] + c;
    for (size_t i = 0; i < K; i++) {
        if (!(a & 1)) return i == K - 1 ? Boundary{1, a / 2} : Boundary{0, 0};
        if (i == K - 1) return {2, a / 2 + 1};
        a = x[i + 1] + a / 2 + 1;
    }
    return {0, 0};
}
struct Word {
    std::vector<uint64_t> offsets;
    uint64_t adds = 0, originalG = 0, sumAdd = 0, sumG = 0, pending = 0;
};
Word extract() {
    Prefix p = ROOT, start{};
    Word w;
    for (uint64_t b = 0; b < 68; b++) {
        if (b == 4) start = p;
        for (uint64_t step = 0; step < B; step++) {
            for (int c : C) {
                if (b >= 4) {
                    auto e = boundary(p, c);
                    if (e.kind == 1) {
                        assert(e.d > 0);
                        w.adds++; w.sumAdd += e.d; w.pending += e.d;
                    }
                    if (e.kind == 2) {
                        w.originalG++; w.sumG += e.d;
                        w.offsets.push_back(e.d + w.pending);
                        w.pending = 0;
                    }
                }
                gp(p, c);
            }
        }
    }
    assert(p == start);
    assert(w.adds == 402 && w.originalG == 386 && w.pending == 0);
    auto sum = std::accumulate(w.offsets.begin(), w.offsets.end(), uint64_t{0});
    assert(sum == 21474835708ULL && sum + 2 * w.originalG == 1024 * T);
    assert(*std::min_element(w.offsets.begin(), w.offsets.end()) == 5178393ULL);
    assert(*std::max_element(w.offsets.begin(), w.offsets.end()) == 309630238ULL);
    return w;
}

// Original partial G(c), including G(c,[]) = H(c-1,[]).
bool G(uint64_t c, const Tail& xs, Tail& out) {
    out.clear();
    uint64_t a = xs.empty() ? c - 1 : xs[0] + c;
    size_t i = xs.empty() ? 0 : 1;
    while (i < xs.size() && (a & 1)) {
        out.push_back(a / 2);
        a = xs[i] + a / 2 + 1;
        ++i;
    }
    if (a & 1) {
        while (a & 1) {
            if (a <= 1) return false;
            out.push_back(a / 2);
            a /= 2;
        }
        if (!a) return false;
        out.push_back(a / 2 + 2);
        out.push_back(a / 2 - 1);
    } else if (i < xs.size()) {
        out.push_back(a / 2 + 2);
        out.push_back(xs[i] + a / 2);
        for (++i; i < xs.size(); ++i) out.push_back(xs[i]);
    } else {
        if (!a) return false;
        out.push_back(a / 2 + 2);
        out.push_back(a / 2 - 1);
    }
    return true;
}

Tail blockRoot() {
    return {283, 906, 982, 3490, 3734, 5935, 13580, 109210, 171050,
            366446, 435438, 366335, 527037, 2639156, 3037351,
            3252483, 6310511, 24221543, 24423525, 56750562,
            67602890, 162126013, 335820941, 659578070};
}
int main() {
    auto w = extract();
    Tail full = blockRoot(), out;
    Tail suffix(full.begin() + K, full.end());
    Tail accelerated = suffix;
    for (auto c : w.offsets) {
        assert(G(c, accelerated, out));
        accelerated.swap(out);
    }
    for (uint64_t n = 0; n < T; n++) {
        for (int c : C) {
            assert(G(c, full, out));
            full.swap(out);
        }
    }
    assert(full.size() >= K);
    auto expectedPrefix = blockRoot();
    assert(std::equal(full.begin(), full.begin() + K, expectedPrefix.begin()));
    assert(std::equal(full.begin() + K, full.end(),
                      accelerated.begin(), accelerated.end()));
    std::cout << "Boundary events: " << w.adds << " head-adds, "
              << w.originalG << " G gates\n";
    std::cout << "Normalized word: " << w.offsets.size()
              << " G offsets, trailing head-add " << w.pending << "\n";
    std::cout << "Sum of offsets: "
              << std::accumulate(w.offsets.begin(), w.offsets.end(), uint64_t{0})
              << "; mass gain " << 1024 * T << "\n";
    std::cout << "PASS: authentic root block matches normalized suffix word\n";
    std::cout << "Offsets:";
    for (auto c : w.offsets) std::cout << " " << c;
    std::cout << "\n";
}

#endif // BB6_S4_SUFFIX_MACRO_LIBRARY
