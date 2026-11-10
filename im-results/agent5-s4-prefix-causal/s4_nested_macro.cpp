// Second-level S4 source-operator renormalization.
// C++20, standalone together with s4_suffix_macro.cpp in this directory.
// The exact source-compatible 18-prefix block becomes 386 G gates.
// A root-synchronized 10-prefix cycle of that 386-gate word becomes 4603 G gates.
#define BB6_S4_SUFFIX_MACRO_LIBRARY
#include "s4_suffix_macro.cpp"
#include <string>
using NestedPrefix = std::array<uint64_t, 10>;
constexpr uint64_t NESTED_PERIOD = 12800;

void nestedGp(NestedPrefix& x, uint64_t c) {
    uint64_t a = x[0] + c;
    for (size_t i = 0; i < x.size(); ++i) {
        if (i+1 == x.size()) {
            x[i] = a / 2 + ((a & 1) ? 0 : 2);
            return;
        }
        if (!(a & 1)) {
            x[i] = a / 2 + 2;
            x[i+1] += a / 2;
            return;
        }
        x[i] = a / 2;
        a = x[i+1] + a / 2 + 1;
    }
}

Boundary nestedBoundary(const NestedPrefix& x, uint64_t c) {
    uint64_t a = x[0] + c;
    for (size_t i = 0; i < x.size(); ++i) {
        if (!(a & 1)) return i+1 == x.size()
            ? Boundary{1, a / 2} : Boundary{0, 0};
        if (i+1 == x.size()) return Boundary{2, a / 2 + 1};
        a = x[i+1] + a / 2 + 1;
    }
    return {0, 0};
}

int main(int argc, char** argv) {
    const Word first = extract();
    const Tail root = blockRoot();
    Tail full(root.begin()+K, root.end()), out;

    // The full first-level modeled suffix at macro index 107.
    for (int t = 0; t < 107; ++t) {
        for (auto c : first.offsets) {
            if (!G(c, full, out)) return 1;
            full.swap(out);
        }
    }
    if (full.size() < 10) return 1;
    NestedPrefix initial{};
    std::copy_n(full.begin(), 10, initial.begin());
    NestedPrefix p = initial;
    Tail actualTail(full.begin()+10, full.end());

    std::vector<uint64_t> offsets;
    uint64_t nAdd=0, nGate=0, pending=0, sumAdd=0, sumGate=0;
    for (uint64_t t = 0; t < NESTED_PERIOD; ++t) {
        for (auto c : first.offsets) {
            const auto e = nestedBoundary(p, c);
            if (e.kind == 1) {
                nAdd++;
                sumAdd += e.d;
                pending += e.d;
            } else if (e.kind == 2) {
                nGate++;
                sumGate += e.d;
                offsets.push_back(e.d + pending);
                pending = 0;
            }
            nestedGp(p, c);
        }
    }

    assert(p == initial);
    assert(nGate == 4603 && nAdd == 4597 && pending == 0);
    const auto sum = std::accumulate(offsets.begin(), offsets.end(), uint64_t{0});
    assert(sum == 274877906934794ULL);
    assert(sum + 2*nGate == 1024ULL*T*NESTED_PERIOD);
    assert(*std::min_element(offsets.begin(), offsets.end()) == 6883659092ULL);
    assert(*std::max_element(offsets.begin(), offsets.end()) == 546356049297ULL);

    // Independently compare 4,940,800 original first-level G calls to the
    // 4,603-gate second-level word, at the complete modeled root tail.
    Tail accelerated = actualTail;
    for (auto c : offsets) {
        if (!G(c, accelerated, out)) return 1;
        accelerated.swap(out);
    }
    for (uint64_t t = 0; t < NESTED_PERIOD; ++t) {
        for (auto c : first.offsets) {
            if (!G(c, full, out)) return 1;
            full.swap(out);
        }
    }
    assert(full.size() >= 10);
    assert(std::equal(full.begin(), full.begin()+10, initial.begin()));
    assert(std::equal(full.begin()+10, full.end(),
                      accelerated.begin(), accelerated.end()));

    std::cout << "Nested prefix:";
    for (auto v : initial) std::cout << " " << v;
    std::cout << "\nBoundary add=" << nAdd << " gates=" << nGate
              << " pending=" << pending;
    std::cout << "\nEffective offset sum=" << sum
              << " mass gain=" << 1024ULL*T*NESTED_PERIOD;
    std::cout << "\nPASS: Q^12800 equals the 4603-gate nested suffix word\n";

    if (argc > 1 && std::string(argv[1]) == "--print-offsets") {
        std::cout << "Offsets:";
        for (auto v : offsets) std::cout << " " << v;
        std::cout << "\nRootTail:";
        for (auto v : actualTail) std::cout << " " << v;
        std::cout << "\n";
    }
}
