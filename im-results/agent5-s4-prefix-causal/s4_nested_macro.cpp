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

    // Reproduce the 50,000-macro-block finite root-model census without
    // any external data files. 64-bit arithmetic is sufficient in this range.
    if (argc > 1 && std::string(argv[1]) == "--scan-50000") {
        Tail state = actualTail;
        for (uint64_t n = 0; n < 50000; ++n) {
            for (auto c : offsets) {
                if (!G(c, state, out)) {
                    std::cerr << "unexpected failing gate at block " << n << "\n";
                    return 7;
                }
                state.swap(out);
            }
        }
        uint64_t mass = state.size();
        for (auto d : state) {
            if (d > UINT64_MAX-mass) return 8;
            mass += d;
        }
        if (state.size() != 30 || mass != 13743897600618269200ULL) return 9;
        std::cout << "PASS 50000 R blocks: tail length=" << state.size()
                  << " mass=" << mass << "\n";
    }

    // Exact terminal-quotient diagnostic over the existing finite 50,000-R-block
    // model horizon. If the carry consumes all n suffix digits, q=a+1 is the
    // remaining empty-tail potential and G halts iff q is a power of two.
    if (argc > 1 && std::string(argv[1]) == "--scan-terminal-50000") {
        Tail state = actualTail;
        uint64_t fullEvents = 0, residueCandidates = 0, exactPowers = 0;
        uint64_t maxLen = state.size();
        for (uint64_t n = 0; n < 50000; ++n) {
            for (size_t i = 0; i < offsets.size(); ++i) {
                bool fullSuffix = false;
                uint64_t q = 0;
                const uint64_t c = offsets[i];
                const bool ok = G(c, state, out, &fullSuffix, &q);
                if (fullSuffix) {
                    ++fullEvents;
                    const uint64_t r31 = q % 31;
                    const uint64_t r127 = q % 127;
                    const bool candidate31 =
                        r31 == 1 || r31 == 2 || r31 == 4 || r31 == 8 || r31 == 16;
                    const bool candidate127 =
                        r127 == 1 || r127 == 2 || r127 == 4 ||
                        r127 == 8 || r127 == 16 || r127 == 32 || r127 == 64;
                    const bool qPower = q != 0 && (q & (q - 1)) == 0;
                    residueCandidates += candidate127;
                    exactPowers += qPower;
                    std::cout << "event block=" << n << " gate=" << i
                              << " length=" << state.size() << " q=" << q
                              << " q_mod31=" << r31 << " q_mod127=" << r127
                              << " candidate127=" << candidate127
                              << " exact_power=" << qPower << "\n";
                }
                if (!ok) {
                    std::cerr << "HALT block=" << n << " gate=" << i
                              << " q=" << q << "\n";
                    return 10;
                }
                state.swap(out);
                if (state.size() > maxLen) maxLen = state.size();
            }
        }
        uint64_t totalMass = state.size();
        for (auto d : state) {
            if (d > UINT64_MAX - totalMass) return 8;
            totalMass += d;
        }
        std::cout << "SUMMARY blocks=50000 gates=" << 50000ULL * offsets.size()
                  << " full_suffix_events=" << fullEvents
                  << " candidate127=" << residueCandidates
                  << " exact_power2=" << exactPowers
                  << " max_length=" << maxLen
                  << " final_length=" << state.size()
                  << " final_mass=" << totalMass << "\n";
    }

    if (argc > 1 && std::string(argv[1]) == "--print-offsets") {
        std::cout << "Offsets:";
        for (auto v : offsets) std::cout << " " << v;
        std::cout << "\nRootTail:";
        for (auto v : actualTail) std::cout << " " << v;
        std::cout << "\n";
    }
}
