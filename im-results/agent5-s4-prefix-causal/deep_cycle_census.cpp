// Exact finite arithmetic for S4 total prefix projection, starting at the
// original-source certified 18-digit return-5457 state. C++20, standard library.
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>

using State = std::array<std::uint64_t, 18>;
constexpr std::uint64_t block = 327680;
constexpr int offsets[3] = {509, 290, 219};

// Total finite-prefix gate from the source-exact hp/gp recurrence. This is
// deliberately distinct from the partial full-stack G gate at empty suffix.
void gate(State &s, int c) {
    std::uint64_t a = s[0] + c;
    for (std::size_t i = 0; i < s.size(); ++i) {
        if (i + 1 == s.size()) {
            s[i] = a / 2 + ((a & 1) == 0 ? 2 : 0);
            return;
        }
        if ((a & 1) == 0) {
            auto next = s[i + 1];
            s[i] = a / 2 + 2;
            s[i + 1] = next + a / 2;
            return;
        }
        s[i] = a / 2;
        a = s[i + 1] + a / 2 + 1;
    }
}

bool samePrefix(const State &s, const State &t, int n) {
    for (int i = 0; i < n; ++i)
        if (s[i] != t[i]) return false;
    return true;
}

// A stopping event requires this residue to vanish. A zero residue is only
// a necessary condition and does not certify a halt on the genuine stack.
bool candidate(const State &s, int c, int n) {
    std::uint64_t w = c;
    for (int i = 0; i < n; ++i) {
        assert(s[i] < 1000000000ULL); // ensures 64-bit arithmetic is exact
        w += (s[i] + 1) << i;
    }
    return (w & ((1ULL << n) - 1)) == 0;
}

int main() {
    State s = {283, 906, 982, 3490, 3734, 5935, 13580, 109210, 171050,
               366446, 435688, 443554, 1702180, 1770018, 211301, 281569,
               35137, 35134};
    State checkpoints[69]{};
    checkpoints[0] = s;
    std::uint64_t counts[19][3]{};

    for (int b = 0; b < 68; ++b) {
        for (std::uint64_t step = 0; step < block; ++step) {
            for (int j = 0; j < 3; ++j) {
                for (int k : {10, 13, 16, 17, 18}) {
                    bool inPeriod = (k == 10 && b == 0)
                        || (k == 13 && b == 1)
                        || (k == 16 && b >= 1 && b < 5)
                        || (k == 17 && b >= 2 && b < 18)
                        || (k == 18 && b >= 4);
                    if (inPeriod && candidate(s, offsets[j], k))
                        ++counts[k][j];
                }
                gate(s, offsets[j]);
            }
        }
        checkpoints[b + 1] = s;
    }

    assert(samePrefix(checkpoints[0], checkpoints[1], 10));
    for (int n = 11; n <= 13; ++n)
        assert(samePrefix(checkpoints[1], checkpoints[2], n));
    assert(samePrefix(checkpoints[1], checkpoints[3], 14));
    for (int n = 15; n <= 16; ++n)
        assert(samePrefix(checkpoints[1], checkpoints[5], n));
    assert(samePrefix(checkpoints[2], checkpoints[18], 17));
    assert(checkpoints[4] == checkpoints[68]);

    assert(counts[10][0] == 245 && counts[10][1] == 392 && counts[10][2] == 799);
    assert(counts[13][0] == 32 && counts[13][1] == 40 && counts[13][2] == 106);
    assert(counts[16][0] == 23 && counts[16][1] == 28 && counts[16][2] == 48);
    assert(counts[17][0] == 48 && counts[17][1] == 55 && counts[17][2] == 94);
    assert(counts[18][0] == 93 && counts[18][1] == 110 && counts[18][2] == 183);

    for (int n : {10, 13, 16, 17, 18}) {
        std::cout << n << " digits: G509=" << counts[n][0]
                  << " G290=" << counts[n][1]
                  << " G219=" << counts[n][2]
                  << " total=" << counts[n][0] + counts[n][1] + counts[n][2]
                  << '\n';
    }
    std::cout << "PASS: projected periods and residue phase counts\n";
}
