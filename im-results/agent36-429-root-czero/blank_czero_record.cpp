// Original six-state #429 primitive-step blank-tape test. C++17.
// No macro assumptions; only finite evidence, never an all-time proof.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <vector>

int main() {
    constexpr std::int64_t steps = 100'000'000;
    constexpr std::int64_t offset = 12'000'000;
    std::vector<unsigned char> tape(2 * offset, 0);
    // 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA
    constexpr std::array<std::array<unsigned char, 2>, 6> writes{{
        {{1, 0}}, {{1, 1}}, {{0, 0}}, {{1, 0}}, {{0, 1}}, {{1, 1}}}};
    constexpr std::array<std::array<int, 2>, 6> shifts{{
        {{1, -1}}, {{1, 1}}, {{1, 1}}, {{-1, 0}}, {{-1, -1}}, {{1, -1}}}};
    constexpr std::array<std::array<int, 2>, 6> next{{
        {{1, 5}}, {{2, 0}}, {{3, 1}}, {{4, -1}}, {{0, 4}}, {{3, 0}}}};

    std::int64_t head = 0, max_prior_head = -1, min_head = 0;
    std::int64_t c0_total = 0, nonrecord = 0, right_marked = 0;
    int state = 0;
    for (std::int64_t t = 0; t < steps; ++t) {
        const auto i = head + offset;
        if (i < 1 || i + 1 >= static_cast<std::int64_t>(tape.size())) {
            std::printf("TAPE_BOUND t=%lld head=%lld\n",
                        (long long)t, (long long)head);
            return 2;
        }
        const unsigned char bit = tape[static_cast<std::size_t>(i)];
        if (state == 2 && bit == 0) {
            ++c0_total;
            if (head <= max_prior_head) {
                ++nonrecord;
                std::printf("NONRECORD t=%lld head=%lld prior=%lld\n",
                            (long long)t, (long long)head, (long long)max_prior_head);
            }
            if (tape[static_cast<std::size_t>(i + 1)] != 0) {
                ++right_marked;
                std::printf("C01_FATAL_INPUT t=%lld head=%lld\n",
                            (long long)t, (long long)head);
            }
        }
        const int ns = next[static_cast<std::size_t>(state)][bit];
        if (ns < 0) {
            std::printf("HALT t=%lld head=%lld c0=%lld\n",
                        (long long)t, (long long)head, (long long)c0_total);
            return 0;
        }
        max_prior_head = std::max(max_prior_head, head);
        min_head = std::min(min_head, head);
        tape[static_cast<std::size_t>(i)] = writes[static_cast<std::size_t>(state)][bit];
        head += shifts[static_cast<std::size_t>(state)][bit];
        state = ns;
    }
    std::printf("STEPS=%lld C0=%lld NONRECORD=%lld C01=%lld MAX_VISITED=%lld MIN_VISITED=%lld\n",
                (long long)steps, (long long)c0_total, (long long)nonrecord,
                (long long)right_marked, (long long)max_prior_head, (long long)min_head);
}
