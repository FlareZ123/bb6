// Original D-Cryptid six-state machine. C++17 independent raw replay.
// Tests a proposed all-suffix first-event synchronisation/time conjecture.
// Finite experiments are NOT proofs. No blank-root reachability is assumed.
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <map>
#include <random>
#include <string>
#include <vector>

struct Result { int kind, time, unary; std::string tail; };

// kind: 0 = physical blank-left F/0 return, 1 = F/1 halt, 2 = timeout.
Result first_event(int unary, const std::vector<std::uint8_t>& suffix,
                   int cap = 1000000) {
    constexpr int Origin = 14000, Size = 42000;
    std::vector<std::uint8_t> tape(Size, 0);
    for (int i = 1; i <= unary; ++i) tape[Origin + i] = 1;
    for (std::size_t i = 0; i < suffix.size(); ++i)
        tape[Origin + unary + 1 + static_cast<int>(i)] = suffix[i];
    constexpr int write[6][2] = {{1,0},{1,0},{1,1},{1,1},{0,0},{1,0}};
    constexpr int move[6][2] = {{1,1},{-1,1},{-1,-1},{-1,-1},{-1,-1},{-1,0}};
    constexpr int next[6][2] = {{1,4},{2,0},{0,3},{2,5},{2,1},{4,-1}};
    int head = Origin, state = 5, leftOnes = 0;
    int furthest = Origin + unary + static_cast<int>(suffix.size()) + 2;
    for (int t = 1; t <= cap; ++t) {
        int b = tape[head], w = write[state][b], d = move[state][b];
        int s = next[state][b];
        if (s == -1) return {1, t - 1, 0, ""};
        tape[head] = static_cast<std::uint8_t>(w);
        if (d == 1) { leftOnes += w; ++head; }
        else { --head; leftOnes -= tape[head]; }
        state = s;
        if (head < 0 || head + 200 >= Size) return {2, t, 0, ""};
        furthest = std::max(furthest, head + 5);
        if (state == 5 && tape[head] == 0 && leftOnes == 0) {
            int end = furthest;
            while (end > head && tape[end] == 0) --end;
            int i = head + 1;
            while (i <= end && tape[i] == 1) ++i;
            std::string tail;
            for (int j = i; j <= end; ++j) tail.push_back(tape[j] ? '1' : '0');
            return {0, t, i - head - 1, tail};
        }
    }
    return {2, cap, 0, ""};
}

struct Counts { long tests=0, valid=0, timeouts=0, errors=0, halts=0; std::map<int,long> levels; };

void check(Counts& c, int k, int residue, const std::vector<std::uint8_t>& word) {
    int a = 3 * k + residue;
    Result x = first_event(a, word), y = first_event(a + 3, word),
           z = first_event(a + 6, word);
    ++c.tests;
    if (x.kind == 2 || y.kind == 2 || z.kind == 2) { ++c.timeouts; return; }
    ++c.valid;
    if (x.kind == 1) ++c.halts;
    bool same = x.kind == y.kind && y.kind == z.kind;
    if (x.kind == 0)
        same = same && y.unary == x.unary + 8 && z.unary == x.unary + 16
                    && x.tail == y.tail && x.tail == z.tail;
    int dt = y.time - x.time, dt2 = z.time - y.time;
    int base = x.kind == 0 ? 61 : 53;
    int remaining = dt - (24 * k + base);
    bool timed = remaining >= 0 && remaining % 24 == 0 && dt2 == dt + 24;
    if (!same || !timed) {
        ++c.errors;
        if (c.errors < 8) {
            std::printf("COUNTEREXAMPLE k=%d residue=%d suffixLength=%zu ",
                        k, residue, word.size());
            for (auto v : word) std::printf("%d", v);
            std::printf(" kinds=%d,%d,%d times=%d,%d,%d deltas=%d,%d\n",
                x.kind, y.kind, z.kind, x.time, y.time, z.time, dt, dt2);
        }
    } else ++c.levels[remaining / 24];
}

int main() {
    Counts all;
    for (int a : {5,6,7,8,9,10,15,39}) {
        int residue = (a - 2) % 3 + 2;
        int k = (a - residue) / 3;
        for (int length = 0; length <= 14; ++length)
            for (int mask = 0; mask < (1 << length); ++mask) {
                std::vector<std::uint8_t> word(length);
                for (int bit = 0; bit < length; ++bit)
                    word[bit] = (mask >> bit) & 1;
                check(all, k, residue, word);
            }
    }
    std::printf("EXHAUSTIVE: tested=%ld verified=%ld timeout=%ld errors=%ld halts=%ld\n",
        all.tests, all.valid, all.timeouts, all.errors, all.halts);
    Counts random;
    std::mt19937_64 rng(20261105);
    for (int trial = 0; trial < 5000; ++trial) {
        int k = static_cast<int>(rng() % 36);
        int residue = 2 + static_cast<int>(rng() % 3);
        int length = 1 + static_cast<int>(rng() % 160);
        std::vector<std::uint8_t> word(length, 0);
        for (int bit = 1; bit < length; ++bit) word[bit] = rng() & 1;
        word.back() = 1;
        check(random, k, residue, word);
    }
    std::printf("RANDOM: tested=%ld verified=%ld timeout=%ld errors=%ld halts=%ld\n",
        random.tests, random.valid, random.timeouts, random.errors, random.halts);
    for (auto [level, count] : random.levels)
        std::printf("level%d=%ld ", level, count);
    std::puts("");
    return all.errors || random.errors ? 1 : 0;
}
