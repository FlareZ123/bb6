// Original six-state Cryptid D. A symbolic '$' marks the unread right tail.
// Every event closed before reading the marker holds for ALL possible tails.
// This is a finite computational probe, not a proof of a universal shift.
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <string>
#include <vector>

struct Result {
    int kind; // 0 physical return, 1 halt, 2 marker read, 3 timeout
    int time;
    std::string right;
};

Result run(int n, const std::string& prefix, int cap = 1000000) {
    constexpr int origin = 3200;
    constexpr int tapeSize = 80000;
    std::vector<std::uint8_t> tape(tapeSize);
    for (int i = 1; i <= n; ++i) tape[origin + i] = 1;
    for (int i = 0; i < static_cast<int>(prefix.size()); ++i)
        tape[origin + n + 1 + i] = static_cast<std::uint8_t>(prefix[i] == '1');
    const int unknown = origin + n + static_cast<int>(prefix.size()) + 1;

    constexpr int write[6][2] = {{1,0},{1,0},{1,1},{1,1},{0,0},{1,0}};
    constexpr int move[6][2] = {{1,1},{-1,1},{-1,-1},{-1,-1},{-1,-1},{-1,0}};
    constexpr int next[6][2] = {{1,4},{2,0},{0,3},{2,5},{2,1},{4,-1}};
    int head = origin, state = 5, leftOnes = 0;

    for (int t = 1; t <= cap; ++t) {
        if (head >= unknown) return {2, t-1, ""};
        if (head < 1 || head >= tapeSize-1) return {3, t-1, ""};
        int b = tape[head], w = write[state][b], d = move[state][b];
        int successor = next[state][b];
        if (successor < 0) return {1, t-1, ""};
        tape[head] = static_cast<std::uint8_t>(w);
        if (d > 0) {
            leftOnes += w;
            ++head;
        } else {
            --head;
            if (head < 1) return {3, t, ""};
            leftOnes -= tape[head];
        }
        state = successor;
        if (head < unknown && state == 5 && tape[head] == 0 && leftOnes == 0) {
            std::string right;
            for (int i = head + 1; i < unknown; ++i)
                right.push_back(static_cast<char>('0' + tape[i]));
            right.push_back('$');
            return {0, t, right};
        }
    }
    return {3, cap, ""};
}

int main(int argc, char** argv) {
    const int residue = argc > 1 ? std::atoi(argv[1]) : 3;
    const int depth = argc > 2 ? std::atoi(argv[2]) : 24;
    const int k = argc > 3 ? std::atoi(argv[3]) : 0;
    std::vector<std::string> frontier = {""};
    long long closed = 0, broken = 0, halting = 0, timeouts = 0;
    int lastDepth = 0;

    for (int d = 0; d <= depth && !frontier.empty(); ++d) {
        std::vector<std::string> nextFrontier;
        std::map<int, int> levels;
        long atDepth = 0, haltHere = 0, timeoutHere = 0;
        for (const auto& prefix : frontier) {
            Result a = run(residue + 3*k, prefix);
            Result b = run(residue + 3*(k+1), prefix);
            Result c = run(residue + 3*(k+2), prefix);
            if (a.kind >= 2 || b.kind >= 2 || c.kind >= 2) {
                if (a.kind == 3 || b.kind == 3 || c.kind == 3) {
                    ++timeoutHere;
                    continue;
                }
                if (d < depth) {
                    nextFrontier.push_back(prefix + '0');
                    nextFrontier.push_back(prefix + '1');
                }
                continue;
            }

            bool agrees = a.kind == b.kind && b.kind == c.kind;
            if (a.kind == 0) {
                agrees = agrees &&
                    b.right == std::string(8, '1') + a.right &&
                    c.right == std::string(8, '1') + b.right;
            }
            int delta = b.time - a.time;
            int secondDelta = c.time - b.time;
            int base = a.kind == 0 ? 61 : 53;
            int rem = delta - (24*k + base);
            agrees = agrees && rem >= 0 && rem % 24 == 0 &&
                secondDelta == delta + 24;
            if (!agrees) {
                ++broken;
                std::cerr << "COUNTEREXAMPLE prefix=" << prefix <<
                    " kinds=" << a.kind << "," << b.kind << "," << c.kind <<
                    " times=" << a.time << "," << b.time << "," << c.time <<
                    " rights=" << a.right << "," << b.right << "\n";
            } else {
                ++atDepth;
                if (a.kind == 1) ++haltHere;
                ++levels[rem/24];
            }
        }
        closed += atDepth;
        halting += haltHere;
        timeouts += timeoutHere;
        lastDepth = d;
        std::cout << "d=" << d << " active=" << frontier.size() <<
            " closed=" << atDepth << " halted=" << haltHere <<
            " timeout=" << timeoutHere << " next=" << nextFrontier.size() <<
            " levels=" << levels.size() << "\n";
        if (broken) break;
        frontier.swap(nextFrontier);
    }
    std::cerr << "total_closed=" << closed <<
        " halt_prefixes=" << halting << " mismatches=" << broken <<
        " timeouts=" << timeouts << " last_depth=" << lastDepth <<
        " remaining=" << frontier.size() << "\n";
    return broken || timeouts ? 1 : 0;
}
