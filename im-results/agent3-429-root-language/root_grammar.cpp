#include <cstdint>
#include <cstdio>
#include <vector>

// Literal #429 table, A=0 through F=5, tape 0/1. D/1 is undefined.
// An exact blank-origin stress test of the candidate C/0 section language.
int main() {
    constexpr int N = 1 << 22, origin = N / 2;
    constexpr std::uint64_t steps = 1000000000ULL;
    constexpr int write[6][2] = {{1,0},{1,1},{0,0},{1,-1},{0,1},{1,1}};
    constexpr int shift[6][2] = {{1,-1},{1,1},{1,1},{-1,0},{-1,-1},{1,-1}};
    constexpr int next[6][2] = {{1,5},{2,0},{3,1},{4,-1},{0,4},{3,0}};
    std::vector<unsigned char> tape(N, 0);
    int head = origin, state = 0, max_before = origin-1, min_visited = origin;
    int events = 0, typeI = 0, typeII = 0, outside = 0, record_fail = 0;

    for (std::uint64_t step = 0; step < steps; ++step) {
        const int read = tape[head];
        if (state == 2 && read == 0) {
            ++events;
            if (head <= max_before || tape[head+1]) ++record_fail;
            int leftmost = min_visited;
            while (leftmost < head && !tape[leftmost]) ++leftmost;
            int marked_runs = 0, long_runs = 0, long_at = -1;
            int terminal = 0;
            bool isolated_zero = true, odd_long = true;
            for (int x = head-1; x >= leftmost;) {
                int ones = 0;
                while (x >= leftmost && tape[x]) { ++ones; --x; }
                if (ones) {
                    ++marked_runs;
                    terminal = ones;
                    if (x >= leftmost && ones > 1) {
                        ++long_runs;
                        long_at = marked_runs-1;
                        if (ones % 2 == 0) odd_long = false;
                    }
                }
                int zeros = 0;
                while (x >= leftmost && !tape[x]) { ++zeros; --x; }
                if (zeros > 1) isolated_zero = false;
            }
            if (isolated_zero && terminal % 2 == 0 && long_runs == 0) {
                ++typeI;
            } else if (isolated_zero && terminal == 6 && odd_long &&
                       long_runs == 1 && long_at <= 1) {
                ++typeII;
            } else {
                ++outside;
                if (outside <= 5) {
                    std::printf("OUTSIDE step=%llu head=%d\n",
                       (unsigned long long)step, head-origin);
                }
            }
        }
        if (head > max_before) max_before = head;
        if (head < min_visited) min_visited = head;
        const int new_state = next[state][read];
        if (new_state < 0) {
            std::printf("HALT step=%llu\n", (unsigned long long)step);
            break;
        }
        tape[head] = static_cast<unsigned char>(write[state][read]);
        head += shift[state][read];
        state = new_state;
        if (head <= 0 || head >= N-1) {
            std::puts("BUFFER EXCEEDED; sample invalid");
            return 1;
        }
    }
    std::printf("events=%d I=%d II=%d outside=%d right_record_fail=%d range=%d..%d\n",
        events,typeI,typeII,outside,record_fail,min_visited-origin,max_before-origin);
}
