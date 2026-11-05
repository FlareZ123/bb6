// Independent original-table primitive regression for the q=7 E/A root packet.
// Compile from this directory with C++17; it includes the separate raw simulator.
#define main original_verifier_main
#include "shift_first_event.cpp"
#undef main

int main() {
    for (int t = 0; t < 35; ++t) {
        int n = 9*t+10, k = 3*t+2, K = 8*t+6;
        std::vector<std::uint8_t> suffix{0};
        for (int i = 0; i < 6; ++i) {
            suffix.push_back(1);
            suffix.push_back(0);
        }
        suffix.push_back(1);
        suffix.push_back(1);

        Result first = first_event(n, suffix, 1000000);
        std::vector<std::uint8_t> nextTail;
        for (auto ch : first.tail) nextTail.push_back(ch == '1');
        Result second = first_event(first.unary, nextTail, 1000000);

        int expectedE = 12*k*k+49*k+84;
        int expectedA = 12*K*K+145*K+474;
        if (first.kind != 0 || second.kind != 0 ||
            first.time != expectedE || second.time != expectedA ||
            second.unary != 64*t+91 || second.tail != "01010111") {
            std::fprintf(stderr,
                "FAIL t=%d E kind/time=%d/%d A kind/time=%d/%d output=%d %s\n",
                t, first.kind, first.time, second.kind, second.time,
                second.unary, second.tail.c_str());
            return 1;
        }
    }
    std::puts("PASS: all 35 q=7 original primitive two-first-return checks");
    return 0;
}
