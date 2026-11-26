#include <bits/stdc++.h>
using namespace std;

struct Rule {
    int write = 0;
    int dir = 0;
    int next = 0;
    bool defined = false;
};

static void ensure_index(vector<uint8_t>& tape, int64_t& offset, int64_t pos) {
    while (pos + offset < 0 || pos + offset >= static_cast<int64_t>(tape.size())) {
        const size_t old_size = tape.size();
        const size_t new_size = old_size * 2;
        vector<uint8_t> grown(new_size, 0);
        const int64_t new_offset = static_cast<int64_t>(new_size / 2);
        const int64_t shift = new_offset - offset;
        copy(tape.begin(), tape.end(), grown.begin() + shift);
        tape.swap(grown);
        offset = new_offset;
    }
}

static bool parse_table(const string& text, Rule rules[6][2]) {
    if (text.size() != 36) return false;
    for (int q = 0; q < 6; ++q) {
        for (int b = 0; b < 2; ++b) {
            const string tok = text.substr(3 * (2 * q + b), 3);
            Rule r;
            if (tok != "---") {
                if ((tok[0] != '0' && tok[0] != '1') ||
                    (tok[1] != 'L' && tok[1] != 'R') ||
                    (tok[2] < 'A' || tok[2] > 'F')) return false;
                r.defined = true;
                r.write = tok[0] - '0';
                r.dir = tok[1] == 'R' ? 1 : -1;
                r.next = tok[2] - 'A';
            }
            rules[q][b] = r;
        }
    }
    return true;
}

int main(int argc, char** argv) {
    if (argc != 2) {
        cerr << "usage: simulate_1lb_residuals CAP < id-table-lines\n";
        return 2;
    }
    const uint64_t cap = stoull(argv[1]);
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    string id, table;
    while (cin >> id >> table) {
        Rule rules[6][2];
        if (!parse_table(table, rules)) {
            cerr << "invalid table for " << id << "\n";
            return 2;
        }

        vector<uint8_t> tape(1u << 20, 0);
        int64_t offset = static_cast<int64_t>(tape.size() / 2);
        int64_t head = 0, min_head = 0, max_head = 0;
        int state = 0;
        uint64_t steps = 0, ones = 0;
        bool found_hole = false;

        while (steps < cap) {
            ensure_index(tape, offset, head);
            const size_t ix = static_cast<size_t>(head + offset);
            const int bit = tape[ix];
            const Rule& r = rules[state][bit];
            if (!r.defined) {
                found_hole = true;
                cout << "{\"id\":\"" << id << "\",\"status\":\"hole\","
                     << "\"steps\":" << steps << ",\"state\":" << state
                     << ",\"bit\":" << bit << ",\"head\":" << head
                     << ",\"ones\":" << ones << ",\"min_head\":" << min_head
                     << ",\"max_head\":" << max_head << "}\n";
                break;
            }
            if (bit != r.write) {
                if (r.write) ++ones;
                else --ones;
                tape[ix] = static_cast<uint8_t>(r.write);
            }
            state = r.next;
            head += r.dir;
            ++steps;
            min_head = min(min_head, head);
            max_head = max(max_head, head);
        }

        if (!found_hole) {
            cout << "{\"id\":\"" << id << "\",\"status\":\"no-hole-within-cap\","
                 << "\"steps\":" << steps << ",\"state\":" << state
                 << ",\"head\":" << head << ",\"ones\":" << ones
                 << ",\"min_head\":" << min_head << ",\"max_head\":" << max_head
                 << ",\"tape_cells\":" << tape.size() << "}\n";
        }
    }
    return 0;
}
