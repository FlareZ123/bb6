#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <string>
#include <vector>

using namespace std;

struct Cand {
  array<int, 12> tab;
  int steps;
  vector<int> path;
};

array<int, 12> tab;
map<string, Cand> found;
long long nodes = 0;
int maxDepth = 8, maxNew = 5;
uint64_t rightTarget = (1ULL << 33) | (1ULL << 34);
uint64_t leftTarget = (1ULL << 31) | (1ULL << 32);

string keytab(const array<int, 12>& t) {
  string s;
  for (int x : t) s += char(x + 1);
  return s;
}

void dfs(int state, int head, uint64_t ones, int steps, int nnew,
         vector<int>& path) {
  ++nodes;
  if (state == 2 &&
      ((head == 1 && ones == rightTarget) ||
       (head == -1 && ones == leftTarget))) {
    Cand c{tab, steps, path};
    found.emplace(keytab(tab), c);
    return;
  }
  if (steps >= maxDepth) return;

  int bit = (ones >> (head + 32)) & 1ULL;
  int slot = state * 2 + bit;
  auto run = [&](int a, int nextNew) {
    bool write = a >= 12;
    bool right = (a % 12) >= 6;
    int next = a % 6;
    uint64_t nmask = ones;
    uint64_t bitmask = 1ULL << (head + 32);
    if (write) nmask |= bitmask;
    else nmask &= ~bitmask;
    int nh = head + (right ? 1 : -1);
    path.push_back(a);
    dfs(next, nh, nmask, steps + 1, nextNew, path);
    path.pop_back();
  };

  if (tab[slot] >= 0) {
    run(tab[slot], nnew);
    return;
  }
  if (nnew >= maxNew) return;
  for (int a = 0; a < 24; a++) {
    tab[slot] = a;
    run(a, nnew + 1);
    tab[slot] = -1;
  }
}

string notation(int a) {
  if (a < 0) return "?";
  char w = a >= 12 ? '1' : '0';
  char d = (a % 12) >= 6 ? 'R' : 'L';
  char q = 'A' + (a % 6);
  return string() + w + d + q;
}

int main(int argc, char** argv) {
  if (argc > 1) maxDepth = atoi(argv[1]);
  if (argc > 2) maxNew = atoi(argv[2]);
  tab.fill(-1);

  // P4 = A/0 1RB, B/0 1LC, C/1 0RD, D/1 1RE.
  tab[0] = 19;
  tab[2] = 14;
  tab[5] = 9;
  tab[7] = 22;

  vector<int> path;
  dfs(2, 0, (1ULL << 32) | (1ULL << 33), 0, 0, path);
  cerr << "nodes=" << nodes << " candidates=" << found.size() << "\n";

  vector<Cand> cs;
  for (auto& kv : found) cs.push_back(kv.second);
  sort(cs.begin(), cs.end(), [](const Cand& a, const Cand& b) {
    int na = count_if(a.tab.begin(), a.tab.end(), [](int x) { return x >= 0; });
    int nb = count_if(b.tab.begin(), b.tab.end(), [](int x) { return x >= 0; });
    if (na != nb) return na < nb;
    return a.steps < b.steps;
  });

  int shown = 0;
  for (auto& c : cs) {
    if (shown++ >= 80) break;
    int fixed = count_if(c.tab.begin(), c.tab.end(), [](int x) { return x >= 0; });
    cout << "steps=" << c.steps << " slots=" << fixed
         << " mass=25^" << (12 - fixed) << "\n";
    for (int s = 0; s < 12; s++) {
      if (c.tab[s] >= 0)
        cout << "  " << char('A' + s / 2) << "/" << (s % 2)
             << "=" << notation(c.tab[s]) << "\n";
    }
    cout << "path=";
    for (int a : c.path) cout << notation(a) << " ";
    cout << "\n\n";
  }
}
