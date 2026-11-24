#include <bits/stdc++.h>
using namespace std;
using i64 = long long;

struct Stats {
  int maxD = 0;
  long long unhandled = 0;
  map<string, long long> killed;
};

static inline int md(i64 x, int m) { return int(x % m); }

// Exact BB429Mod8.Allowed residue table.
static inline bool allowed(i64 a, i64 b) {
  const int x = md(a, 8), y = md(b, 4);
  switch (x) {
    case 0: return y == 0 || y == 2;
    case 1: return y == 0 || y == 1 || y == 2;
    case 2: return y == 2;
    case 3: return y == 1 || y == 2 || y == 3;
    case 4: return y == 2;
    case 5: return true;
    case 6: return y == 2;
    case 7: return y == 2 || y == 3;
  }
  return false;
}

// Only source-certified all-time root obstructions are used here.
// They correspond to BB429RootEven8, BB429RootMod16/32,
// BB429NewRootRows, and BB429RootMod64R0/R2.
static inline const char* bad(i64 a, i64 b) {
  const int A8 = md(a, 8), B8 = md(b, 8);
  const int A16 = md(a, 16), B16 = md(b, 16);
  const int A32 = md(a, 32), B32 = md(b, 32);
  const int A64 = md(a, 64);

  if (!allowed(a, b)) return "Allowed";
  if (a > 0 && a % 2 == 0 && B8 != 2) return "positive_even_eight";
  if (A8 == 7 && B8 == 7) return "rooted_not_7_7";
  if (A16 == 1 && B8 == 6) return "rooted_not_1_6";
  if (A16 == 5 && B8 == 6) return "rooted_not_5_6";
  if (A32 == 5 && B16 == 1) return "rooted_not_5_1";
  if (A16 == 11 && B8 != 2 && B8 != 6 && B8 != 7) return "rooted_eleven";
  if ((A32 == 19 || A32 == 27) && B8 != 2 && B8 != 7)
    return "rooted_nineteen_or_twentyseven";
  if (A16 == 15 && B32 == 26) return "no_15_26";
  if (A32 == 15 && B32 == 24) return "no_15_24";
  if (A32 == 31 && B32 == 24) return "no_31_24";
  if (A32 == 1 && B32 == 25) return "no_1_25";
  if (A64 == 1 && B32 == 23) return "no_1_23";
  if (A64 == 33 && B32 == 23) return "no_33_23";
  if (A64 == 5 && B32 == 20) return "no_5_20";
  if (A16 == 3 && B32 == 18) return "no_3_18";
  if (A32 == 9 && B32 == 9) return "no_9_9";
  if (A64 == 21 && B32 == 20) return "no_21_20";
  return nullptr;
}

// Enumerate every legal inverse branch from BB429NewResidue.odd_back/even_back.
// F is always available for odd a; S is also available exactly when b=2 (mod 4).
// For positive-even a, positive_even_eight first forces b=2 (mod 8), then E is unique.
static void dfs(i64 a, i64 b, int depth, int targetDepth, int D,
                Stats& stats, long long& leaves) {
  stats.maxD = max(stats.maxD, D);
  if (const char* why = bad(a, b)) {
    stats.killed[why]++;
    return;
  }
  if (depth == targetDepth) {
    ++leaves;
    return;
  }
  if (a >= 13 && a % 2 == 1) {
    // F: (a,b) <- ((a-3)/2, b+a)
    dfs((a - 3) / 2, b + a, depth + 1, targetDepth, D + 1, stats, leaves);
    if (b % 4 == 2) {
      // S: (a,b) <- ((4a+b-26)/4, (b+4)/2)
      dfs((4 * a + b - 26) / 4, (b + 4) / 2,
          depth + 1, targetDepth, D + 2, stats, leaves);
    }
  } else if (a >= 6 && a % 2 == 0) {
    // E: (a,b) <- ((4a+b-14)/4, b/2)
    dfs((4 * a + b - 14) / 4, b / 2,
        depth + 1, targetDepth, D + 2, stats, leaves);
  } else {
    // An inverse theorem's lower-bound precondition failed; do not count this as closed.
    ++stats.unhandled;
    ++leaves;
  }
}

static inline i64 representativeA(i64 positiveU) {
  // For every u>=1, n=23+32u>=55, so this has the same residues
  // as 13*2^(23+32u)-24u-19 modulo 2^30.
  return 13LL * (1LL << 55) - 24 * positiveU - 19;
}

static long long runClass(i64 u, int depth, Stats& stats) {
  const i64 a = representativeA(u);
  const i64 b = 2 * a - 13;
  long long leaves = 0;
  dfs(a, b, 0, depth, 0, stats, leaves);
  return leaves;
}

static bool findPath(i64 a, i64 b, int depth, int targetDepth, int D,
                     string& path, i64& finalA, i64& finalB, int& finalD) {
  if (bad(a, b)) return false;
  if (depth == targetDepth) {
    finalA = a; finalB = b; finalD = D;
    return true;
  }
  if (a >= 13 && a % 2 == 1) {
    path.push_back('F');
    if (findPath((a - 3) / 2, b + a, depth + 1, targetDepth, D + 1,
                 path, finalA, finalB, finalD)) return true;
    path.pop_back();
    if (b % 4 == 2) {
      path.push_back('S');
      if (findPath((4 * a + b - 26) / 4, (b + 4) / 2,
                   depth + 1, targetDepth, D + 2,
                   path, finalA, finalB, finalD)) return true;
      path.pop_back();
    }
  } else if (a >= 6 && a % 2 == 0) {
    path.push_back('E');
    if (findPath((4 * a + b - 14) / 4, b / 2,
                 depth + 1, targetDepth, D + 2,
                 path, finalA, finalB, finalD)) return true;
    path.pop_back();
  }
  return false;
}

int main() {
  constexpr int K1 = 22, D1 = 12, D2 = 14, D3 = 16;
  const i64 M1 = 1LL << K1;
  const i64 M2 = 1LL << 25;
  const i64 M3 = 1LL << 27;

  vector<i64> open1, open2;
  Stats s1, s2, s3;

  // Stage 1: all u mod 2^22, depth 12. r=0 represents positive multiples;
  // u=0 is handled separately below.
  for (i64 r = 0; r < M1; ++r) {
    const i64 u = (r == 0 ? M1 : r);
    if (runClass(u, D1, s1) > 0) open1.push_back(r);
  }

  // Stage 2: refine each open 2^22 class into its eight 2^25 lifts.
  map<int, long long> hist2;
  long long openClasses25 = 0;
  for (i64 r : open1) {
    int nopen = 0;
    for (i64 k = 0; k < 8; ++k) {
      const i64 s = r + k * M1;
      const i64 u = (s == 0 ? M2 : s);
      if (runClass(u, D2, s2) > 0) {
        ++nopen;
        ++openClasses25;
      }
    }
    ++hist2[nopen];
    if (nopen > 0) open2.push_back(r);
  }

  // Stage 3: refine each open 2^22 class into its 32 2^27 lifts.
  map<int, long long> hist3;
  map<int, long long> openBy64;
  long long openClasses27 = 0, openLeaves27 = 0;
  for (i64 r : open2) {
    int nopen = 0;
    for (i64 k = 0; k < 32; ++k) {
      const i64 s = r + k * M1;
      const i64 u = (s == 0 ? M3 : s);
      const long long leaves = runClass(u, D3, s3);
      if (leaves > 0) {
        ++nopen;
        ++openClasses27;
        openLeaves27 += leaves;
      }
    }
    ++hist3[nopen];
    if (nopen > 0) ++openBy64[int(r % 64)];
  }

  // Exact exceptional parameter u=0: n=23, so use the actual a, not the u>=1 representative.
  const i64 a0 = 13LL * (1LL << 23) - 19;
  const i64 b0 = 2 * a0 - 13;
  Stats s0_14, s0_16;
  long long leaves0_14 = 0, leaves0_16 = 0;
  dfs(a0, b0, 0, D2, 0, s0_14, leaves0_14);
  dfs(a0, b0, 0, D3, 0, s0_16, leaves0_16);

  cout << "stage1 depth12: open mod-2^22 classes=" << open1.size()
       << ", maxD=" << s1.maxD << ", unhandled=" << s1.unhandled << "\n";
  cout << "stage2 depth14: open mod-2^22 base classes=" << open2.size()
       << ", open mod-2^25 classes=" << openClasses25
       << ", maxD=" << s2.maxD << ", unhandled=" << s2.unhandled << "\n";
  cout << "stage2 lift histogram:";
  for (auto [k,v] : hist2) cout << " " << k << ":" << v;
  cout << "\n";
  cout << "stage3 depth16: open mod-2^27 classes=" << openClasses27
       << ", open inverse leaves=" << openLeaves27
       << ", maxD=" << s3.maxD << ", unhandled=" << s3.unhandled << "\n";
  cout << "stage3 lift histogram:";
  for (auto [k,v] : hist3) cout << " " << k << ":" << v;
  cout << "\nopen base classes by u mod64:";
  for (auto [k,v] : openBy64) cout << " " << k << ":" << v;
  cout << "\n";
  cout << "u=0 exact: depth14 leaves=" << leaves0_14
       << ", maxD=" << s0_14.maxD << ", unhandled=" << s0_14.unhandled
       << "; depth16 leaves=" << leaves0_16
       << ", maxD=" << s0_16.maxD << ", unhandled=" << s0_16.unhandled << "\n";

  // The exact u=26 representative closes at depth 9; this does not close its whole mod-64 cylinder.
  Stats s26;
  const long long leaves26 = runClass(26, 9, s26);
  cout << "u=26 exact depth9: leaves=" << leaves26
       << ", rooted_not_5_6 kills=" << s26.killed["rooted_not_5_6"] << "\n";

  // A concrete surviving synthetic inverse path in the u=2330 (mod 2^22) class.
  const i64 sampleU = 2330;
  const i64 sampleA = representativeA(sampleU);
  const i64 sampleB = 2 * sampleA - 13;
  string path;
  i64 finalA = 0, finalB = 0;
  int finalD = 0;
  const bool found = findPath(sampleA, sampleB, 0, D3, 0,
                              path, finalA, finalB, finalD);
  cout << "u=2330 depth16 path found=" << found;
  if (found) {
    cout << " path=" << path << " D=" << finalD
         << " final(a mod64,b mod32)=(" << md(finalA,64)
         << "," << md(finalB,32) << ")";
  }
  cout << "\n";
}
