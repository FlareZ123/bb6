#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <string>
#include <vector>

using Mask = std::uint64_t;
struct Inst { bool defined; int write; bool right; int next; };
struct Rule { int dst, src, off; };
struct Cert {
  int d = 0;
  bool rev = false;
  std::vector<int> dfa;
  std::vector<Mask> rows0, rows1;
  Mask z = 0;
};

static constexpr std::array<Inst, 12> machine{{
  {true, 1, true, 1},   // A0 = 1RB
  {true, 0, false, 2},  // A1 = 0LC
  {true, 1, true, 2},   // B0 = 1RC
  {true, 0, true, 2},   // B1 = 0RC
  {true, 1, false, 3},  // C0 = 1LD
  {true, 0, true, 1},   // C1 = 0RB
  {true, 1, false, 0},  // D0 = 1LA
  {true, 0, false, 4},  // D1 = 0LE
  {true, 1, false, 3},  // E0 = 1LD
  {true, 1, false, 5},  // E1 = 1LF
  {true, 1, false, 3},  // F0 = 1LD
  {false, 0, false, 0}  // F1 is the single missing instruction
}};

static inline Mask bit(int i) { return Mask(1) << i; }

bool fastValid(int d, const std::vector<int>& dfa, bool rev,
               const std::vector<Mask>& rows, Mask z) {
  const int N = 6 * d + 1, H = N - 1;
  if ((int)dfa.size() != 2 * d || dfa[0] != 0) return false;
  for (int x : dfa) if (x < 0 || x >= d) return false;
  if (!(z & bit(H)) || (z & bit(0))) return false;

  // zero(s) iff there is a zero-labelled edge from s into zero.
  for (int s = 0; s < N; ++s) {
    bool rhs = false;
    Mask x = rows[s] & z;
    rhs = (x != 0);
    const bool lhs = (z & bit(s)) != 0;
    if (lhs != rhs) return false;
  }
  // The distinguished None state has a self-loop for both labels.
  for (int a = 0; a < 2; ++a)
    if (!(rows[a * N + H] & bit(H))) return false;

  auto edge = [&](int a, int s, int t) {
    return (rows[a * N + s] & bit(t)) != 0;
  };
  auto push = [&](int l, int a) { return dfa[2 * l + a]; };

  for (int l = 0; l < d; ++l) {
    for (int q = 0; q < 6; ++q) {
      for (int a = 0; a < 2; ++a) {
        const Inst& m = machine[2 * q + a];
        const int src = 6 * l + q;
        if (!m.defined) {
          if (!edge(a, src, H)) return false;
        } else if (m.right != rev) {
          const int dst = 6 * push(l, m.write) + m.next;
          if (!edge(a, src, dst)) return false;
        } else {
          for (int j = 0; j < d; ++j) {
            for (int b = 0; b < 2; ++b) {
              if (push(j, b) != l) continue;
              const int midSrc = 6 * j + m.next;
              for (int v = 0; v < N; ++v) {
                if (!edge(b, midSrc, v)) continue;
                for (int t = 0; t < N; ++t) {
                  if (edge(m.write, v, t) && !edge(a, src, t))
                    return false;
                }
              }
            }
          }
        }
      }
    }
  }
  return true;
}

bool synthesize(const std::vector<int>& dfa, bool rev, Cert& cert) {
  const int d = (int)dfa.size() / 2;
  const int N = 6 * d + 1, H = N - 1;
  const Mask halt = bit(H);
  std::vector<Mask> rows(2 * N, 0);
  rows[H] = halt;
  rows[N + H] = halt;
  std::vector<Rule> rules;
  std::vector<std::vector<int>> pre(d);
  for (int j = 0; j < d; ++j)
    for (int b = 0; b < 2; ++b)
      pre[dfa[2 * j + b]].push_back(2 * j + b);

  for (int l = 0; l < d; ++l) {
    for (int q = 0; q < 6; ++q) {
      for (int a = 0; a < 2; ++a) {
        const Inst& m = machine[2 * q + a];
        const int dst = a * N + 6 * l + q;
        if (!m.defined) {
          rows[dst] = halt;
        } else if (m.right != rev) {
          rows[dst] = bit(6 * dfa[2 * l + m.write] + m.next);
        } else {
          for (int jb : pre[l]) {
            const int j = jb / 2, b = jb % 2;
            rules.push_back({dst, b * N + 6 * j + m.next, m.write * N});
          }
        }
      }
    }
  }

  bool converged = false;
  for (int iter = 0; iter <= 2 * N * N; ++iter) {
    bool changed = false;
    for (const Rule& r : rules) {
      Mask x = rows[r.src], v = rows[r.dst];
      while (x) {
        const int i = __builtin_ctzll(x);
        x &= x - 1;
        v |= rows[r.off + i];
      }
      if (v != rows[r.dst]) {
        rows[r.dst] = v;
        changed = true;
      }
    }
    if (!changed) { converged = true; break; }
  }
  if (!converged) return false;

  Mask z = halt;
  for (int iter = 0; iter <= N; ++iter) {
    Mask next = z;
    for (int i = 0; i < N; ++i)
      if (rows[i] & z) next |= bit(i);
    if (next == z) break;
    z = next;
  }
  if (z & bit(0)) return false;
  if (!fastValid(d, dfa, rev, rows, z)) return false;

  cert.d = d;
  cert.rev = rev;
  cert.dfa = dfa;
  cert.rows0.assign(rows.begin(), rows.begin() + N);
  cert.rows1.assign(rows.begin() + N, rows.end());
  cert.z = z;
  return true;
}

void writeResult(const std::string& status, int tested, const Cert* c) {
  std::ofstream out("/tmp/f421-far.json");
  out << "{\n  \"machine\": \"1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---\",\n";
  out << "  \"status\": \"" << status << "\",\n  \"dfa_size\": 6,\n";
  out << "  \"tested_dfas\": " << tested;
  if (c) {
    out << ",\n  \"reverse\": " << (c->rev ? "true" : "false");
    auto arr = [&](const char* name, const std::vector<Mask>& xs) {
      out << ",\n  \"" << name << "\": [";
      for (std::size_t i = 0; i < xs.size(); ++i) {
        if (i) out << ", ";
        out << xs[i];
      }
      out << "]";
    };
    out << ",\n  \"dfa\": [";
    for (std::size_t i = 0; i < c->dfa.size(); ++i) {
      if (i) out << ", ";
      out << c->dfa[i];
    }
    out << "]";
    arr("T0", c->rows0);
    arr("T1", c->rows1);
    out << ",\n  \"zero_mask\": " << c->z;
  }
  out << "\n}\n";
}

int main() {
  constexpr int d = 6;
  std::vector<int> pre{0};
  int tested = 0;
  bool found = false;
  Cert cert;
  const auto start = std::chrono::steady_clock::now();

  std::function<void(int, int)> dfs = [&](int k, int mx) {
    if (found) return;
    if (k == 0) {
      if (mx + 1 != d) return;
      ++tested;
      for (bool rev : {true, false}) {
        if (synthesize(pre, rev, cert)) { found = true; break; }
      }
      if (tested % 10000 == 0) {
        const double sec = std::chrono::duration<double>(
          std::chrono::steady_clock::now() - start).count();
        std::cout << "tested=" << tested << " elapsed_seconds=" << sec << std::endl;
      }
      return;
    }
    if ((int)pre.size() / 2 > mx) return;
    for (int x = 0; x < d && x <= mx + 1 && !found; ++x) {
      pre.push_back(x);
      dfs(k - 1, std::max(mx, x));
      pre.pop_back();
    }
  };

  dfs(2 * d - 1, 0);
  const double sec = std::chrono::duration<double>(
    std::chrono::steady_clock::now() - start).count();
  if (found) {
    std::cout << "CERTIFICATE FOUND: d=6 reverse=" << cert.rev << " dfa=";
    for (int x : cert.dfa) std::cout << x << ",";
    std::cout << " zero_mask=" << cert.z << " elapsed_seconds=" << sec << std::endl;
    writeResult("certificate-found-fastValid-checked", tested, &cert);
    return 0;
  }
  std::cout << "NO CERTIFICATE: all canonical d=6 DFAs tested=" << tested
            << " elapsed_seconds=" << sec << std::endl;
  writeResult("no-d6-certificate", tested, nullptr);
  return 0;
}
