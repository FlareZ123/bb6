#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <random>
#include <string>
#include <vector>
using namespace std;

struct Result {
  int n = -1;
  string suffix;
  int64_t steps = 0;
  char status = '?'; // R=return, H=halt, O=out-of-window, L=nonblank left, T=fuel
};

const string table[6][2] = {
  {"1RB", "0RE"}, {"1LC", "0RA"}, {"1LA", "1LD"},
  {"1LC", "1LF"}, {"0LC", "0LB"}, {"1LE", "---"}
};

Result macro(int n, const string& r, int64_t fuel = 2000000) {
  const int pad = max(5000, n * 10 + 100);
  const int size = 2 * pad + n + int(r.size()) + 100;
  vector<unsigned char> tape(size, 0);
  for (int j = 1; j <= n; ++j) tape[pad+j] = 1;
  for (int j = 0; j < int(r.size()); ++j)
    tape[pad+n+1+j] = (r[j] == '1');

  int p = pad, state = 5;
  for (int64_t t = 0; t < fuel; ++t) {
    if (t && state == 5 && p < pad && tape[p] == 0) {
      for (int j = 0; j < p; ++j)
        if (tape[j]) return {-1, "", t, 'L'};
      int i = p+1;
      while (i < size && tape[i]) ++i;
      int last = size-1;
      while (last >= i && !tape[last]) --last;
      string suffix;
      for (int j = i; j <= last; ++j)
        suffix += char('0' + tape[j]);
      return {i-p-1, suffix, t, 'R'};
    }
    if (p <= 0 || p >= size-1) return {-1, "", t, 'O'};
    const string& op = table[state][tape[p]];
    if (op == "---") return {-1, "", t, 'H'};
    tape[p] = op[0]-'0';
    p += (op[1]=='R' ? 1 : -1);
    state = op[2]-'A';
  }
  return {-1, "", fuel, 'T'};
}

int main() {
  mt19937 rng(94929);
  int64_t compared=0, failures=0, incomplete=0, both_halt=0;
  for (int n=5; n<=14; ++n) {
    for (int len=1; len<=90; ++len) {
      for (int sample=0; sample<120; ++sample) {
        string suffix = "0";
        for (int i=1; i<len; ++i)
          suffix += (rng() & 1) ? '1' : '0';
        Result a=macro(n,suffix), b=macro(n+3,suffix);
        if (a.status=='T' || b.status=='T' || a.status=='O' ||
            b.status=='O' || a.status=='L' || b.status=='L') {
          ++incomplete;
          continue;
        }
        ++compared;
        if (a.status=='H' && b.status=='H') {
          ++both_halt;
          continue;
        }
        if (a.status!='R' || b.status!='R' ||
            b.n!=a.n+8 || b.suffix!=a.suffix) {
          ++failures;
          if (failures<40)
            printf("FAIL n=%d suffix=%s a=(%c,%d,%s) b=(%c,%d,%s)\n",
                   n,suffix.c_str(),a.status,a.n,a.suffix.c_str(),
                   b.status,b.n,b.suffix.c_str());
        }
      }
    }
    fprintf(stderr,"n=%d compared=%lld failures=%lld incomplete=%lld\n",
            n,(long long)compared,(long long)failures,(long long)incomplete);
  }
  printf("FINAL compared=%lld failed=%lld incomplete=%lld bothhalting=%lld\n",
         (long long)compared,(long long)failures,
         (long long)incomplete,(long long)both_halt);
}
