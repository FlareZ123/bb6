#include <array>
#include <cstdint>
#include <iostream>
#include <vector>

namespace {
constexpr unsigned kUnknown = 255;
constexpr unsigned kAssigned = 4;
constexpr unsigned kSteps = 20;
using Partial = std::array<unsigned,12>;

struct Config { unsigned state; int head; std::uint64_t ones;
  bool operator==(const Config& other) const {
    return state == other.state && head == other.head && ones == other.ones;
  }
};

unsigned successor(unsigned a) { return (a >= 13 ? a - 13 : a - 1) / 2; }
bool right(unsigned a) { return ((a >= 13 ? a - 13 : a - 1) % 2) != 0; }

Config next(Config c, unsigned a) {
  const auto b = std::uint64_t{1} << (c.head + 20);
  if (a >= 13) c.ones |= b;
  else c.ones &= ~b;
  c.head += right(a) ? 1 : -1;
  c.state = successor(a);
  return c;
}

void dfs(Config c, unsigned depth, unsigned count, bool readOne,
         Partial& p, std::vector<Config>& trace, std::vector<Partial>& out) {
  for (const auto& prev : trace) {
    if (prev == c) {
      if (count >= 3 && count <= kAssigned && readOne) out.push_back(p);
      return;
    }
  }
  if (depth >= kSteps) return;
  const auto one = (c.ones >> (c.head + 20)) & 1u;
  const auto slot = 2u * c.state + static_cast<unsigned>(one);
  trace.push_back(c);
  if (p[slot] == kUnknown) {
    if (count < kAssigned) {
      for (unsigned a=1; a<=24; ++a) {
        p[slot] = a;
        dfs(next(c,a),depth+1,count+1,readOne || one,p,trace,out);
      }
      p[slot] = kUnknown;
    }
  } else {
    dfs(next(c,p[slot]),depth+1,count,readOne,p,trace,out);
  }
  trace.pop_back();
}

bool pristineCycle(const std::array<unsigned,6>& d) {
  unsigned state=0, seen=0;
  for (;;) {
    if ((seen & (1u<<state)) != 0) return true;
    seen |= 1u<<state;
    unsigned a=d[state];
    if (a==0 || a>=13) return false;
    state=successor(a);
  }
}
bool closedRayCycle(const std::array<unsigned,6>& d, unsigned state, bool dir) {
  unsigned seen=0;
  for (;;) {
    if ((seen & (1u<<state)) != 0) return true;
    seen |= 1u<<state;
    unsigned a=d[state];
    if (a==0 || right(a)!=dir) return false;
    state=successor(a);
  }
}
bool freshRay(std::uint64_t ones,int head,bool dir) {
  auto pos=static_cast<unsigned>(head+6);
  auto mask=dir ? (8191ull & ~((1ull<<pos)-1)) : ((1ull<<(pos+1))-1);
  return (ones & mask)==0;
}

// Reproduce Agent32's exact six-read-zero-sufficient-condition classifier.
bool remainsOpenAtReadOne(const std::array<unsigned,6>& d) {
  if (pristineCycle(d)) return false;
  unsigned state=0;
  std::uint64_t ones=0;
  int head=0;
  for (unsigned step=0; step<=6; ++step) {
    std::uint64_t bit=1ull<<(head+6);
    if ((ones&bit) != 0) return true;
    if ((freshRay(ones,head,true) && closedRayCycle(d,state,true)) ||
        (freshRay(ones,head,false) && closedRayCycle(d,state,false))) return false;
    if (step==6) return false;
    auto a=d[state];
    if (a==0) return false;
    if (a>=13) ones|=bit;
    else ones&=~bit;
    head+=right(a)?1:-1;
    state=successor(a);
  }
  return false;
}
} // namespace

int main() {
  Partial p;
  p.fill(kUnknown);
  std::vector<Config> trace;
  std::vector<Partial> triples;
  dfs(Config{0,0,0},0,0,false,p,trace,triples);
  if (triples.size()!=4600) {
    std::cerr<<"unexpected lasso count "<<triples.size()<<'\n';
    return 1;
  }
  unsigned n3=0, n4=0;
  std::uint64_t fullMass=0;
  for (unsigned i=0;i<triples.size();++i) {
    auto& a=triples[i];
    unsigned nzero=0,none=0;
    for (unsigned j=0;j<12;++j) {
      if (a[j]!=kUnknown) ((j%2==0)?nzero:none)++;
    }
    if (nzero+none==3) {
      ++n3; fullMass+=3814697265625ull;
      if (nzero!=2 || none!=1) return 2;
    } else if (nzero+none==4) {
      ++n4; fullMass+=152587890625ull;
      if (nzero < 2 || none < 1) return 2;
    } else return 2;
    for (unsigned k=i+1;k<triples.size();++k) {
      bool clash=false;
      for (unsigned j=0;j<12;++j) {
        if (a[j]!=kUnknown && triples[k][j]!=kUnknown &&
            a[j]!=triples[k][j]) clash=true;
      }
      if (!clash) return 3;
    }
  }
  if (n3!=90 || n4!=4510) return 6;
  std::uint64_t tested=0;
  for (const auto& a:triples) {
    unsigned free=0;
    for (unsigned q=0;q<6;++q) free+=(a[2*q]==kUnknown);
    unsigned nChoices=1;
    for (unsigned k=0;k<free;++k) nChoices*=25;
    for (unsigned code=0;code<nChoices;++code) {
      auto value=code;
      std::array<unsigned,6> rows{};
      for (unsigned q=0;q<6;++q) {
        if (a[2*q]==kUnknown) {
          rows[q]=value%25;
          value/=25;
        } else rows[q]=a[2*q];
      }
      if (!remainsOpenAtReadOne(rows)) {
        std::cerr<<"violated zero-row disjointness for code "<<code<<'\n';
        return 4;
      }
      ++tested;
    }
  }
  std::cout << "three-slot read-one lassos: " << n3 << " four-slot: " << n4 << '\n'
            << "all pairwise conflicting: true\n"
            << "zero-row completions tested open: " << tested << '\n'
            << "full raw-table mass: " << fullMass << '\n';
  return tested==371875000ull && fullMass==1031494140625000ull ? 0 : 5;
}
