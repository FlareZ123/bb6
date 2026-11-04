#include <cstdint>
#include <cstdio>

constexpr int M = 80, C = 84;
struct State { long long a,k,c; };
static State step(State v, bool& halt) {
  auto [a,k,c] = v;
  halt = false;
  if (c==1) return {a,k+1,0};
  if (c==2) { halt=true; return {}; }
  if (c==3) return {a,k+2,1};
  if (c==0) {
    if (a==0) return {1,0,2*k+2};
    if (a==1) return k==0 ? State{5,0,1} : State{2,2,2*k-1};
    return {a-2,1,2*k+1};
  }
  if (a==0) return k%2==0 ? State{2*k+2,2,c-3} : State{2*k+3,0,c};
  return {a-1,k+1,c-1};
}
static bool bad(State p) {
  const int a=p.a%M, k=p.k%M, c=p.c%M;
  if (p.c==2) return false;
  if (p.c<4) {
    int s=(k+c)%M;
    return (a==41&&s==15) || (a==26&&s%40==19) || (a==66&&s%40==39);
  }
  int d=(a+M-c)%M, t=(a+k)%M;
  return (d==0&&t%40==31)||(d==23&&t%40==2)||(d==38&&t==53)||
    (d==40&&t%40==11)||(d==63&&t%40==22)||(d==65&&t%40==25);
}
int main() {
  uint64_t edges=0, badstates=0;
  for(int a=0;a<M;a++)for(int k=0;k<M;k++)for(int ci=0;ci<C;ci++) {
    long long c0=ci<4?ci:(ci-4<4 ? ci-4+80 : ci-4);
    State q{a,k,c0};
    bool qbad=bad(q);
    badstates+=qbad;
    for(int ia=0;ia<2;ia++)for(int ik=0;ik<2;ik++)for(int ic=0;ic<(ci<4?1:2);ic++) {
      State before{a+ia*M,k+ik*M,c0+ic*M};
      bool halt=false;
      State after=step(before,halt);
      if(halt)continue;
      edges++;
      if(bad(after)&&!bad(before)) {
        std::printf("FAIL (%lld,%lld,%lld)->(%lld,%lld,%lld)\n",
          before.a,before.k,before.c,after.a,after.k,after.c);
        return 1;
      }
      if(bad(before)!=qbad) {
        std::printf("FAIL nonuniform bad preimage (%lld,%lld,%lld)\n",before.a,before.k,before.c);
        return 1;
      }
    }
  }
  std::printf("M80 reverse closure: %llu bad quotient states, %llu tested concrete edges, rootBad=%d\n",
    static_cast<unsigned long long>(badstates),static_cast<unsigned long long>(edges),bad({5,0,1}));
  return badstates==895 && edges==4172800 && !bad({5,0,1}) ? 0 : 1;
}
