// Exact finite certificate for Machine C's eventual fourth-return image.
// The section inverse formulas are proved in SectionAllInverse.lean.
// The three-return period is derived in the accompanying README.
// C++17, optional OpenMP; no external libraries or random sampling.
#include <cstdint>
#include <cstdio>
#include <vector>
#include <cstdlib>
#include <cstring>
#include <algorithm>
using u64 = std::uint64_t;

static std::uint8_t h2[64*64];
static std::vector<std::uint8_t> h3(32768*128);
static int val2(u64 n) {
  int e=0;
  while ((n&1)==0) { ++e; n >>= 1; }
  return e;
}
static bool image1(u64 a,u64 k) {
  return k%2==0 || (a+k)%4==0 || (a+k)%4==3;
}
static bool H2(int sm,int ym) {
  const u64 s=256+(sm&63),y=64+(ym&63),x=s-y,q=s+(s&1);
  const int v=val2(q);
  if (v>=5) return true;
  if ((y&1)==0 && image1(s-2,(y-2)/2)) return true;
  for (int n=0;n+1<v;++n) {
    if (((s&1)?n:n+1)%2 != x%2) continue;
    const u64 a=(q>>(n+1))-((s&1)?3:2);
    const u64 k=(s+y-a-7-3*n)/2;
    if (image1(a,k)) return true;
  }
  return false;
}
static bool H3(int sm,int ym) {
  const u64 s=(1u<<18)+(sm&32767),y=512+(ym&127);
  const u64 q=s+(s&1);
  const int v=val2(q);
  if (v>=10) return true;
  if ((y&1)==0) {
    const u64 a=s-2,k=(y-2)/2;
    if (h2[((a+k)&63)*64+(k&63)]) return true;
  }
  for (int n=0;n+1<v;++n) {
    if (((s&1)?n:n+1)%2 != (s-y)%2) continue;
    const u64 a=(q>>(n+1))-((s&1)?3:2);
    const u64 k=(s+y-a-7-3*n)/2;
    if (h2[((a+k)&63)*64+(k&63)]) return true;
  }
  return false;
}
static bool H4(u64 q,int p,u64 y,int depthCap=100) {
  const u64 s=q-p;
  if ((y&1)==0) {
    const u64 a=s-2,k=(y-2)/2;
    if (h3[((a+k)&32767)*128+(k&127)]) return true;
  }
  const int v=val2(q);
  for (int n=0;n+1<v && n<=depthCap;++n) {
    if ((p?n:n+1)%2 != (s-y)%2) continue;
    const u64 a=(q>>(n+1))-(p?3:2);
    const u64 k=(s+y-a-7-3*n)/2;
    if (h3[((a+k)&32767)*128+(k&127)]) return true;
  }
  return false;
}
static void initialize() {
  u64 h2hits=0,h3hits=0,h3odd=0;
  for (int sm=0;sm<64;++sm)
    for (int ym=0;ym<64;++ym)
      h2hits+=(h2[sm*64+ym]=H2(sm,ym));
  for (int sm=0;sm<32768;++sm)
    for (int ym=0;ym<128;++ym)
      h3hits+=(h3[sm*128+ym]=H3(sm,ym));
  for (int sm=0;sm<32768;++sm)
    for (int ym=0;ym<128;++ym)
      if (((sm-ym)&1)!=0) h3odd+=h3[sm*128+ym];
  std::fprintf(stderr,"H2=%llu/4096 H3=%llu/4194304 H3_odd=%llu/2097152\n",
    (unsigned long long)h2hits,(unsigned long long)h3hits,(unsigned long long)h3odd);
  if (h2hits!=2448 || h3hits!=2089368 || h3odd!=1041072) std::abort();
}
static void row(int v,int targetOdd) {
  u64 hits=0;
  // For fixed valuation v<=17, U=Q/2^v ranges over all odd residues modulo 2^15.
  // The first-counter parity fixes the right-coordinate parity from S=Q-p.
  #pragma omp parallel for reduction(+:hits) schedule(dynamic,1)
  for (int ui=0;ui<16384;++ui) {
    const u64 u=(1u<<20)+2*ui+1;
    const u64 q=u<<v;
    for (int p=0;p<2;++p)
      for (int yi=0;yi<32768;++yi) {
        const u64 y=(1u<<20)+2u*yi+((p+targetOdd)&1);
        hits+=H4(q,p,y);
      }
  }
  std::printf("targetOdd=%d v=%d accepted=%llu total=1073741824\n",
    targetOdd,v,(unsigned long long)hits);
  std::fflush(stdout);
}
static void high(int v) {
  // For v>=18, among genuine source parents depths n<=11 suffice.
  // For v=18..27, U mod 2^(28-v) and y mod 2^16 suffice.
  // For v>=28 the v=28 row covers all since U's terms vanish mod 2^16.
  const int bits=std::max(1,28-v);
  const int oddCount=(1<<bits)/2;
  u64 failures=0;
  #pragma omp parallel for reduction(+:failures) schedule(dynamic,1)
  for (int ui=0;ui<oddCount;++ui) {
    const u64 u=(1u<<20)+2*ui+1;
    const u64 q=u<<v;
    for (int p=0;p<2;++p)
      for (int ym=0;ym<65536;++ym) {
        const u64 y=(1u<<20)+ym;
        failures+=!H4(q,p,y,11);
      }
  }
  std::printf("high v=%d tests=%llu failures=%llu\n",
    v,(unsigned long long)oddCount*2*65536,(unsigned long long)failures);
  if (failures!=0) std::abort();
  std::fflush(stdout);
}
int main(int argc,char**argv) {
  initialize();
  if (argc>1 && std::strcmp(argv[1],"period")==0) {
    u64 mismatches=0;
    #pragma omp parallel for reduction(+:mismatches) schedule(static)
    for (int sm=0;sm<(1<<17);++sm)
      for (int ym=0;ym<128;++ym)
        mismatches+=H3(sm,ym)!=bool(h3[(sm&32767)*128+ym]);
    std::printf("H3 period mismatches=%llu /16777216\n",
      (unsigned long long)mismatches);
    if (mismatches!=0) std::abort();
  } else if (argc>1 && std::strcmp(argv[1],"high")==0) {
    const int v=argc>2?std::atoi(argv[2]):18;
    high(v);
  } else if (argc>1 && std::strcmp(argv[1],"row")==0) {
    const int v=argc>2?std::atoi(argv[2]):1;
    const int parity=argc>3?std::atoi(argv[3]):1;
    row(v,parity);
  } else {
    for (int v=1;v<=17;++v) row(v,1);
    for (int v=1;v<=17;++v) row(v,0);
    for (int v=18;v<=28;++v) high(v);
  }
}
