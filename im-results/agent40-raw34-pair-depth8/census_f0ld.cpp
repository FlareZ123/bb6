#include <bits/stdc++.h>
using namespace std;

/*
Exact candidate census for the Raw34 pair parent D1=0LF, F0=0LD.
This enumerator is deliberately not a proof: emitted side/closed candidates
must be checked by the Lean source theorems.  It reproduces the exact
first-query depth-six residual list, then exhausts the remaining genuine
queries through complete depth eight.

Source codes are the repository's physical-table encoding.  choiceCodes is
HALT followed by the same state-major 25-way order as BB6Coverage.choices.
*/

struct Snap { int q, h; bitset<4096> ones; };
struct Res { int kind, slot, t; vector<Snap> hist; }; // 0 unknown, 1 halt, 2 long

bitset<4096> rightMask[4096], leftMask[4096];
vector<int> choiceCodes() {
  vector<int> v{1};
  for (int q=0;q<6;q++) {
    v.push_back(2+q); v.push_back(8+q); v.push_back(14+q); v.push_back(20+q);
  }
  return v;
}
const vector<int> CH = choiceCodes();

void initMasks() {
  for (int b=0;b<4096;b++) for (int i=0;i<4096;i++) {
    if (i>=b) rightMask[b].set(i);
    if (i<=b) leftMask[b].set(i);
  }
}
Res trace(const array<int,12>& p, int cap=100) {
  int q=0,h=0; bitset<4096> ones; vector<Snap> hist; hist.reserve(cap+1);
  for (int t=0;t<=cap;t++) {
    hist.push_back({q,h,ones});
    int z=h+2048;
    if (z<0 || z>=4096) { cerr<<"head range exceeded\n"; exit(3); }
    int slot=2*q+(ones[z]?1:0), a=p[slot];
    if (a<=1) return {a==0?0:1,slot,t,move(hist)};
    int v=a-2;
    ones.set(z,v>=12);
    q=v%6; h += v%12>=6 ? 1 : -1;
  }
  return {2,-1,cap+1,move(hist)};
}
bool side(const vector<Snap>& hist, int maxEntry=60, int maxPeriod=30) {
  int me=min<int>(hist.size(),maxEntry);
  for (int e=0;e<me;e++) {
    int rmin=INT_MAX,lmax=INT_MIN;
    for (int j=e+1;j<min<int>(hist.size(),e+maxPeriod+1);j++) {
      int hp=hist[j-1].h; rmin=min(rmin,hp); lmax=max(lmax,hp);
      const auto &a=hist[e], &b=hist[j];
      int delta=b.h-a.h;
      if (a.q!=b.q) continue;
      for (int rr=0;rr<2;rr++) {
        bool right=rr==0;
        if (right ? delta<0 : delta>0) continue;
        int boundary=right?rmin:lmax, bi=boundary+2048;
        if (bi<0 || bi>=4096) continue;
        bitset<4096> shifted = delta>=0 ? (b.ones>>delta) : (b.ones<<(-delta));
        if ((((a.ones^shifted)&(right?rightMask[bi]:leftMask[bi])).none()))
          return true;
      }
    }
  }
  return false;
}
bool closedReachable(const array<int,12>& p) {
  bool seen[6]={true,false,false,false,false,false};
  bool changed=true;
  while (changed) {
    changed=false;
    for (int q=0;q<6;q++) if (seen[q]) for (int bit=0;bit<2;bit++) {
      int a=p[2*q+bit];
      if (a<=1) return false;
      int nq=(a-2)%6;
      if (!seen[nq]) { seen[nq]=true; changed=true; }
    }
  }
  return true;
}
bool closesWithoutE(const array<int,12>& p) {
  static const int qs[]={0,1,2,3,5};
  for (int q:qs) for (int bit=0;bit<2;bit++) {
    int a=p[2*q+bit];
    if (a<=1 || (a-2)%6==4) return false;
  }
  return true;
}

array<int,12> work={21,0,22,0,11,0,16,7,0,0,5,0};
const array<int,12> contiguous={21,14,22,21,11,0,16,7,0,0,5,14};
const array<int,12> alternating={21,7,22,20,11,0,16,7,0,0,5,14};
vector<array<int,12>> rows;
map<string,long long> depth6Stats;

void buildDepth6(int depth) {
  if (work==contiguous) { depth6Stats["contiguousGrowth5"]++; return; }
  if (work==alternating) { depth6Stats["alternatingGrowth5"]++; return; }
  auto r=trace(work);
  if (side(r.hist)) { depth6Stats["cycle"+to_string(depth)]++; return; }
  if (r.kind==1) { depth6Stats["halt"+to_string(depth)]++; return; }
  if (r.kind==2) {
    auto rr=trace(work,1000);
    if (side(rr.hist,500,200)) { depth6Stats["extendedCycle"+to_string(depth)]++; return; }
    if (closesWithoutE(work)) { depth6Stats["closed"+to_string(depth)]++; return; }
    rows.push_back(work); depth6Stats["longResidual"+to_string(depth)]++; return;
  }
  if (depth>=6) {
    rows.push_back(work); depth6Stats["openResidual6"]++; return;
  }
  int s=r.slot;
  for (int code:CH) { work[s]=code; buildDepth6(depth+1); }
  work[s]=0;
}

int main() {
  initMasks();
  buildDepth6(2);
  if (rows.size()!=4274 ||
      depth6Stats["openResidual6"]!=4234 || depth6Stats["longResidual6"]!=40 ||
      depth6Stats["cycle6"]!=10155 || depth6Stats["halt6"]!=604 ||
      depth6Stats["closed6"]!=42 || depth6Stats["extendedCycle6"]!=25) {
    cerr<<"depth-six census mismatch\n"; return 4;
  }

  long long open6=0,long6=0;
  long long side7=0,halt7=0,open7=0,long7=0,extended7=0;
  long long side8=0,halt8=0,long8=0,closed8=0;

  for (auto base:rows) {
    auto r0=trace(base);
    if (r0.kind==2) { long6++; continue; }
    if (r0.kind!=0) { cerr<<"residual invariant\n"; return 5; }
    open6++;
    int s=r0.slot;
    for (int code:CH) {
      auto child=base; child[s]=code;
      auto r=trace(child);
      if (side(r.hist)) { side7++; continue; }
      if (r.kind==1) { halt7++; continue; }
      if (r.kind==2) {
        auto ext=trace(child,1000);
        if (side(ext.hist,500,200)) extended7++;
        else long7++;
        continue;
      }
      open7++;
      int s2=r.slot;
      for (int code2:CH) {
        auto grand=child; grand[s2]=code2;
        auto g=trace(grand);
        if (side(g.hist)) { side8++; continue; }
        if (g.kind==1) { halt8++; continue; }
        if (g.kind!=2) { cerr<<"complete depth-eight machine still unknown\n"; return 6; }
        long8++;
        if (!closedReachable(grand)) {
          cerr<<"long complete machine lacks closed reachable state set\n"; return 7;
        }
        closed8++;
      }
    }
  }

  if (open6!=4234 || long6!=40 ||
      side7!=78968 || halt7!=4234 || open7!=20605 ||
      extended7!=767 || long7!=1276 ||
      side8!=455952 || halt8!=20605 || long8!=38568 || closed8!=38568) {
    cerr<<"depth-seven/eight census mismatch\n"; return 8;
  }

  const long long depth6Physical=4274LL*625;
  const long long unresolvedPhysical=40LL*625 + 1276LL*25;
  const long long classifiedPhysical=depth6Physical-unresolvedPhysical;
  if (depth6Physical!=2671250 || unresolvedPhysical!=56900 ||
      classifiedPhysical!=2614350) return 9;

  cout<<"{\n"
      <<"  \"depth6ResidualRows\": 4274,\n"
      <<"  \"depth6ResidualPhysical\": "<<depth6Physical<<",\n"
      <<"  \"depth6\": {\"open\": "<<open6<<", \"long\": "<<long6<<"},\n"
      <<"  \"depth7\": {\"shortSide\": "<<side7<<", \"halts\": "<<halt7
      <<", \"open\": "<<open7<<", \"extendedSide\": "<<extended7
      <<", \"longResidual\": "<<long7<<"},\n"
      <<"  \"depth8\": {\"shortSide\": "<<side8<<", \"halts\": "<<halt8
      <<", \"long\": "<<long8<<", \"closedReachable\": "<<closed8<<"},\n"
      <<"  \"classifiedPhysicalCandidate\": "<<classifiedPhysical<<",\n"
      <<"  \"remainingPhysicalCandidate\": "<<unresolvedPhysical<<",\n"
      <<"  \"remainingFormula\": \"40*625 + 1276*25\"\n"
      <<"}\n";
}
