// Independent Machine C mixed96 audit for Agent 3's 128-modulus high-stop family.
// All branches reproduce the original BB6CLine.nextC map as in Agent41 mixed96.cpp.
// Scope: finite abstract graph comparison, never a real blank-TM reachability claim.
#include <cstdint>
#include <iostream>
#include <set>
#include <utility>
#include <vector>

struct Triple { int a, k, c; };

bool nextC(Triple t, Triple& o) {
  int a=t.a, k=t.k, c=t.c;
  if (c==1) { o={a,k+1,0}; return true; }
  if (c==2) return false;
  if (c==3) { o={a,k+2,1}; return true; }
  if (c==0) {
    if (a==0) { o={1,0,2*k+2}; return true; }
    if (a==1 && k==0) { o={5,0,1}; return true; }
    if (a==1) { o={2,2,2*(k-1)+1}; return true; }
    o={a-2,1,2*k+1}; return true;
  }
  if (a==0) {
    if (k%2==0) o={2*k+2,2,c-3};
    else o={2*k+3,0,c};
    return true;
  }
  o={a-1,k+1,c-1}; return true;
}

constexpr int Na=96, Nk=96, Nc=50, N=Na*Nk*Nc;
int residue(int x,int mod) { return (x%mod+mod)%mod; }
int encode(Triple t) {
  return (residue(t.a,96)*Nk+residue(t.k,96))*Nc
    +(t.c<2?t.c:2+residue(t.c-2,48));
}

int main() {
  std::vector<std::uint8_t> reached(N,0);
  std::vector<int> depth(N,-1), queue;
  queue.reserve(N);
  const int root=encode({5,0,1});
  queue.push_back(root); reached[root]=1; depth[root]=0;
  std::uint64_t edges=0;
  for (std::size_t head=0;head<queue.size();head++) {
    int i=queue[head],c=i%Nc,k=i/Nc%Nk,a=i/(Nc*Nk);
    for (int da=0;da<2;da++)
      for (int dk=0;dk<2;dk++)
        for (int dc=0;dc<(c<2?1:2);dc++) {
          Triple out;
          if (!nextC({a+96*da,k+96*dk,c+48*dc},out)) continue;
          ++edges;
          int j=encode(out);
          if (!reached[j]) {
            reached[j]=1; depth[j]=depth[i]+1; queue.push_back(j);
          }
        }
  }
  std::cout<<"mixed96 reached="<<queue.size()<<" edges="<<edges<<"\n";
  if (queue.size()!=260672 || edges!=2022544) return 2;

  // m=6,10,...,386 and j=0,...,383 traverse every (m,j) residue
  // pair modulo 384 satisfying m%4=2, (j+127*m)%128=87.
  // For m>=6, 2^(2m+2) mod 96 equals 64.
  std::set<std::pair<int,int>> cells;
  int instances=0, absent=0;
  for (int m=6;m<390;m+=4)
    for (int j=0;j<384;j++)
      if (residue(j+127*m,128)==87) {
        ++instances;
        int a=residue(2*j+3,96);
        int k=residue(64*(j+3)-(j+3*m+5),96);
        cells.emplace(a,k);
        if (!reached[encode({a,k,0})]) ++absent;
      }
  std::cout<<"family instances="<<instances
           <<" distinct target cells="<<cells.size()
           <<" abstract-missing="<<absent<<"\n";
  for (auto [a,k]:cells) {
    std::cout<<"("<<a<<","<<k<<",0) abstract BFS depth="
             <<depth[encode({a,k,0})]<<"\n";
  }
  if (instances!=288 || cells.size()!=12 || absent!=0) return 3;
  return 0;
}
