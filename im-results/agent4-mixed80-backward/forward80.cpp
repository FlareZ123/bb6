// Finite M80 overapproximation of genuine Machine C accelerator.
// Discovery aid only: rigorous exclusions are established in the Lean
// source-checked reverse-core theorems, independently of this enumerator.
#include <cstdio>
#include <vector>
#include <cstdint>
using u64 = unsigned long long;
struct S { int a,k,c; };
static S step(S t) {
  if (t.c==1) return {t.a,t.k+1,0};
  if (t.c==2) return {-1,-1,-1};
  if (t.c==3) return {t.a,t.k+2,1};
  if (t.c==0) {
    if (t.a==0) return {1,0,2*t.k+2};
    if (t.a==1) return t.k==0?S{5,0,1}:S{2,2,2*t.k-1};
    return {t.a-2,1,2*t.k+1};
  }
  if (t.a==0) return t.k%2==0?S{2*t.k+2,2,t.c-3}:S{2*t.k+3,0,t.c};
  return {t.a-1,t.k+1,t.c-1};
}
constexpr int M=80,C=84,N=M*M*C;
static int idx(S t) {
  int ic=t.c<4?t.c:4+t.c%80;
  return (t.a%80*M+t.k%80)*C+ic;
}
int main() {
  std::vector<char> seen(N);
  std::vector<int> queue;
  queue.reserve(N);
  int root=idx({5,0,1});
  seen[root]=1;
  queue.push_back(root);
  u64 edges=0;
  for (size_t cur=0; cur<queue.size(); cur++) {
    int ix=queue[cur],ci=ix%C,k=(ix/C)%M,a=(ix/C)/M;
    int c0=ci<4?ci:(ci<8?ci-4+80:ci-4);
    for(int ia=0;ia<2;ia++)for(int ik=0;ik<2;ik++)
      for(int ic=0;ic<(ci<4?1:2);ic++) {
        S v=step({a+80*ia,k+80*ik,c0+80*ic});
        if(v.a<0)continue;
        edges++;
        int j=idx(v);
        if(!seen[j]) { seen[j]=1; queue.push_back(j); }
      }
  }
  std::printf("M80 graph: %zu reached / %d states, %llu edges\n",
              queue.size(),N,edges);
  std::printf("Absent first-family low residues k mod80:");
  for(int k=0;k<M;k++)if(!seen[idx({1,k,0})])std::printf(" %d",k);
  std::puts("");
  int second_excluded=0;
  for(int u=0;u<M;u++)for(int m=0;m<M;m++) {
    int pow=m%2?16:64;
    int a=(2*u+1)%M;
    int k=(pow*(u+2)-u-3*m-4+100000*M)%M;
    if(!seen[idx({a,k,0})])second_excluded++;
  }
  std::printf("Projected second stopping candidate pairs excluded: %d / 6400\n",
              second_excluded);
  return queue.size()==311163 && edges==2443968 && second_excluded==2650 ? 0 : 1;
}
