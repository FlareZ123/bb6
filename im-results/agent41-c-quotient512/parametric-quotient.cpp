#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
using namespace std;

// Exact finite overapproximation for the Machine C accelerated triple.
int main(int argc, char** argv) {
  if (argc < 2 || argc > 3) return 1;
  const int m = atoi(argv[1]), base = argc > 2 ? atoi(argv[2]) : 8;
  const int n = m + base;
  if (m < 8 || (m & 1) || base < 8 || base > m ||
      int64_t(n) * n * n > 2000000000LL) return 2;
  const int total = n*n*n, n2 = n*n;
  auto q = [m,base](int x) {return x < base ? x : base + (x-base)%m;};
  auto enc = [n,n2](int a,int k,int c) {return a*n2+k*n+c;};
  vector<uint64_t> bits((total+63LL)/64);
  auto has = [&](int x) {return (bits[x>>6]>>(x&63))&1;};
  auto add = [&](int x) {
    uint64_t &v=bits[x>>6], b=uint64_t(1)<<(x&63);
    if (v&b) return false;
    v|=b;return true;
  };
  vector<int> queue;
  queue.reserve(total/2);
  const int start=enc(5,0,1);
  add(start); queue.push_back(start);
  uint64_t edges=0;
  auto started=chrono::steady_clock::now();
  for (size_t head=0;head<queue.size();++head) {
    const int id=queue[head], a=id/n2,k=id/n%n,c=id%n;
    for(int ai=0;ai<(a<base?1:2);++ai)
    for(int ki=0;ki<(k<base?1:2);++ki)
    for(int ci=0;ci<(c<base?1:2);++ci) {
      const int A=a+ai*m,K=k+ki*m,C=c+ci*m;
      int aa=0,kk=0,cc=0;
      if(C==2) continue;
      if(C==1 || C==3) {aa=A;kk=K+(C==1?1:2);cc=C==1?0:1;}
      else if(C==0) {
        if(A==0) {aa=1;kk=0;cc=2*K+2;}
        else if(A==1) {aa=K==0?5:2;kk=K==0?0:2;cc=K==0?1:2*K-1;}
        else {aa=A-2;kk=1;cc=2*K+1;}
      } else if(A==0) {
        if((K&1)==0) {aa=2*K+2;kk=2;cc=C-3;}
        else {aa=2*K+3;kk=0;cc=C;}
      } else {aa=A-1;kk=K+1;cc=C-1;}
      ++edges;
      const int out=enc(q(aa),q(kk),q(cc));
      if(add(out)) queue.push_back(out);
    }
  }
  const double seconds=chrono::duration<double>(chrono::steady_clock::now()-started).count();
  printf("B=%d M=%d total=%d reached=%zu edges=%llu time=%.3f\n",
    base,m,total,queue.size(),(unsigned long long)edges,seconds);
  printf("reset=");
  for(int j=0;j<m;++j)
    if(!has(enc(q(2*(j+m)+1),q(3*(j+m)+4),0))) printf("%d,",j);
  printf("\nside=");
  for(int j=0;j<m;++j)
    if(!has(enc(0,q(4*(j+m)),q(24*(j+m)+23)))) printf("%d,",j);
  puts("");
}
