#include <boost/multiprecision/cpp_int.hpp>
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
#include <unordered_map>
using boost::multiprecision::cpp_int;
using U=uint64_t;
struct Key{U h;int q;bool operator==(const Key&)const=default;};
struct Hash{size_t operator()(const Key&k)const{return k.h^(U(k.q)*0x9e3779b97f4a7c15ULL);}};
struct Trace{cpp_int l,r;int h;};
// Exact half-tape integers; hashes only select candidates, never certify equality.
void solve(int id,const std::string&p,int cap,int lookback){
 std::vector<Trace> tr;tr.reserve(cap+1);
 std::unordered_map<Key,std::vector<int>,Hash> left,right;
 std::vector<std::array<int,22>> mins,maxs;mins.reserve(cap+1);maxs.reserve(cap+1);
 cpp_int L=0,R=0;int q=0,h=0;U lh=0,rh=0;constexpr U P=0x9e3779b97f4a7c15ULL;
 U pinv=1;for(int k=0;k<6;k++)pinv*=2-P*pinv;
 for(int n=0;n<=cap;n++){
  int a=bit_test(L,0),s=2*q+a;int m=3*s;
  if(p[m]=='-'){std::cout<<id<<" hole "<<n<<' '<<s<<'\n'<<std::flush;return;}
  mins.push_back({});maxs.push_back({});mins.back()[0]=maxs.back()[0]=h;
  for(int k=1;(1<<k)<=n+1;k++){
   mins[n][k]=std::min(mins[n][k-1],mins[n-(1<<(k-1))][k-1]);
   maxs[n][k]=std::max(maxs[n][k-1],maxs[n-(1<<(k-1))][k-1]);
  }
  auto extreme=[&](int j,bool r){int k=std::bit_width(unsigned(n-j+1))-1;int t=j+(1<<k)-1;return r?std::min(mins[n][k],mins[t][k]):std::max(maxs[n][k],maxs[t][k]);};
  auto &rs=right[{rh,2*q+a}], &ls=left[{lh,q}];
  for(int k=int(rs.size())-1;k>=0&&k>=int(rs.size())-lookback;k--){int j=rs[k];auto&z=tr[j];if(h<z.h||R!=z.r)continue;int b=extreme(j,true);int bits=z.h-b+1;cpp_int mask=(cpp_int(1)<<bits)-1;if(((L^z.l)&mask)==0){std::cout<<id<<" cycle "<<j<<' '<<n-j<<" 1 "<<b<<'\n'<<std::flush;return;}}
  for(int k=int(ls.size())-1;k>=0&&k>=int(ls.size())-lookback;k--){int j=ls[k];auto&z=tr[j];if(h>z.h||L!=z.l)continue;int b=extreme(j,false);int bits=b-z.h;cpp_int mask=(cpp_int(1)<<bits)-1;if(((R^z.r)&mask)==0){std::cout<<id<<" cycle "<<j<<' '<<n-j<<" 0 "<<b<<'\n'<<std::flush;return;}}
  tr.push_back({L,R,h});rs.push_back(n);ls.push_back(n);
  int w=p[m]-'0';q=p[m+2]-'A';
  if(p[m+1]=='R'){int b=bit_test(R,0);L=(L>>1)<<2;L|=b|(w<<1);R>>=1;lh=b+P*(w+lh-a);rh=(rh-b)*pinv;++h;}
  else{L>>=1;R=(R<<1)|w;lh=(lh-a)*pinv;rh=w+P*rh;--h;}
 }
 std::cout<<id<<" open\n"<<std::flush;
}
int main(int argc,char**argv){int cap=argc>1?std::stoi(argv[1]):100000,lookback=argc>2?std::stoi(argv[2]):32;int id;std::string p;while(std::cin>>id>>p)solve(id,p,cap,lookback);}
