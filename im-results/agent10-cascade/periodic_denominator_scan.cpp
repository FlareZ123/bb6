#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
using U=std::uint64_t;
struct Edge {U n; unsigned v,d;};
Edge edge(U n,U q){U m=n+q;unsigned w=std::countr_zero(m);m>>=w;unsigned v=1;while(2*m<q && v<w){m*=3;++v;}if(2*m<q || m>=q)return {0,0,0};return {m,v,w-v};}
std::vector<U> divisors(U n){std::vector<U>a{1};for(U p=2;p*p<=n;++p){if(n%p)continue;unsigned e=0;while(n%p==0){n/=p;++e;}if(p==3)continue;size_t s=a.size();U pp=1;for(unsigned i=0;i<2*e;++i){pp*=p;for(size_t j=0;j<s;++j)a.push_back(a[j]*pp);}}if(n>1 && n!=3){size_t s=a.size();for(size_t j=0;j<s;++j)a.push_back(a[j]*n);for(size_t j=0;j<s;++j)a.push_back(a[j]*n*n);}return a;}
struct Stats {U nodes=0, cycles=0, matches=0;};
Stats scan(U q,unsigned D){Stats st;if(q==1)return st;U lo=(q/2)|1;if(2*lo<q)lo+=2;U len=(q-lo+1)/2;std::vector<std::uint8_t> color(len);std::vector<U> path;
 auto ix=[&](U n){return (n-lo)/2;};
 for(U n=lo;n<q;n+=2){if(color[ix(n)])continue;if(std::gcd(n,q)!=1){color[ix(n)]=2;continue;}++st.nodes;path.clear();U x=n;
  while(x && !color[ix(x)]){color[ix(x)]=1;path.push_back(x);auto e=edge(x,q);x=e.n;}
  if(x && color[ix(x)]==1){++st.cycles;U y=x;unsigned ds=0,l=0;do{auto e=edge(y,q);ds+=e.d;++l;y=e.n;}while(y!=x);if(ds==D){++st.matches;std::cout<<"candidate D="<<D<<" q="<<q<<" n="<<x<<" L="<<l<<"\n";}}
  for(U y:path)color[ix(y)]=2;
 }
 return st;}
int main(int argc,char**argv){unsigned maxD=argc>1?std::stoul(argv[1]):14;if(maxD>14){std::cerr<<"limit D to 14 for memory and runtime\n";return 1;}for(unsigned D=1;D<=maxD;++D){auto ds=divisors((U(1)<<D)-1);Stats all;U maxq=0;for(U q:ds){maxq=std::max(maxq,q);auto s=scan(q,D);all.nodes+=s.nodes;all.cycles+=s.cycles;all.matches+=s.matches;}std::cout<<"D="<<D<<" denominators="<<ds.size()<<" max="<<maxq<<" starts="<<all.nodes<<" cycles="<<all.cycles<<" primitive_D_matches="<<all.matches<<std::endl;}}
