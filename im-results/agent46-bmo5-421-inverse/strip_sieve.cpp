#include <boost/multiprecision/cpp_int.hpp>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <algorithm>
#include <cstdlib>
using boost::multiprecision::cpp_int;
using u64=std::uint64_t; using u128=__uint128_t; using i128=__int128_t;
constexpr u64 bigM=4052555153018976267ULL, period=bigM/3, firstN=128;
constexpr unsigned maxDepth=256;
struct State {u64 A,D;unsigned d,s;i128 C;};
std::array<u64,39> factors{};
std::array<u64,maxDepth> hist{};
u64 N,w,visited=0,singles=0,deep=0,unresolved=0,bad=0;
unsigned longest=0;
u64 mul(u64 a,u64 b,u64 m){return u128(a)*b%m;}
u64 powmod(u64 a,u64 e,u64 m){u64 r=1;while(e){if(e&1)r=mul(r,a,m);a=mul(a,a,m);e>>=1;}return r;}
u64 half(u64 p){return (p+(p&1)*bigM)/2;}
u64 p_at(u64 n,unsigned d){u64 e=((period-3)/2+period-n%period)%period;unsigned parity=w%4==1; if(e%2!=parity)e+=period;u64 p=mul(5,powmod(2,e,bigM),bigM);for(unsigned k=0;k<d;++k)p=half(p);return p;}
u64 rem(State s,u64 p,u64 m){i128 z=i128(mul(s.A%m,p%m,m))+s.C;z%=m;if(z<0)z+=m;return u64(z);}
State child(State s,bool down){if(down){s.A*=2;++s.d;}else{s.A+=8*s.D;s.C-=6*i128(s.D);}s.D*=3;++s.s;return s;}
void done(unsigned s,u64 count=1){assert(s<maxDepth);hist[s]+=count;if(count)longest=std::max(longest,s);}
cpp_int toBig(i128 x){bool neg=x<0;u128 a=neg?-x:x;cpp_int z=u64(a>>64);z<<=64;z+=u64(a);return neg?-z:z;}
cpp_int pow3(unsigned n){cpp_int z=1;for(unsigned i=0;i<n;++i)z*=3;return z;}
cpp_int mod(cpp_int x,const cpp_int &m){x%=m;if(x<0)x+=m;return x;}
// exact j modulo 2*3^s, including n<s (no asymptotic assumption)
cpp_int p_big(u64 n,unsigned d,const cpp_int &D){cpp_int m=3*D,phi=2*D;cpp_int r=boost::multiprecision::powm(cpp_int(3),cpp_int(n),2*phi);cpp_int e=mod(w*r-3,2*phi)/2;e=mod(e-cpp_int(n)-d,phi);return mod(5*cpp_int(boost::multiprecision::powm(cpp_int(2),e,m)),m);}
void slow(u64 n,State st){++deep;cpp_int A=st.A,D=st.D,C=toBig(st.C);unsigned d=st.d,s=st.s;while(s+1<maxDepth){cpp_int m=3*D,p=p_big(n,d,D),r=mod(A*p+C,m);assert(r%D==0);unsigned y=(r/D).convert_to<unsigned>();if(y==0){A*=2;++d;}else if(y==p%3){A+=8*D;C-=6*D;}else{done(s);return;}D=m;++s;}++unresolved;std::cout<<"UNRESOLVED "<<n<<"\n";}
void single(u64 n,State s,u64 p){++singles;while(s.s<39){u64 m=3*s.D,r=rem(s,p,m);assert(r%s.D==0);unsigned y=r/s.D;if(y==0){s=child(s,true);p=half(p);}else if(y==p%3){s=child(s,false);}else{done(s.s);return;}}slow(n,s);}
u64 count(u64 r,u64 M){u64 first=r>=firstN?r:r+((firstN-r+M-1)/M)*M;return first>N?0:(N-first)/M+1;}
void visit(State s,u64 r,u64 p){++visited;u64 M=s.D/3,c=count(r,M);if(!c)return;if(c==1){u64 n=r>=firstN?r:r+((firstN-r+M-1)/M)*M;single(n,s,n==r?p:p_at(n,s.d));return;}assert(s.s<39);u64 nextM=3*M,total=0;std::array<u64,2> rr,pp;std::array<State,2> ss;for(unsigned down=0;down<2;++down){State t=child(s,down);u64 q=down?half(p):p;unsigned matches=0;for(unsigned lift=0;lift<3;++lift){if(rem(t,q,t.D)==0){rr[down]=r+lift*M;pp[down]=q;ss[down]=t;++matches;}q=mul(q,factors[s.s],bigM);}assert(matches==1);total+=count(rr[down],nextM);}assert(rr[0]!=rr[1]&&total<=c);done(s.s,c-total);for(unsigned down=0;down<2;++down)visit(ss[down],rr[down],pp[down]);}
cpp_int predecessor(cpp_int y){if(y==5)return 1;if(y<5)return -1;unsigned j=boost::multiprecision::msb(cpp_int(y/5));for(int k=int(j);k>=0&&k>=int(j)-1;--k){cpp_int P=cpp_int(5)<<k,L=P-k-3;if(y==2*P)return L+P-2;cpp_int v=y-P-3;if(v>=0&&v%3==0&&v/3<=P-4)return L+v/3;}return -1;}
void small(){for(u64 n=0;n<=N&&n<firstN;++n){if(n<6){u64 i=((pow3(n)*w-3)/2).convert_to<u64>();cpp_int y=(cpp_int(10)<<i)-i-6;unsigned s=0;for(;;){cpp_int x=predecessor(y);if(x<0)break;assert(x<y);y=x;++s;}if(y<=3){++bad;std::cout<<"ROOT HIT "<<n<<" "<<y<<"\n";}done(s>n?s-n:0);}else slow(n,{8,3,0,1,-i128(w)-6});}}
int main(int argc,char **argv){assert(argc==3);w=std::strtoull(argv[1],nullptr,10);N=std::strtoull(argv[2],nullptr,10);assert((w==5||w==7)&&N<=1000000000000ULL);u64 M=1;for(unsigned s=1;s<39;++s){factors[s]=powmod(2,period-M,bigM);M*=3;}assert(M==period);small();if(N>=firstN)visit({8,3,0,1,-i128(w)-6},0,p_at(0,0));u64 total=0;for(unsigned i=0;i<maxDepth;++i)if(hist[i]){std::cout<<i<<" "<<hist[i]<<"\n";total+=hist[i];}std::cout<<"w="<<w<<" N="<<N<<" classified="<<total<<" nodes="<<visited<<" single="<<singles<<" deep="<<deep<<" maxAdditionalDepth="<<longest<<" unresolved="<<unresolved<<" rootHits="<<bad<<"\n";assert(total+unresolved==N+1);return bad||unresolved;}
