#include <boost/multiprecision/cpp_int.hpp>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <algorithm>
#include <cstdlib>
using boost::multiprecision::cpp_int;
using u64=std::uint64_t;
using u128=__uint128_t;
using i128=__int128_t;
constexpr unsigned fastDepth=39;
constexpr u64 fastMod=4052555153018976267ULL; // 3^39
constexpr u64 lowerBound=512;
struct State {u64 A,D; unsigned d,t; i128 C;};
std::array<std::array<u64,3>,fastDepth> factors{};
std::array<u64,256> histogram{};
u64 N=1000000000ULL, nodes=0, candidates=0, deep=0, unresolved=0, bad=0;
unsigned maxDepth=0;
inline u64 mulmod(u64 a,u64 b,u64 m){return u128(a)*b%m;}
u64 powmod(u64 a,u64 b,u64 m){u64 r=1;while(b){if(b&1)r=mulmod(r,a,m);a=mulmod(a,a,m);b>>=1;}return r;}
inline u64 halfmod(u64 p){return (p+(p&1)*fastMod)/2;}
inline i128 B(u64 D){return (3*i128(D)-1)/2;}
inline u64 rem(const State &s,u64 p,u64 i,u64 m){
    i128 z=i128(mulmod(s.A%m,p%m,m))-B(s.D)*i-s.C;
    z%=m;if(z<0)z+=m;return u64(z);
}
inline State child(const State &s,unsigned low){
    u64 D=3*s.D;unsigned d=s.d+low;
    return {(s.A<<low)+2*s.D,D,d,s.t+1,s.C+i128(D)*(4-i128(d))};
}
void done(unsigned t){assert(t<histogram.size());histogram[t]++;maxDepth=std::max(maxDepth,t);}
cpp_int toBig(i128 x){bool neg=x<0;u128 a=neg?-x:x;cpp_int z=u64(a>>64);z<<=64;z+=u64(a);return neg?-z:z;}
void slow_single(u64 i,State s){
    ++deep;cpp_int A=s.A,D=s.D,C=toBig(s.C);unsigned d=s.d,t=s.t;
    while(i>=4ULL*(t+1)+10 && t+1<histogram.size()){
        cpp_int m=3*D,b=(3*D-1)/2;
        cpp_int p=boost::multiprecision::powm(cpp_int(2),cpp_int(i-d),m);
        cpp_int n=(A*5*p-b*i-C)%m;if(n<0)n+=m;
        assert(n%D==0);unsigned y=(n/D).convert_to<unsigned>();
        if(y==0){done(t);return;}
        unsigned low=(y!=((i-d)%2==0?2U:1U));
        d+=low;A=(A<<low)+2*D;D=m;C+=D*(4-cpp_int(d));++t;
    }
    ++unresolved;std::cout<<"UNRESOLVED "<<i<<" depth "<<t<<"\n";
}
void single(u64 i,State s,u64 p){
    ++candidates;
    while(s.t<fastDepth && i>=4ULL*(s.t+1)+10){
        u64 m=3*s.D,n=rem(s,p,i,m);assert(n%s.D==0);
        unsigned y=n/s.D;if(y==0){done(s.t);return;}
        unsigned low=(y!=((i-s.d)%2==0?2U:1U));
        if(low)p=halfmod(p);
        s=child(s,low);
    }
    slow_single(i,s);
}
void visit(State s,u64 r,u64 p){
    ++nodes;
    u64 M=2*s.D;
    u64 first=r>=lowerBound?r:r+((lowerBound-r+M-1)/M)*M;
    if(first>N)return;
    if(N-first<M){
        if(first!=r)p=mulmod(5,powmod(2,first-s.d,fastMod),fastMod);
        single(first,s,p);return;
    }
    assert(s.t<fastDepth && lowerBound>=4ULL*(s.t+1)+10);
    // All other lifts die at this depth: exact counts across the interval.
    u64 parentCount=(N-first)/M+1,childCount=0;
    std::array<State,2> ss;std::array<u64,2> rr,pp;
    for(unsigned low=0;low<2;++low){
        State h=child(s,low);u64 p0=low?halfmod(p):p;
        u64 n=rem(h,p0,r,h.D);assert(n%s.D==0);
        unsigned lift=(3-n/s.D)%3;
        u64 q=r+lift*M, q0=q>=lowerBound?q:q+((lowerBound-q+3*M-1)/(3*M))*(3*M);
        if(q0<=N)childCount+=(N-q0)/(3*M)+1;
        ss[low]=h;rr[low]=q;pp[low]=mulmod(p0,factors[s.t][lift],fastMod);
    }
    assert(rr[0]!=rr[1]&&childCount<=parentCount);
    histogram[s.t]+=parentCount-childCount;
    if(parentCount>childCount)maxDepth=std::max(maxDepth,s.t);
    for(unsigned low=0;low<2;++low)visit(ss[low],rr[low],pp[low]);
}
cpp_int predecessor(cpp_int y){
    if(y==5)return 1;
    if(y<5)return -1;
    cpp_int z=y/5;unsigned j=boost::multiprecision::msb(z);
    for(int k=int(j);k>=0&&k>=int(j)-1;--k){
        cpp_int P=cpp_int(5)<<k,L=P-k-3;
        if(y==2*P)return L+P-2;
        cpp_int v=y-P-3;
        if(v>=0&&v%3==0&&v/3<=P-4)return L+v/3;
    }
    return -1;
}
void small(){
    for(u64 i=0;i<lowerBound&&i<=N;++i){
        cpp_int y=(cpp_int(10)<<i)-i-6;unsigned t=0;
        for(;;){cpp_int x=predecessor(y);if(x<0)break;assert(x<y);y=x;++t;}
        if(y<=3){++bad;std::cout<<"ROOT HIT "<<i<<" root "<<y<<"\n";}
        done(t);
    }
}
int main(int argc,char** argv){
    if(argc>1)N=std::strtoull(argv[1],nullptr,10);
    assert(N<=1000000000000ULL);
    u64 D=1;
    for(unsigned t=0;t<fastDepth;++t){u64 a=powmod(2,2*D,fastMod);factors[t]={1,a,mulmod(a,a,fastMod)};D*=3;}
    assert(D==fastMod);
    small();if(N>=lowerBound){visit({2,1,0,0,6},0,5);visit({2,1,0,0,6},1,10);}
    u64 count=0;for(unsigned t=0;t<histogram.size();++t)if(histogram[t]){count+=histogram[t];std::cout<<t<<" "<<histogram[t]<<"\n";}
    std::cout<<"N="<<N<<" classified="<<count<<" nodes="<<nodes<<" single="<<candidates<<" deep="<<deep<<" maxDepth="<<maxDepth<<" unresolved="<<unresolved<<" rootHits="<<bad<<"\n";
    assert(count+unresolved==N+1);return unresolved||bad;
}
