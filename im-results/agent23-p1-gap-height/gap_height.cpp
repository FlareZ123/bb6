#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <limits>
#include <vector>
using u64=uint64_t; using u128=__uint128_t;
const unsigned LIMIT=256;
u64 X; unsigned cap;
u64 best[LIMIT+1]; std::vector<unsigned> witness[LIMIT+1], path;
u64 symbolic_nodes=0, concrete_nodes=0, leaves=0;
unsigned maxG=0;
static inline u64 invodd(u64 a) { u64 z=a; for(int i=0;i<5;++i)z*=2-a*z;return z; }
void record(unsigned G,u64 C0) {
    maxG=std::max(maxG,G);
    if(G<=LIMIT && C0<best[G]) {best[G]=C0;witness[G]=path;}
}
void concrete(u64 C0,unsigned G,u64 b) {
    ++concrete_nodes;
    assert(C0>=17 && C0<=X && (C0+G+b)%8==0);
    record(G,C0);
    if(G>=cap){++leaves;return;}
    u64 C=C0+G, a=C+b;
    unsigned gmax=__builtin_ctzll(a);
    for(unsigned g=3;g<=gmax;++g){
        u64 next=a>>g;
        if((C+g+next)%8)continue;
        path.push_back(g); concrete(C0,G+g,next);path.pop_back();
    }
}
// r+2^(G+3)h, b(h)=b+8Sh. At G=0, b=-1, S=0.
void symbolic(unsigned G,u64 r,int64_t b,u64 S){
    ++symbolic_nodes;
    assert(G<61 && r < (1ull<<(G+3)));
    const u64 mod=1ull<<(G+3);
    u64 lo = r>=17?r:r+((17-r+mod-1)/mod)*mod;
    if(lo>X)return;
    record(G,lo);
    if(G>=cap){++leaves;return;}
    if(mod>X-r){concrete(r,G,b);return;}
    const u64 maxh=(X-r)/mod;
    const u64 C=r+G;
    assert((int64_t(C)+b)%8==0);
    const u64 A=(int64_t(C)+b)/8;
    const u64 inv=invodd((1ull<<G)+S);
    // for C0<=X, C+b <= 8/7*(X+cap) after the first edge;
    // b=-1 at the root. Conservative 2*(X+cap+64) bound.
    const unsigned gmax=63-__builtin_clzll(2*(X+cap+64));
    for(unsigned g=3;g<=gmax;++g){
        u64 mask=(1ull<<g)-1;
        u64 h0=(-(A+((C+g)%8<<(g-3)))*inv)&mask;
        if(h0>maxh)continue;
        const u64 rr=r+mod*h0;
        const u64 SS=S+(1ull<<G);
        const u64 newb=(u64(int64_t(C)+b)+8*SS*h0)>>g;
        const unsigned GG=G+g;
        assert((rr+GG+newb)%8==0);
        path.push_back(g);
        if(GG+3>=61 || (1ull<<(GG+3))>X-rr){
            if(rr>=17)concrete(rr,GG,newb);
        }else symbolic(GG,rr,newb,SS);
        path.pop_back();
    }
}
int main(int argc,char**argv){
    X=argc>1?std::stoull(argv[1]):(1ull<<30);
    cap=argc>2?std::stoul(argv[2]):100;
    assert(X>=17 && X<(1ull<<58) && cap<=LIMIT-60);
    std::fill(best,best+LIMIT+1,std::numeric_limits<u64>::max());
    symbolic(0,1,-1,0);
    std::cout<<"X="<<X<<" cap="<<cap<<" symbolic="<<symbolic_nodes<<" concrete="<<concrete_nodes<<" capHits="<<leaves<<" maxG="<<maxG<<"\n";
    for(unsigned G=1;G<=maxG;++G)if(best[G]!=std::numeric_limits<u64>::max()){
        std::cout<<G<<" "<<best[G]<<" :"; for(auto g:witness[G])std::cout<<" "<<g;std::cout<<"\n";
    }
}
