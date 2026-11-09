#include <algorithm>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
#include <limits>
using namespace std;

struct Rule { int bit,dir,st; };
static const Rule T[6][2] = {
    {{1,1,1},{0,1,4}}, {{1,-1,2},{0,1,0}},
    {{1,-1,0},{1,-1,3}}, {{1,-1,2},{1,-1,5}},
    {{0,-1,2},{0,-1,1}}, {{1,-1,4},{0,0,6}}
};
struct Result { int typ,steps,lo,hi; };
constexpr int CAP = 1 << 18, OFFSET = CAP / 2;
static vector<uint32_t> tags(CAP,0);
static vector<uint8_t> tape(CAP,0);
static uint32_t epoch=0;
inline uint8_t readBit(int i){ return tags[i]==epoch ? tape[i] : 0; }
inline void writeBit(int i,uint8_t b){ tags[i]=epoch; tape[i]=b; }

Result simulate(int n,uint32_t word,int stepMax) {
    ++epoch;
    if (!epoch) {fill(tags.begin(),tags.end(),0);++epoch;}
    int p=OFFSET,state=5,onesLeft=0,lo=p,hi=p;
    for (int i=1;i<=4;i++) writeBit(p+i,1);
    for (int i=0;i<n;i++)
        if ((word>>i)&1u) writeBit(p+6+i,1);
    hi=p+6+n;
    for (int steps=0;steps<stepMax;steps++) {
        int bit=readBit(p);
        if (steps && state==5) {
            if (bit) return {2,steps,lo,hi};
            if (!onesLeft) return {1,steps,lo,hi};
        }
        Rule r=T[state][bit];
        if (r.st>=6) return {2,steps,lo,hi};
        writeBit(p,r.bit);
        if (r.dir==1) {onesLeft+=r.bit;p++;}
        else {p--;onesLeft-=readBit(p);}
        state=r.st;
        lo=min(lo,p);hi=max(hi,p);
        if (p<2||p>=CAP-2) return {4,steps,lo,hi};
    }
    return {3,stepMax,lo,hi};
}

int main(int argc,char**argv) {
    int N=argc>1?stoi(argv[1]):22,limit=argc>2?stoi(argv[2]):200000;
    for (int n=0;n<=N;n++) {
        uint64_t cases=n==0?1ull:(1ull<<(n-1));
        uint64_t cnt[5]={0};
        int maxt=0,maxw=0,maxType=0,maxwidth=0,maxExtraRight=-1000000,maxExtraLeft=-1000000;
        for (uint64_t j=0;j<cases;j++) {
            uint32_t word=n==0?0u:(uint32_t(j)|(1u<<(n-1)));
            Result r=simulate(n,word,limit);
            cnt[r.typ]++;
            maxExtraRight=max(maxExtraRight,r.hi-(OFFSET+6+n));
            maxExtraLeft=max(maxExtraLeft,OFFSET-r.lo);
            if (r.steps>maxt) {
                maxt=r.steps;maxw=word;maxType=r.typ;maxwidth=r.hi-r.lo;
            }
        }
        cerr<<"n="<<n<<" cases="<<cases<<" return="<<cnt[1]
            <<" halt="<<cnt[2]<<" capped="<<cnt[3]<<" OOB="<<cnt[4]
            <<" maxSteps="<<maxt<<" maxWord="<<maxw<<" type="<<maxType
            <<" span="<<maxwidth<<" extraRight="<<maxExtraRight
            <<" leftReach="<<maxExtraLeft<<"\n";
    }
}
