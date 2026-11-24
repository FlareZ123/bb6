// Untrusted larger FAR candidate search for the final depth-eight siblings.
// 128-bit bitsets permit up to 21 DFA states; Lean checks every emitted DFA.
#include <array>
#include <vector>
#include <string>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <random>
#include <climits>
#include <numeric>
using U = unsigned __int128;
using M = std::array<int,12>;
using D = std::vector<int>;
struct Rule {int dst,src,off;};
struct Result {bool safe; int rounds, depth, density; std::vector<U> rows; U z;};
int ctz(U x){uint64_t l=x;return l?__builtin_ctzll(l):64+__builtin_ctzll(uint64_t(x>>64));}
int pop(U x){return __builtin_popcountll(uint64_t(x))+__builtin_popcountll(uint64_t(x>>64));}
U compose(U mask,const U* rows){U v=0;while(mask){int j=ctz(mask);v|=rows[j];mask&=mask-1;}return v;}
Result far(const M& m,const D& dfa,bool rev){
  int d=int(dfa.size()/2), N=6*d+1, H=N-1;
  U T[254]{}; Rule rules[504]; int nr=0; U halt=U(1)<<H;
  T[H]=T[N+H]=halt;
  for(int l=0;l<d;l++)for(int q=0;q<6;q++)for(int a=0;a<2;a++){
    int x=m[2*q+a],i=a*N+6*l+q;
    if(x<0){T[i]=halt;continue;}
    int w=(x>>1)&1,n=x/4;
    if(bool(x&1)!=rev)T[i]=U(1)<<(6*dfa[2*l+w]+n);
    else for(int j=0;j<d;j++)for(int b=0;b<2;b++)if(dfa[2*j+b]==l)rules[nr++]={i,b*N+6*j+n,w*N};
  }
  for(int round=1;;round++){
    U cur=1,seen=0;int depth=0;
    while(cur){seen|=cur;if(seen&halt){int density=0;for(int k=0;k<2*N;k++)density+=pop(T[k]);return {false,round,depth,density,{},0};}cur=compose(cur,T)&~seen;depth++;}
    bool changed=false;
    for(int j=0;j<nr;j++){auto [dst,src,off]=rules[j];U x=T[dst]|compose(T[src],T+off);if(x!=T[dst]){T[dst]=x;changed=true;}}
    if(!changed){
      U z=halt;
      for(;;){U z1=z;for(int i=0;i<N;i++)if(T[i]&z)z1|=U(1)<<i;if(z==z1)break;z=z1;}
      return {true,round,depth,0,std::vector<U>(T,T+2*N),z};
    }
  }
}
M parse(const std::string& s){M m; int i=0;std::string t;for(char c:s)if(c!='_')t+=c;if(t.size()!=36)throw std::runtime_error("bad code "+s);for(;i<12;i++){const char* p=t.data()+3*i;m[i]=p[0]=='-'?-1:4*(p[2]-'A')+2*(p[0]-'0')+(p[1]=='R');}return m;}
void emit(int i,const std::string& s,const D& a,bool rev,const Result& r){std::cout<<"HIT "<<i<<" "<<s<<" "<<a.size()/2<<" "<<rev<<" DFA";for(auto x:a)std::cout<<" "<<x;std::cout<<std::endl;}
D canon(const D& a){int d=a.size()/2;D map(d,-1),order{0};map[0]=0;for(size_t i=0;i<order.size();++i)for(int b=0;b<2;b++){int y=a[2*order[i]+b];if(map[y]<0){map[y]=order.size();order.push_back(y);}}D out;for(int x:order)for(int b=0;b<2;b++)out.push_back(map[a[2*x+b]]);return out;}
D expand(D a,int d,std::mt19937_64& rng){int k=a.size()/2;while(k<d){int i=1+rng()%(2*k-1);int old=a[i];a[i]=k;a.push_back(rng()%2?old:a[2*old]);a.push_back(rng()%2?old:a[2*old+1]);k++;}return a;}
int score(const Result&r,int mode,int d){if(r.safe)return INT_MAX;switch(mode){case 0:return r.rounds*128+r.depth;case 1:return r.rounds*128+r.depth*8-r.density/(d+1);case 2:return r.rounds*256-r.density/(d+1)+r.depth;default:return r.rounds*128+r.depth*16;}}
int main(int argc,char** argv){if(argc<4)return 2;std::ifstream f(argv[1]);std::string s;std::vector<std::string> rows;while(f>>s)rows.push_back(s);int idx=atoi(argv[2]),samples=atoi(argv[3]);int maxd=argc>4?atoi(argv[4]):21;int seed=argc>5?atoi(argv[5]):0;if(idx<1||idx>int(rows.size())||samples<0||maxd<5||maxd>21)return 2;std::mt19937_64 rng(0x94a6db*uint64_t(idx+1)+seed);M m=parse(rows.at(idx-1));
std::vector<D> seeds;for(std::string c:{"0123224101","0123224022","0123224120","0123224020","0123224212","0123224223","0123440144","045455215355","054044214443","051141211013","021114153411","054441234443","043155525155","05631433656263","05161633123435","04222215632066","06505252315264","0723266726416665","0544241724236364","065887701387542885"}){D a;for(char v:c)a.push_back(v-'0');seeds.push_back(a);}
for(int rev=0;rev<2;rev++){D bestGlobal=seeds[0];int globalScore=-1;for(int d=5;d<=maxd;d++){D best=expand(canon(bestGlobal),d,rng);if((int)best.size()!=2*d)best=expand(canon(seeds[0]),d,rng);int bestScore=-1;for(auto a:seeds){a=canon(a);if(int(a.size())<=2*d){a=expand(a,d,rng);auto r=far(m,a,rev);if(r.safe){emit(idx,rows[idx-1],canon(a),rev,r);return 0;}int sc=score(r,0,d);if(sc>bestScore){bestScore=sc;best=a;}}}D cur=best;int curScore=bestScore;
for(int j=0;j<samples;j++){int mode=(j/10000)%4;if(j%1000==0){if(j%4000==0){cur=expand(canon(best),d,rng);if(j%8000==0){for(int k=1;k<2*d;k++)cur[k]=rng()%d;}}else{cur=best;for(int k=0;k<1+int(rng()%5);k++)cur[1+rng()%(2*d-1)]=rng()%d;}curScore=score(far(m,cur,rev),mode,d);}
D a=cur;int changes=j%17==0?2+int(rng()%3):1;for(int k=0;k<changes;k++)a[1+rng()%(2*d-1)]=rng()%d;auto r=far(m,a,rev);if(r.safe){emit(idx,rows[idx-1],canon(a),rev,r);return 0;}int sc=score(r,mode,d),bs=score(r,0,d);if(bs>bestScore){bestScore=bs;best=a;}if(sc>=curScore||rng()%1000<5){curScore=sc;cur=std::move(a);}}
if(bestScore>globalScore){globalScore=bestScore;bestGlobal=best;}std::cerr<<"target="<<idx<<" rev="<<rev<<" d="<<d<<" score="<<bestScore<<" global="<<globalScore<<"\n";
}}
return 0;}
