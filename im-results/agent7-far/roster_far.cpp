// Untrusted one-sided FAR candidate generation, independently checked in Lean.
#include <array>
#include <vector>
#include <string>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <random>
using U = uint64_t;
using M = std::array<int,12>;
using D = std::vector<int>;
struct Rule {int dst,src,off;};
struct Result {bool safe; int rounds; std::vector<U> rows; U z;};
U compose(U mask,const U* rows){U v=0;while(mask){int j=__builtin_ctzll(mask);v|=rows[j];mask&=mask-1;}return v;}
Result far(const M& m,const D& dfa,bool rev){
  int d=int(dfa.size()/2), N=6*d+1, H=N-1;
  U T[122]{}; Rule rules[240]; int nr=0; U halt=U(1)<<H;
  T[H]=T[N+H]=halt;
  for(int l=0;l<d;l++)for(int q=0;q<6;q++)for(int a=0;a<2;a++){
    int x=m[2*q+a],i=a*N+6*l+q;
    if(x<0){T[i]=halt;continue;}
    int w=(x>>1)&1,n=x/4;
    if(bool(x&1)!=rev)T[i]=U(1)<<(6*dfa[2*l+w]+n);
    else for(int j=0;j<d;j++)for(int b=0;b<2;b++)if(dfa[2*j+b]==l)rules[nr++]={i,b*N+6*j+n,w*N};
  }
  for(int round=1;;round++){
    U cur=1,seen=0;
    while(cur){seen|=cur;if(seen&halt)return {false,round,{},0};cur=compose(cur,T)&~seen;}
    bool changed=false;
    for(int j=0;j<nr;j++){auto [dst,src,off]=rules[j];U x=T[dst]|compose(T[src],T+off);if(x!=T[dst]){T[dst]=x;changed=true;}}
    if(!changed){
      U z=halt;
      for(;;){U z1=z;for(int i=0;i<N;i++)if(T[i]&z)z1|=U(1)<<i;if(z==z1)break;z=z1;}
      return {true,round,std::vector<U>(T,T+2*N),z};
    }
  }
}
void enumerate(int d,D& a,int mx,std::vector<D>& out){
  if(int(a.size())==2*d){if(mx==d-1)out.push_back(a);return;}
  if(int(a.size()/2)>mx)return;
  for(int j=0;j<=std::min(d-1,mx+1);j++){a.push_back(j);enumerate(d,a,std::max(j,mx),out);a.pop_back();}
}
M parse(const std::string& s){M m; int i=0;std::string t;for(char c:s)if(c!='_')t+=c;if(t.size()!=36)throw std::runtime_error("bad code "+s);for(;i<12;i++){const char* p=t.data()+3*i;m[i]=p[0]=='-'?-1:4*(p[2]-'A')+2*(p[0]-'0')+(p[1]=='R');}return m;}
void emit(int i,const std::string& s,const D& a,bool rev,const Result& r){std::cout<<"HIT "<<i<<" "<<s<<" "<<a.size()/2<<" "<<rev<<" DFA";for(auto x:a)std::cout<<" "<<x;std::cout<<" MASK";for(auto x:r.rows)std::cout<<" "<<x;std::cout<<" Z "<<r.z<<std::endl;}
int main(int argc,char** argv){if(argc<2||argc>6)return 2;int start=argc>2?std::atoi(argv[2]):0;int stride=argc>3?std::atoi(argv[3]):1;int samples=argc>4?std::atoi(argv[4]):30000;int maxd=argc>5?std::atoi(argv[5]):10;if(start<0||stride<=0||maxd<5||maxd>10)return 2;std::ifstream f(argv[1]);std::string s;std::vector<std::string> rows;while(f>>s)rows.push_back(s);if(rows.empty())return 2;std::vector<D> dfas;D a{0};enumerate(5,a,0,dfas);std::mt19937_64 rng(0xB66F123+start);int tested=0,hits=0;for(int i=start;i<int(rows.size());i+=stride){M m=parse(rows[i]);bool got=false;int best[2]={0,0};D bestD[2];for(int rev=0;rev<2&&!got;rev++)for(const auto& d:dfas){auto r=far(m,d,rev);if(r.safe){emit(i+1,rows[i],d,rev,r);got=true;break;}if(r.rounds>best[rev]){best[rev]=r.rounds;bestD[rev]=d;}}if(!got)for(int rev=0;rev<2&&!got;rev++){
      for(int d=6;d<=maxd&&!got;d++){
        D current=bestD[rev];while(int(current.size())<2*d){current.push_back(rng()%d);current.push_back(rng()%d);}int score=far(m,current,rev).rounds;
        for(int j=0;j<samples;j++){
          D x=current;if(j%1000==0){for(int k=1;k<2*d;k++)x[k]=rng()%d;}else{x[1+rng()%(2*d-1)]=rng()%d;if(j%11==0)x[1+rng()%(2*d-1)]=rng()%d;}
          auto r=far(m,x,rev);if(r.safe){emit(i+1,rows[i],x,rev,r);got=true;break;}
          if(r.rounds>=score||rng()%1000<5){score=r.rounds;current=std::move(x);}
        }
        if(!got){bestD[rev]=current;best[rev]=score;}
      }
    }tested++;hits+=got;if(tested%10==0)std::cerr<<"tested="<<tested<<" hits="<<hits<<" last="<<i+1<<" score="<<best[0]<<","<<best[1]<<"\n";}std::cerr<<"completed="<<tested<<" hits="<<hits<<"\n";}
