// Candidate filter only. The emitted FAR masks must pass Lean zipCheck.
#include <array>
#include <vector>
#include <string>
#include <iostream>
#include <fstream>
#include <cassert>
#include <cstdint>
using U=unsigned __int128; using M=std::array<int,12>; using D=std::vector<int>;
int ctz(U x){uint64_t l=x;return l?__builtin_ctzll(l):64+__builtin_ctzll(uint64_t(x>>64));}
U compose(U mask,const U* rows){U v=0;while(mask){int j=ctz(mask);v|=rows[j];mask&=mask-1;}return v;}
struct Rule{int dst,src,off;};
bool good(const M&m,const D&dfa,bool rev){int d=dfa.size()/2,N=6*d+1,H=N-1;assert(N<=127);U T[254]{};Rule rules[2048];int nr=0;U halt=U(1)<<H;T[H]=T[N+H]=halt;for(int l=0;l<d;l++)for(int q=0;q<6;q++)for(int a=0;a<2;a++){int x=m[2*q+a],i=a*N+6*l+q;if(x<0){T[i]=halt;continue;}int w=(x>>1)&1,n=x/4;if(bool(x&1)!=rev)T[i]=U(1)<<(6*dfa[2*l+w]+n);else for(int j=0;j<d;j++)for(int b=0;b<2;b++)if(dfa[2*j+b]==l){assert(nr<2048);rules[nr++]={i,b*N+6*j+n,w*N};}}for(;;){U cur=1,seen=0;while(cur){seen|=cur;if(seen&halt)return false;cur=compose(cur,T)&~seen;}bool changed=false;for(int j=0;j<nr;j++){auto[dst,src,off]=rules[j];U v=compose(T[src],T+off)&~T[dst];if(v){T[dst]|=v;changed=true;}}if(!changed)return true;}}
M parse(std::string s){M m;std::string t;for(char c:s)if(c!='_')t+=c;assert(t.size()==36);for(int i=0;i<12;i++){auto p=t.data()+3*i;m[i]=p[0]=='-'?-1:4*(p[2]-'A')+2*(p[0]-'0')+(p[1]=='R');}return m;}
D parseD(std::string x){D d;for(size_t i=1;i<x.size();i++){char c=x[i];d.push_back(c<='9'?c-'0':c-'a'+10);}return d;}
int main(int argc,char**argv){assert(argc==2);std::ifstream bf(argv[1]);std::string x;std::vector<std::pair<std::string,D>> bank;while(bf>>x)bank.push_back({x,parseD(x)});std::string s;int n=0;while(std::cin>>s){M m=parse(s);bool ok=false;for(auto &[a,d]:bank){if(good(m,d,a[0]=='1')){std::cout<<n<<' '<<a<<'\n';ok=true;break;}}if(!ok)std::cout<<n<<" -\n";n++;}}
