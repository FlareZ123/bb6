#include <array>
#include <vector>
#include <string>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <cstdint>
#include <stdexcept>
using U=unsigned __int128;
using M=std::array<int,12>;
using D=std::vector<int>;
struct Rule {int dst,src,off;};
U compose(U mask,const U* rows){U v=0;while(mask){uint64_t lo=(uint64_t)mask;int j=lo?__builtin_ctzll(lo):64+__builtin_ctzll((uint64_t)(mask>>64));v|=rows[j];mask&=mask-1;}return v;}
bool far(const M& m,const D& dfa,bool rev){
 int d=int(dfa.size()/2),N=6*d+1,H=N-1;
 U T[254]{};Rule rules[504];int nr=0;U halt=U(1)<<H;T[H]=T[N+H]=halt;
 for(int l=0;l<d;l++)for(int q=0;q<6;q++)for(int a=0;a<2;a++){
  int x=m[2*q+a],i=a*N+6*l+q;
  if(x<0){T[i]=halt;continue;}
  int w=(x>>1)&1,n=x/4;
  if(bool(x&1)!=rev)T[i]=U(1)<<(6*dfa[2*l+w]+n);
  else for(int j=0;j<d;j++)for(int b=0;b<2;b++)if(dfa[2*j+b]==l)rules[nr++]={i,b*N+6*j+n,w*N};
 }
 for(;;){
  U cur=1,seen=0;
  while(cur){seen|=cur;if(seen&halt)return false;cur=compose(cur,T)&~seen;}
  bool changed=false;
  for(int j=0;j<nr;j++){auto [dst,src,off]=rules[j];U x=T[dst]|compose(T[src],T+off);if(x!=T[dst]){T[dst]=x;changed=true;}}
  if(!changed)return true;
 }
}
M parse(std::string s){s.erase(std::remove(s.begin(),s.end(),'_'),s.end());if(s.size()!=36)throw std::runtime_error("bad code");M m;for(int i=0;i<12;i++){const char* p=s.data()+3*i;m[i]=p[0]=='-'?-1:4*(p[2]-'A')+2*(p[0]-'0')+(p[1]=='R');}return m;}
struct Entry {D d;bool rev;int count;std::string code;};
int main(int argc,char**argv){
 if(argc!=3)return 2;std::ifstream bf(argv[1]),mf(argv[2]);if(!bf||!mf)return 2;
 std::vector<Entry> bank;std::string s;
 while(bf>>s){D a;for(size_t i=1;i<s.size();i++){char c=s[i];a.push_back(c>='a'?c-'a'+10:c-'0');}if(a.empty()||a.size()%2||a.size()>42||a[0]!=0||*std::min_element(a.begin(),a.end())<0||*std::max_element(a.begin(),a.end())>=int(a.size()/2))throw std::runtime_error("bad DFA");bank.push_back({a,s[0]=='1',0,s});}
 int i=0,hits=0;
 while(mf>>s){auto m=parse(s);for(auto& e:bank){if(far(m,e.d,e.rev)){std::cout<<i<<":"<<e.code<<"\n";e.count++;hits++;break;}}i++;if(i%100==0)std::stable_sort(bank.begin(),bank.end(),[](auto&a,auto&b){return a.count>b.count;});}
 std::cerr<<"completed "<<i<<" hits "<<hits<<"\n";
}
