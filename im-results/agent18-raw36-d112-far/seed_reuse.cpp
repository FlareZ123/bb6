#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <vector>

using U = __uint128_t;
using Table = std::array<int,12>;
struct Rule { int dst,src,off; };
struct DFA { int d,rev; std::vector<int> D; };

int bitindex(U v) {
  uint64_t lo=uint64_t(v);
  return lo ? __builtin_ctzll(lo) : 64+__builtin_ctzll(uint64_t(v>>64));
}
Table parse(std::string s) {
  s.erase(std::remove(s.begin(),s.end(),'_'),s.end());
  Table p{};
  for(int i=0;i<12;i++) {
    auto a=s.substr(3*i,3);
    p[i]=a=="---" ? -1 : (a[0]-'0')*12+(a[1]=='R'?6:0)+(a[2]-'A');
  }
  return p;
}
DFA decode(std::string s) {
  DFA a{int(s.size()-1)/2,s[0]-'0',{}};
  for(size_t i=1;i<s.size();i++) a.D.push_back(s[i]<='9'?s[i]-'0':s[i]-'a'+10);
  return a;
}
std::string encode(const DFA&a) {
  std::string s(1,char('0'+a.rev));
  for(int x:a.D) s+=x<10?char('0'+x):char('a'+x-10);
  return s;
}
bool valid(const DFA&a) {
  return a.d>0 && a.d<=20 && a.D.size()==2*a.d && a.D[0]==0 &&
    std::all_of(a.D.begin(),a.D.end(),[&](int x){return x>=0&&x<a.d;});
}
bool far(const Table&p,const DFA&a) {
  int N=6*a.d+1,H=N-1;
  U T[242]={},halt=U(1)<<H;
  T[H]=T[N+H]=halt;
  Rule rules[480]; int nr=0;
  for(int l=0;l<a.d;l++) for(int q=0;q<6;q++) for(int b=0;b<2;b++) {
    int mv=p[2*q+b],dst=b*N+6*l+q;
    if(mv<0){T[dst]=halt;continue;}
    int w=mv>=12,r=(mv%12>=6),nxt=mv%6;
    if(r!=a.rev) T[dst]=U(1)<<(6*a.D[2*l+w]+nxt);
    else for(int j=0;j<a.d;j++) for(int c=0;c<2;c++)
      if(a.D[2*j+c]==l) rules[nr++]={dst,c*N+6*j+nxt,w*N};
  }
  for(;;) {
    U z=halt,zz;
    do {
      zz=z;
      for(int j=0;j<N;j++) if(T[j]&z) z|=U(1)<<j;
      if(z&1) return false;
    } while(zz!=z);
    bool changed=false;
    for(int i=0;i<nr;i++) {
      const auto&r=rules[i]; U v=T[r.dst],b=T[r.src];
      while(b){int k=bitindex(b);v|=T[r.off+k];b&=b-1;}
      if(v!=T[r.dst]){T[r.dst]=v;changed=true;}
    }
    if(!changed) return true;
  }
}

int main(int argc,char**argv) {
  if(argc!=3){std::cerr<<"usage: seed_reuse tables.txt seeds.txt\n";return 2;}
  std::ifstream f(argv[1]); std::string s;
  std::vector<Table> tables; std::vector<std::string> names;
  while(f>>s){names.push_back(s);tables.push_back(parse(s));}
  std::ifstream g(argv[2]); std::set<std::string> seeds;
  while(g>>s) seeds.insert(s);
  std::vector<bool> done(tables.size());
  int left=tables.size();
  uint64_t tried=0;
  for(const auto&code:seeds) {
    auto a=decode(code);
    if(!valid(a)) continue;
    ++tried;
    for(size_t i=0;i<tables.size();i++) if(!done[i]&&far(tables[i],a)) {
      done[i]=true; --left;
      std::cout<<names[i]<<"\t"<<encode(a)<<"\n";
    }
  }
  std::cerr<<"seed-only FAR reuse: "<<(tables.size()-left)<<" / "<<tables.size()
           <<" closed by "<<tried<<" valid seed automata\n";
}
