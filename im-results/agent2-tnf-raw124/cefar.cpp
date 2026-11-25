#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
#include <unordered_set>
#include <functional>
#include <chrono>
using U=uint64_t;
struct Rule {int dst,src,off;};
struct CE {std::vector<std::pair<std::string,std::string>> eq; uint64_t hits=0;};
struct Machine {int id;std::string table;bool solved=false;std::array<std::vector<CE>,2> ce;uint64_t checked=0,filtered=0;};
std::vector<Machine> ms;int D[20],n;uint64_t count=0;
int runword(const std::string&w){int q=0;for(char c:w)q=D[2*q+c-'0'];return q;}
bool rejects(const CE&c){for(auto &[a,b]:c.eq)if(runword(a)!=runword(b))return false;return true;}
void trim(std::string &s){auto i=s.find_first_not_of('0');if(i==std::string::npos)s.clear();else if(i)s.erase(0,i);}
struct Deriv{int src=-1,mid=-1,off=-1;};
// Every emitted success passes full FAR closure. Failed closures may yield reusable
// abstract halting derivations, expressed as DFA equivalences between finite words.
bool check(const std::string &p,int rev,CE *witness=nullptr){
 const int N=6*n+1,H=N-1; U T[122]={},halt=U(1)<<H;T[H]=T[N+H]=halt;
 Rule rules[1200];int nr=0;std::vector<Deriv> proofs;if(witness)proofs.resize(2*N*N);
 for(int l=0;l<n;l++)for(int q=0;q<6;q++)for(int a=0;a<2;a++){
  int s=3*(2*q+a),dst=a*N+6*l+q;
  if(p[s]=='-'){T[dst]=halt;continue;}
  int w=p[s]-'0',r=p[s+1]=='R',nxt=p[s+2]-'A';
  if(r!=rev)T[dst]=U(1)<<(6*D[2*l+w]+nxt);
  else for(int j=0;j<n;j++)for(int b=0;b<2;b++)if(D[2*j+b]==l)rules[nr++]={dst,b*N+6*j+nxt,w*N};
 }
 while(true){
  U z=halt;int znext[61];
  while(true){
   U old=z;
   for(int j=0;j<H;j++)if(!(z&(U(1)<<j))&&(T[j]&z)){
    if(witness)znext[j]=std::countr_zero(T[j]&z);z|=U(1)<<j;
   }
   if(z&1){
    if(!witness)return false;
    std::array<std::string,10> rep;std::array<bool,10> seen{};seen[0]=true;
    int queue[10]={0},tail=1;
    for(int i=0;i<tail;i++)for(int b=0;b<2;b++){
     int j=D[2*queue[i]+b];if(!seen[j]){seen[j]=true;rep[j]=rep[queue[i]]+char('0'+b);queue[tail++]=j;}
    }
    std::string left;int steps=0;bool failed=false,halted=false;
    auto addEq=[&](std::string a,std::string b){trim(a);trim(b);if(a==b)return;if(a>b)std::swap(a,b);if(a.size()>512||b.size()>512){failed=true;return;}witness->eq.push_back({std::move(a),std::move(b)});};
    std::function<void(int,int,int)> expand=[&](int row,int end,int depth){
     if(failed||halted||row%N==H)return;
     if(++steps>10000||depth>1000){failed=true;return;}
     int a=row/N,q=(row%N)%6,l=(row%N)/6,s=3*(2*q+a);
     if(runword(left)!=l){failed=true;return;}
     if(p[s]=='-'){halted=true;return;}
     auto d=proofs[row*N+end];int w=p[s]-'0';
     if(d.src<0){
      if((p[s+1]=='R')==rev){failed=true;return;}
      left+=char('0'+w);trim(left);return;
     }
     int b=d.src/N,j=(d.src%N)/6;
     if((p[s+1]=='R')!=rev||!seen[j]){failed=true;return;}
     std::string pop=left;int actual=0;if(!pop.empty()){actual=pop.back()-'0';pop.pop_back();}
     if(actual==b&&runword(pop)==j)left=std::move(pop);
     else{std::string alt=rep[j]+char('0'+b);addEq(left,alt);left=rep[j];}
     expand(d.src,d.mid,depth+1);expand(d.off+d.mid,end,depth+1);
    };
    for(int j=0;j!=H&&!failed&&!halted;){int k=znext[j];expand(j,k,0);j=k;}
    if(failed||!halted)witness->eq.clear();
    else{std::sort(witness->eq.begin(),witness->eq.end());witness->eq.erase(std::unique(witness->eq.begin(),witness->eq.end()),witness->eq.end());if(witness->eq.size()>40)witness->eq.clear();}
    return false;
   }
   if(old==z)break;
  }
  bool changed=false;
  for(int i=0;i<nr;i++){
   auto [dst,src,off]=rules[i];U v=T[dst],bits=T[src];
   while(bits){int mid=std::countr_zero(bits);U extra=T[off+mid]&~v;if(witness){for(U b=extra;b;b&=b-1)proofs[dst*N+std::countr_zero(b)]={src,mid,off};}v|=extra;bits&=bits-1;}
   if(v!=T[dst]){T[dst]=v;changed=true;}
  }
  if(!changed)return true;
 }
}
void visit(){++count;for(auto&m:ms)if(!m.solved){for(int r=0;r<2;r++){
 auto&cs=m.ce[r];bool filt=false;
 for(auto&c:cs)if(rejects(c)){++c.hits;filt=true;++m.filtered;break;}
 if(filt)continue;
 ++m.checked;
 if(check(m.table,r)){m.solved=true;std::cout<<m.id<<' '<<r;for(int i=0;i<2*n;i++)std::cout<<D[i];std::cout<<'\n'<<std::flush;break;}
 CE c;check(m.table,r,&c);if(!c.eq.empty()){
  if(!rejects(c))abort();
  if(cs.size()<128)cs.push_back(std::move(c));
  else{auto it=std::min_element(cs.begin(),cs.end(),[](auto&a,auto&b){return a.hits<b.hits;});*it=std::move(c);}
 }
 if((m.checked&511)==0)std::stable_sort(cs.begin(),cs.end(),[](auto&a,auto&b){return a.hits>b.hits;});
}}}
void dfs(int i,int max){if(i==2*n){if(max==n-1)visit();return;}if(i/2>max)return;for(int v=0;v<=std::min(max+1,n-1);v++){D[i]=v;dfs(i+1,std::max(max,v));}}
int partial_word(const std::string&w,int i){int q=0;for(char c:w){int a=2*q+c-'0';if(a>=i)return -1;q=D[a];}return q;}
bool partial_rejects(const CE&c,int i){for(auto &[a,b]:c.eq){int x=partial_word(a,i);if(x<0)return false;int y=partial_word(b,i);if(y<0||x!=y)return false;}return true;}
uint64_t pruned=0,nodes=0;
void dfs_single(int i,int max,int mask){
 if(ms[0].solved||!mask)return;
 ++nodes;
 if(i>=3&&(i%2==0||i==2*n)){
  for(int r=0;r<2;r++)if(mask&(1<<r))for(auto&c:ms[0].ce[r])if(partial_rejects(c,i)){mask&=~(1<<r);++c.hits;break;}
  if(!mask){++pruned;return;}
 }
 if(i==2*n){if(max==n-1)visit();return;}
 if(i/2>max)return;
 for(int v=0;v<=std::min(max+1,n-1);v++){D[i]=v;dfs_single(i+1,std::max(max,v),mask);if(ms[0].solved)return;}
}
int main(int argc,char**argv){
 int limit=argc>1?std::stoi(argv[1]):7;if(limit<1||limit>10)return 2;
 bool single=argc>2&&std::string(argv[2])=="single";
 Machine m;D[0]=0;
 if(single){
  while(std::cin>>m.id>>m.table){if(m.table.size()!=36)return 2;ms.clear();ms.push_back(m);for(n=1;n<=limit;n++){count=pruned=nodes=0;dfs_single(1,0,3);auto &a=ms[0];std::cerr<<"id="<<a.id<<" n="<<n<<" nodes="<<nodes<<" leaves="<<count<<" pruned="<<pruned<<" checks="<<a.checked<<" filtered="<<a.filtered<<" solved="<<a.solved<<'\n';if(a.solved)break;}}
 }else{
  while(std::cin>>m.id>>m.table){if(m.table.size()!=36)return 2;ms.push_back(m);}
  for(n=1;n<=limit;n++){count=0;dfs(1,0);int left=std::count_if(ms.begin(),ms.end(),[](auto&m){return!m.solved;});uint64_t c=0,f=0;for(auto&m:ms){c+=m.checked;f+=m.filtered;}std::cerr<<"n="<<n<<" enumerated="<<count<<" left="<<left<<" checks="<<c<<" filtered="<<f<<'\n';if(!left)break;}
 }
}
