#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
using U=uint64_t;
struct Rule {int dst,src,off;};
struct Machine {int id;std::string table;bool solved=false;};
std::vector<Machine> ms;
int D[20],n;
uint64_t count=0;
bool check(const std::string &p,int rev){
 const int N=6*n+1,H=N-1; U T[122]={},halt=U(1)<<H;T[H]=T[N+H]=halt;
 Rule rules[1200];int nr=0;
 for(int l=0;l<n;l++)for(int q=0;q<6;q++)for(int a=0;a<2;a++){
  int s=3*(2*q+a),dst=a*N+6*l+q;
  if(p[s]=='-'){T[dst]=halt;continue;}
  int w=p[s]-'0',r=p[s+1]=='R',nxt=p[s+2]-'A';
  if(r!=rev)T[dst]=U(1)<<(6*D[2*l+w]+nxt);
  else for(int j=0;j<n;j++)for(int b=0;b<2;b++)if(D[2*j+b]==l)rules[nr++]={dst,b*N+6*j+nxt,w*N};
 }
 while(true){U z=halt;while(true){U old=z;for(int j=0;j<N;j++)if(T[j]&z)z|=U(1)<<j;if(z&1)return false;if(old==z)break;}
  bool changed=false;for(int i=0;i<nr;i++){auto [dst,src,off]=rules[i];U v=T[dst],bits=T[src];while(bits){v|=T[off+std::countr_zero(bits)];bits&=bits-1;}if(v!=T[dst]){T[dst]=v;changed=true;}}
  if(!changed)return true;
 }
}
void visit(){++count;for(auto &m:ms)if(!m.solved){for(int r=0;r<2;r++)if(check(m.table,r)){m.solved=true;std::cout<<m.id<<' '<<r;for(int i=0;i<2*n;i++)std::cout<<D[i];std::cout<<'\n'<<std::flush;break;}}}
void dfs(int i,int max){if(i==2*n){if(max==n-1)visit();return;}if(i/2>max)return;for(int v=0;v<=std::min(max+1,n-1);v++){D[i]=v;dfs(i+1,std::max(max,v));}}
int main(int argc,char**argv){Machine m;while(std::cin>>m.id>>m.table)ms.push_back(m);int limit=argc>1?std::stoi(argv[1]):6;if(limit<1||limit>10)return 2;D[0]=0;for(n=1;n<=limit;n++){count=0;dfs(1,0);int left=std::count_if(ms.begin(),ms.end(),[](auto &m){return !m.solved;});std::cerr<<"n="<<n<<" enumerated="<<count<<" left="<<left<<'\n';if(!left)break;}}
