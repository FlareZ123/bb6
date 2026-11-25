#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <string>
#include <vector>
using U=uint64_t;
struct Rule {int dst,src,off;};
struct Machine {int id;std::string table;bool solved=false;};
std::vector<Machine> ms;
int D[20],n;
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
int main(int argc,char**argv){Machine m;while(std::cin>>m.id>>m.table)ms.push_back(m);std::ifstream f(argv[1]);std::string code;while(f>>code){n=(code.size()-1)/2;if(n>10)continue;for(int i=0;i<2*n;i++)D[i]=code[i+1]-'0';for(auto &m:ms)if(!m.solved&&check(m.table,code[0]-'0')){m.solved=true;std::cout<<m.id<<' '<<code<<'\n';}}for(auto &m:ms)if(!m.solved)std::cerr<<m.id<<' '<<m.table<<'\n';}
