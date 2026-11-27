#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>
#include <fstream>
#include <string>
#include <bit>
#include <cassert>
using namespace std;using Mask=uint64_t;using Dep=uint32_t;
struct Inst{int write,right,next;};
const array<Inst,12> M={{{1,1,1},{0,0,2},{1,1,2},{0,1,2},{1,0,3},{0,1,1},{1,0,0},{0,0,4},{1,0,3},{1,0,5},{1,0,3},{-1,0,0}}};
struct Rule{int dst,src,off;Dep dep;};
struct Event{int row,t;}; // row=-1: new zero state
struct Mark{size_t edges,rules,watches,zeros;};
struct Search{
 int d,N,H;bool rev;vector<int>D;vector<Mask>rows;vector<Dep>proofs;vector<Rule>rules;vector<vector<int>>bySrc,watches;
 vector<Event>edgeLog,agenda;vector<int>watchLog,zeroLog;Mask z=0;array<Dep,64>zd{};size_t qi=0;
 uint64_t nodes=0,prunes=0,added=0,watchAdds=0,complete=0;int deepest=0;bool found=false,stop=false;chrono::steady_clock::time_point start;double seconds;vector<int>fixed;vector<int> resume;
 Search(int dd,bool rr,double sec,vector<int> f):d(dd),N(6*d+1),H(N-1),rev(rr),D(2*d,-1),rows(2*N),proofs(2*N*N),bySrc(2*N),watches(2*N),seconds(sec),fixed(move(f)){}
 inline void edge(int row,int t,Dep dep){if((rows[row]>>t)&1)return;rows[row]|=1ULL<<t;proofs[row*N+t]=dep;edgeLog.push_back({row,t});agenda.push_back({row,t});++added;}
 inline void zero(int t,Dep dep){if((z>>t)&1)return;z|=1ULL<<t;zd[t]=dep;zeroLog.push_back(t);agenda.push_back({-1,t});}
 inline void reg(int id,int v){Rule r=rules[id];int row=r.off+v;watches[row].push_back(id);watchLog.push_back(row);++watchAdds;Dep dep=proofs[r.src*N+v]|r.dep;Mask x=rows[row]&~rows[r.dst];while(x){int t=countr_zero(x);x&=x-1;edge(r.dst,t,dep|proofs[row*N+t]);}}
 void rule(Rule r){int id=rules.size();rules.push_back(r);bySrc[r.src].push_back(id);Mask x=rows[r.src];while(x){int v=countr_zero(x);x&=x-1;reg(id,v);}}
 bool close(){while(qi<agenda.size()&&!(z&1)){auto [row,t]=agenda[qi++];if(row<0){for(int s=0;s<N;++s)if(!((z>>s)&1)&&((rows[s]>>t)&1))zero(s,proofs[s*N+t]|zd[t]);continue;}
   if(row<N&&((z>>t)&1))zero(row,proofs[row*N+t]|zd[t]);
   for(int id:bySrc[row])reg(id,t);
   size_t cnt=watches[row].size();for(size_t k=0;k<cnt;++k){Rule r=rules[watches[row][k]];int v=row-r.off;assert(v>=0&&v<N&&((rows[r.src]>>v)&1));edge(r.dst,t,r.dep|proofs[r.src*N+v]|proofs[row*N+t]);}
  }agenda.clear();qi=0;return !(z&1);}
 Mark mark(){assert(agenda.empty());return {edgeLog.size(),rules.size(),watchLog.size(),zeroLog.size()};}
 void undo(Mark m){while(watchLog.size()>m.watches){int row=watchLog.back();watchLog.pop_back();watches[row].pop_back();}while(rules.size()>m.rules){bySrc[rules.back().src].pop_back();rules.pop_back();}while(edgeLog.size()>m.edges){auto [row,t]=edgeLog.back();edgeLog.pop_back();rows[row]&=~(1ULL<<t);}while(zeroLog.size()>m.zeros){z&=~(1ULL<<zeroLog.back());zeroLog.pop_back();}}
 bool assign(int k,int l){D[k]=l;int j=k/2,b=k%2;Dep dep=Dep(1)<<k;
  for(int q=0;q<6;++q)for(int a=0;a<2;++a){auto m=M[2*q+a];if(m.write<0)continue;if(m.right!=rev){if(m.write==b)edge(a*N+6*j+q,6*l+m.next,dep);}else rule({a*N+6*l+q,b*N+6*j+m.next,m.write*N,dep});}
  return close();}
 Dep dfs(int pos,int mx){++nodes;deepest=max(deepest,pos);if((nodes&65535)==0){double t=chrono::duration<double>(chrono::steady_clock::now()-start).count();if(t>seconds){stop=true;resume=D;return 0;}if((nodes&1048575)==0)cout<<"nodes "<<nodes<<" prunes "<<prunes<<" depth "<<deepest<<" sec "<<t<<endl;}
  if((pos<2*d&&pos/2>mx)||mx+1+(2*d-pos)<d)return 0;
  if(pos==2*d){if(mx+1!=d)return 0;found=true;++complete;cout<<"FOUND d="<<d<<" reverse="<<rev<<" DFA ";for(auto x:D)cout<<x<<",";cout<<endl;ofstream f("far-result.txt");f<<d<<" "<<rev<<"\n";for(auto x:D)f<<x<<" ";f<<"\n";for(auto x:rows)f<<x<<" ";f<<"\n"<<z<<"\n";return 0;}
  int lo=0,hi=min(d-1,mx+1);if(pos<int(fixed.size()))lo=hi=fixed[pos];
  for(int x=lo;x<=hi;++x){if(x>mx+1||x>=d)continue;if(pos%2==1&&pos/2>max(mx,x))continue;Mark m=mark();Dep dep=0;if(!assign(pos,x)){++prunes;dep=zd[0];assert(dep);}else dep=dfs(pos+1,max(mx,x));D[pos]=-1;undo(m);if(found||stop)return 0;if(dep&&!(dep&(Dep(1)<<pos)))return dep;}
  return 0;
 }
 void run(){start=chrono::steady_clock::now();edge(H,H,0);edge(N+H,H,0);for(int l=0;l<d;++l)edge(N+6*l+5,H,0);zero(H,0);assert(close());if(assign(0,0))dfs(1,0);cout<<"END d="<<d<<" reverse="<<rev<<" found="<<found<<" stop="<<stop<<" nodes="<<nodes<<" prunes="<<prunes<<" edges="<<added<<" watches="<<watchAdds<<" sec="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;if(stop){cout<<"RESUME ";for(auto x:resume)if(x>=0)cout<<x;cout<<endl;}}
};
int main(int argc,char**argv){int d=argc>1?stoi(argv[1]):7;bool rev=argc>2?stoi(argv[2]):0;double sec=argc>3?stod(argv[3]):20;vector<int> pre;if(argc>4){for(char x:string(argv[4]))pre.push_back(x-'0');}if(d<1||d>10)return 1;Search s(d,rev,sec,pre);s.run();}
