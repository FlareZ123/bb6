// Discovery only; all candidates are independently checked by DomainPackedStack.
#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <cstdint>
#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <chrono>
#include <cassert>
#include <tuple>
using namespace std;
using T=array<int,12>;
struct Params{int base,mod,bits;};
struct S{int s,l,r;}; struct W{int next,pushed;};
struct Node{uint64_t key;int push[2]={-1,-1};vector<pair<int,int>> edges;vector<W> wait;};
struct Stack{Params p;vector<Node> nodes{{0,{-1,-1},{{0,0}},{}}};unordered_map<uint64_t,int> ids{{0,0}};
 int id(uint64_t key){auto it=ids.find(key);if(it!=ids.end())return it->second;int j=nodes.size();ids.emplace(key,j);nodes.push_back(Node{key});return j;}
 uint64_t encode_push(uint64_t key,int w){int bits=p.bits,mask=(1<<bits)-1;int tail=key&mask,res=key>>bits;return (((res*p.base+w)%p.mod)<<bits)|(((tail<<1)|w)&mask);}
};
int check(const T&t,int target,Params a,Params b,int cap){Stack stacks[2]{{a},{b}};vector<S> todo{{0,0,0}};unordered_set<uint64_t> seen{0};bool bad=false;
 auto add=[&](int s,int l,int r){if(bad)return;if(s==target||t[s]==0){bad=true;return;}uint64_t key=(uint64_t(s)<<40)|(uint64_t(l)<<20)|r;if(seen.insert(key).second){if((int)seen.size()>cap){bad=true;return;}todo.push_back({s,l,r});}};
 auto pop=[&](int d,W w,pair<int,int> e){if(d)add(w.next+e.first,w.pushed,e.second);else add(w.next+e.first,e.second,w.pushed);};
 for(size_t i=0;i<todo.size()&&!bad;i++){auto x=todo[i];int lo=t[x.s]<0?1:t[x.s],hi=t[x.s]<0?24:t[x.s];if(lo==0)return 0;
 for(int val=lo;val<=hi&&!bad;val++){int v=val-1,d=v%2,w=v/2%2,u=d?x.l:x.r,y=d?x.r:x.l;Stack& a=stacks[1-d];Stack& b=stacks[d];int j=a.nodes[u].push[w];if(j<0){j=a.id(a.encode_push(a.nodes[u].key,w));a.nodes[u].push[w]=j;pair<int,int> e={w,u};if(find(a.nodes[j].edges.begin(),a.nodes[j].edges.end(),e)==a.nodes[j].edges.end()){a.nodes[j].edges.push_back(e);for(auto z:a.nodes[j].wait)pop(1-d,z,e);}}W ww{2*(v/4),j};b.nodes[y].wait.push_back(ww);for(auto e:b.nodes[y].edges)pop(d,ww,e);}}
 return bad?0:seen.size();}
vector<Params> schedule(int level){vector<Params> p;int maxm=level?31:17,maxk=level?6:4;for(int m=2;m<=maxm;m++)for(int a=1;a<m;a++){if(a!=1&&a!=2&&a!=m-1&&a!=m-2&&(!level||a>5))continue;for(int k=0;k<=maxk;k++){if(m*(1<<k)>512)continue;p.push_back({a,m,k});}}stable_sort(p.begin(),p.end(),[](auto a,auto b){return a.mod*(1<<a.bits)<b.mod*(1<<b.bits);});return p;}
int main(int argc,char**argv){
 assert(argc==2||argc==3);int target=atoi(argv[1]),level=argc==3;string tag=to_string(target);
 ifstream in((level?"modhard":"wide-start")+tag+".txt");ofstream cert((level?"modwide":"modular")+tag+".txt"),fail((level?"modfinal":"modhard")+tag+".txt");assert(in&&cert&&fail);T t;int cnt=0,solved=0,maxsize=0;auto p=schedule(level);auto start=chrono::steady_clock::now();
 while(in>>t[0]){for(int i=1;i<12;i++)in>>t[i];cnt++;int sz=0;Params a{},b{};
  for(auto x:p){sz=check(t,target,x,x,level?10000:3000);if(sz){a=b=x;break;}}
  if(!sz&&level){int n=min((int)p.size(),70);for(int k=0;k<2*n-1&&!sz;k++)for(int i=max(0,k-n+1);i<n&&i<=k&&!sz;i++){int j=k-i;if(i==j)continue;sz=check(t,target,p[i],p[j],5000);if(sz){a=p[i];b=p[j];}}}
  ostream&out=sz?cert:fail;for(int v:t)out<<v<<' ';if(sz){for(auto x:{a,b})out<<x.base<<' '<<x.mod<<' '<<x.bits<<' ';out<<sz;solved++;maxsize=max(maxsize,sz);}out<<'\n';}
 cout<<target<<" MOD "<<solved<<'/'<<cnt<<" max states "<<maxsize<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
