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
using namespace std;using T=array<int,12>;
struct State{int s,l,r;};struct Wait{State x;int v;};struct Edge{int bits=0;vector<Wait> wait;};
int check(const T&t,int k,int target,int cap){
 int mask=(1<<k)-1,shift=k-1; vector<int> ds[12];for(int i=0;i<12;i++)if(t[i]>=0)ds[i]={t[i]};else for(int v=1;v<=24;v++)if(i!=6||v!=9)ds[i].push_back(v);
 unordered_set<uint64_t> seen{0};vector<State>todo{{0,0,0}};unordered_map<int,Edge>E[2];E[0][0].bits=E[1][0].bits=1;
 bool bad=false;
 auto add=[&](State x){if(bad)return;if(x.s==target){bad=true;return;}uint64_t key=(uint64_t(x.s)<<(2*k))|(uint64_t(x.l)<<k)|x.r;if(seen.insert(key).second){if(int(seen.size())>cap){bad=true;return;}todo.push_back(x);}};
 auto pop=[&](State x,int v,int e){int q=v/4,w=v/2%2;if(v%2)add({2*q+(x.r&1),((x.l<<1)|w)&mask,(x.r>>1)|(e<<shift)});else add({2*q+(x.l&1),(x.l>>1)|(e<<shift),((x.r<<1)|w)&mask});};
 for(size_t i=0;i<todo.size()&&!bad;i++){auto x=todo[i];for(int val:ds[x.s]){if(val==0)return 0;int v=val-1,d=v%2,w=v/2%2,u=d?x.l:x.r,y=d?x.r:x.l;int ee=u>>shift;auto &a=E[1-d][((u<<1)|w)&mask];if(!(a.bits&(1<<ee))){a.bits|=1<<ee;for(const auto &z:a.wait)pop(z.x,z.v,ee);}auto &b=E[d][y];b.wait.push_back({x,v});for(int e=0;e<2;e++)if(b.bits&(1<<e))pop(x,v,e);if(bad)break;}}
 return bad?0:int(seen.size());
}
int main(int argc,char**argv){int target=atoi(argv[1]);ifstream in("open"+to_string(target)+".txt");ofstream cert("ngram"+to_string(target)+".txt"),fail("hard"+to_string(target)+".txt");T t;int cnt=0,solved=0,maxk=0,maxsize=0;auto start=chrono::steady_clock::now();while(in>>t[0]){for(int i=1;i<12;i++)in>>t[i];cnt++;int k=1,size=0;for(;k<=16;k++){size=check(t,k,target,20000);if(size)break;}ostream&out=size?cert:fail;for(int v:t)out<<v<<' ';if(size){out<<k<<' '<<size;solved++;maxk=max(maxk,k);maxsize=max(maxsize,size);}out<<'\n';}cerr<<target<<" solved "<<solved<<"/"<<cnt<<" hard "<<cnt-solved<<" maxk "<<maxk<<" size "<<maxsize<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<'\n';}
