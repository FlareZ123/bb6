#include <algorithm>
#include <cstdint>
#include <iostream>
#include <queue>
#include <stdexcept>
#include <unordered_map>
#include <vector>
using namespace std;
struct Rule {uint8_t write; int8_t dir; uint8_t next;};
static constexpr Rule T[6][2]={{{1,1,1},{0,1,4}},{{1,-1,2},{0,1,0}},{{1,-1,0},{1,-1,3}},{{1,-1,2},{1,-1,5}},{{0,-1,2},{0,-1,1}},{{1,-1,4},{0,0,6}}};
using u64=uint64_t;
struct Edge {uint32_t to;uint8_t label;};
int main(int argc,char **argv){
 int upto=argc>1?stoi(argv[1]):16;
 for(int R=7;R<=upto;R++){
  if(R+11>30)break;
  unordered_map<u64,uint32_t> ids;
  vector<u64> nodes;
  vector<vector<Edge>> edges;
  auto push=[&](u64 v)->uint32_t{
   auto it=ids.find(v);
   if(it!=ids.end())return it->second;
   auto id=uint32_t(nodes.size());
   ids.emplace(v,id);nodes.push_back(v);edges.emplace_back();
   return id;
  };
  for(int r=0;r<1<<R;r++)push(((171ull+((u64)r<<11))<<8)+84);
  int ordinary=0,remote=0;
  for(uint32_t i=0;i<nodes.size();i++){
   u64 key=nodes[i],bits=key>>8;
   int st=key&7,off=(key>>3)&31,bit=(bits>>off)&1;
   if(off==1 || (st==5 && (bit==1 || (bits&((1ull<<off)-1))==0)))continue;
   Rule t=T[st][bit];
   if(t.next==6)throw runtime_error("unexpected halt");
   u64 changed=t.write?bits|(1ull<<off):bits&~(1ull<<off);
   int nextOff=off+t.dir;
   if(nextOff>R+10){
    remote+=6;
    for(int q=0;q<6;q++){
     uint32_t j=push((changed<<8)|(u64(R+10)<<3)|q);
     edges[i].push_back({j,uint8_t(q)});
    }
   }else{
    ordinary++;
    uint32_t j=push((changed<<8)|(u64(nextOff)<<3)|t.next);
    edges[i].push_back({j,6});
   }
  }
  vector<int> ranks(64,-1);
  for(int mask=0;mask<64;mask++){
   vector<uint32_t> indeg(nodes.size(),0),dist(nodes.size(),0);
   queue<uint32_t> pending;
   for(const auto &out:edges)
    for(const auto &e:out)
     if(e.label==6 || (mask>>e.label&1))indeg[e.to]++;
   for(uint32_t i=0;i<nodes.size();i++)
    if(!indeg[i])pending.push(i);
   int seen=0,mx=0;
   while(!pending.empty()){
    auto u=pending.front();pending.pop();seen++;
    for(auto e:edges[u])if(e.label==6 || (mask>>e.label&1)){
     dist[e.to]=max(dist[e.to],dist[u]+1);
     mx=max(mx,int(dist[e.to]));
     if(--indeg[e.to]==0)pending.push(e.to);
    }
   }
   if(seen==(int)nodes.size())ranks[mask]=mx;
  }
  vector<int> acyclic,cyclic,maximal,minimal;
  for(int m=0;m<64;m++)(ranks[m]>=0?acyclic:cyclic).push_back(m);
  for(int m:acyclic){
   bool isMax=true;
   for(int other:acyclic)if(m!=other && (m&other)==m)isMax=false;
   if(isMax)maximal.push_back(m);
  }
  for(int m:cyclic){
   bool isMin=true;
   for(int other:cyclic)if(m!=other && (m&other)==other)isMin=false;
   if(isMin)minimal.push_back(m);
  }
  auto name=[](int m){string out;for(int i=0;i<6;i++)
   if(m>>i&1)out+=char('A'+i);
   return out;
  };
  cout<<"R="<<R<<" states="<<nodes.size()<<" edges="<<ordinary+remote
      <<" acyclicMasks="<<acyclic.size()<<" maximalAcyclic";
  for(int m:maximal)cout<<" "<<name(m)<<":"<<ranks[m];
  cout<<" minimalCyclic";
  for(int m:minimal)cout<<" "<<name(m);
  cout<<"\n";
  if(nodes.size()>800000)break;
 }
}
