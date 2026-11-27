#pragma once
#include <algorithm>
#include <cstdint>
#include <vector>

namespace bb6_forward {
using U=std::uint64_t;
using I=std::uint32_t;

// Exact forward block lookup, independent of the absolute clock and target.
// q mod 2^k and (Y-c) mod 2^k identify all selected words B.
struct Table {
 unsigned k,M,mask;
 std::vector<unsigned> d,offset;
 std::vector<std::uint16_t> words;
 explicit Table(unsigned bits):k(bits),M(1u<<k),mask(M-1),d(M),offset(M*M+1),words(M*M) {
  for(unsigned b=1;b<M;b++)d[b]=2*(d[b/2]+b/2);
  for(unsigned q=0;q<M;q++)for(unsigned b=0;b<M;b++)
   ++offset[q*M+((q*b+d[b])&mask)+1];
  for(unsigned i=1;i<offset.size();i++)offset[i]+=offset[i-1];
  auto pos=offset;
  for(unsigned q=0;q<M;q++)for(unsigned b=0;b<M;b++)
   words[pos[q*M+((q*b+d[b])&mask)]++]=std::uint16_t(b);
 }
 template<class Emit> bool each(I q,unsigned Y,I c,Emit emit)const{
  if(c>=q)return true;
  unsigned idx=(q&mask)*M+((Y-c)&mask);
  for(unsigned i=offset[idx];i<offset[idx+1];i++){
   unsigned b=words[i];
   U x=U(c)+U(q)*b+d[b];
   if(x<Y)continue;
   U z=(x-Y)>>k;
   if(z>=U(q)+k)continue;
   if(!emit(I(z)))return false;
  }
  return true;
 }
};
struct Tables{
 std::vector<Table> a;
 explicit Tables(unsigned maxk){a.reserve(maxk);for(unsigned k=1;k<=maxk;k++)a.emplace_back(k);}
 const Table& operator[](unsigned k)const{return a[k-1];}
};
struct Probe {
 bool complete=false;
 I clock=0;
 U visits=0;
 std::size_t peak=0;
 std::vector<I> mids;
};

// A forward block has a unique inverse for each endpoint; different paths
// never merge. Preserve labels after the midpoint. Budget exhaustion is
// inconclusive and must fall back to the exact reverse solver.
template<class Word> Probe probe(const Tables& tables,unsigned maxk,I start,I mid,I end,
                                 const Word& y,I root,U maxVisits,std::size_t maxWidth){
 struct Node{I c,label;};
 Probe p; p.clock=start;p.peak=1;
 std::vector<Node> a{{root,0}},b;
 std::vector<I> midpoints;
 std::vector<bool> live;
 for(I q=start;q<end;){
  if(a.empty()){p.complete=true;return p;}
  if(q==mid){
   midpoints.reserve(a.size());
   for(I i=0;i<a.size();i++){midpoints.push_back(a[i].c);a[i].label=i;}
  }
  if(a.size()>maxVisits-p.visits)return p;
  p.visits+=a.size();
  unsigned k=std::min<I>(maxk,(q<mid?mid:end)-q);
  unsigned Y=unsigned(y(q,k));b.clear();
  for(auto v:a){
   if(!tables[k].each(q,Y,v.c,[&](I z){
    if(b.size()>=maxWidth)return false;
    b.push_back({z,v.label});return true;
   }))return p;
  }
  q+=k;p.clock=q;p.peak=std::max(p.peak,b.size());a.swap(b);
 }
 p.complete=true;
 if(mid==end){
  for(auto v:a)p.mids.push_back(v.c);
 }else{
  live.assign(midpoints.size(),false);
  for(auto v:a)live[v.label]=true;
  for(std::size_t i=0;i<live.size();i++)if(live[i])p.mids.push_back(midpoints[i]);
 }
 std::sort(p.mids.begin(),p.mids.end());
 p.mids.erase(std::unique(p.mids.begin(),p.mids.end()),p.mids.end());
 return p;
}
}
