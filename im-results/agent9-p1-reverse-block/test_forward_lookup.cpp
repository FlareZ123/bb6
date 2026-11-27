#include "forward_lookup.hpp"
#include <cassert>
#include <iostream>
#include <random>
using namespace bb6_forward;
static std::vector<I> scalar(I q,unsigned k,unsigned Y,I c){
 std::vector<I>a{c},b;
 for(unsigned j=0;j<k;j++,q++){
  b.clear();unsigned y=(Y>>j)&1;
  for(I z:a)for(U x:{U(0),U(q)}){
   U t=z+x;
   if(t>=y&&((t-y)&1)==0&&(t-y)/2<q)b.push_back(I((t-y)/2));
  }
  a.swap(b);
 }
 std::sort(a.begin(),a.end());return a;
}
int main(){
 Tables t(8);U count=0,wide=0,probes=0;
 auto check=[&](I q,unsigned k,unsigned Y,I c){
  std::vector<I>a;t[k].each(q,Y,c,[&](I z){a.push_back(z);return true;});
  std::sort(a.begin(),a.end());assert(a==scalar(q,k,Y,c));++count;
 };
 for(I q=1;q<=32;q++)for(unsigned k=1;k<=6;k++)
  for(unsigned Y=0;Y<(1u<<k);Y++)for(I c=0;c<q;c++)check(q,k,Y,c);
 std::mt19937_64 rng(45352466);
 for(unsigned j=0;j<200000;j++){
  I q=1+I(rng()%2147483000u);unsigned k=1+rng()%8;
  check(q,k,rng()&((1u<<k)-1),rng()%q);++wide;
 }
 for(unsigned j=0;j<10000;j++){
  I q=1+rng()%1000;unsigned k=1+rng()%40,h=1+rng()%k;
  U Y=rng()&((U(1)<<k)-1);I c=rng()%q;
  auto y=[&](I r,unsigned l){return (Y>>(r-q))&((U(1)<<l)-1);};
  auto p=probe(t,8,q,q+h,q+k,y,c,1000000,100000);
  std::vector<I> expected;
  auto steps=[&](I start,unsigned n,U word,std::vector<I> a){
   std::vector<I>b;
   for(unsigned s=0;s<n;s++,start++){
    b.clear();unsigned bit=(word>>s)&1;
    for(I v:a)for(U x:{U(0),U(start)})if(v+x>=bit&&((v+x-bit)&1)==0&&(v+x-bit)/2<start)b.push_back(I((v+x-bit)/2));
    a.swap(b);
   }
   return a;
  };
  auto mid=steps(q,h,Y,{c});
  for(I m:mid)if(!steps(q+h,k-h,Y>>h,{m}).empty())expected.push_back(m);
  std::sort(expected.begin(),expected.end());expected.erase(std::unique(expected.begin(),expected.end()),expected.end());
  assert(p.complete&&p.mids==expected);
  auto limited=probe(t,8,q,q+h,q+k,y,c,1,1);
  if(limited.complete)assert(limited.mids==expected);
  ++probes;
 }
 std::cout<<"forward lookup exact cases="<<count<<" wide="<<wide<<" midpoint probes="<<probes<<"\n";
}
