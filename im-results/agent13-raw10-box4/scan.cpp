#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <cstdint>
#include <algorithm>
#include <chrono>
#include <cassert>
using namespace std;
using U=__uint128_t;using T=array<int,12>;
constexpr int LIM=127;
struct Conf{U l,r;int q,h;};
struct Res{int kind,n,s,period;bool right;int edge;};
enum{HALT,HOLE,CYCLE,SIDE,OPEN};
U mask(int n){return n>=128?~U(0):((U(1)<<n)-1);}
Res trace(const T&t){
 Conf his[LIM+1];U l=0,r=0;int q=0,h=0;
 for(int n=0;n<=LIM;n++){
  int s=2*q+int(r&1),v=t[s];
  if(v<=0)return {v==0?HALT:HOLE,n,s,0,false,0};
  int lo=h,hi=h;
  for(int j=n-1;j>=0;j--){
   auto &c=his[j];lo=min(lo,c.h);hi=max(hi,c.h);
   if(c.q!=q)continue;
   if(c.l==l&&c.r==r)return {CYCLE,j,0,n-j,h>=c.h,h>=c.h?lo:hi};
   if(h>c.h&&r==c.r&&((l^c.l)&mask(c.h-lo))==0)return {SIDE,j,0,n-j,true,lo};
   if(h<c.h&&l==c.l&&((r^c.r)&mask(hi-c.h+1))==0)return {SIDE,j,0,n-j,false,hi};
  }
  if(n==LIM)return {OPEN,n,0,0,false,0};
  his[n]={l,r,q,h};--v;int w=v/2%2;
  if(v%2){l=(l<<1)|w;r>>=1;h++;}else{r=(((r>>1)<<1)|w)<<1|(l&1);l>>=1;h--;}
  q=v/4;
 }
 abort();
}
int main(int argc,char**argv){
 int target=atoi(argv[1]);vector<int> ds[12];int fx[6]={8,14,11,7,17,4};
 for(int i=0;i<12;i++){if(i<6)ds[i]={fx[i]};else if(i==target)ds[i]={0};else for(int v=1;v<=24;v++)if(i!=6||v!=9)ds[i].push_back(v);}
 T root;uint64_t total=1;for(int i=0;i<12;i++){root[i]=ds[i].size()==1?ds[i][0]:-1;total*=ds[i].size();}
 vector<T> stk{root};uint64_t count[5]={},mass[5]={};int mx=0;T best{};ofstream out("open"+to_string(target)+".txt");
 auto start=chrono::steady_clock::now();
 while(!stk.empty()){
  auto t=stk.back();stk.pop_back();auto z=trace(t);count[z.kind]++;
  if(z.kind==HOLE){for(int v:ds[z.s]){auto c=t;c[z.s]=v;stk.push_back(c);}continue;}
  uint64_t m=1;for(int i=0;i<12;i++)if(t[i]<0)m*=ds[i].size();mass[z.kind]+=m;
  if(z.kind==HALT&&z.n+1>mx){mx=z.n+1;best=t;}
  if(z.kind==OPEN){for(int v:t)out<<v<<' ';out<<'\n';}
 }
 uint64_t sum=0;for(int i=0;i<5;i++){sum+=mass[i];cerr<<i<<":"<<count[i]<<"/"<<mass[i]<<" ";}cerr<<"total "<<total<<" max "<<mx<<" best ";for(int v:best)cerr<<v<<" ";cerr<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<'\n';assert(sum==total);
}
