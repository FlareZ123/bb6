// Exact delayed-bit carry scan. No floating point participates in decisions.
// Build: g++ -std=c++17 -O3 -march=native lagblock.cpp -o lagblock
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
#ifdef __BMI2__
#include <immintrin.h>
#endif
using namespace std;
using U=uint64_t;

uint32_t even(U x){
#ifdef __BMI2__
 return _pext_u64(x,0x5555555555555555ULL);
#else
 x&=0x5555555555555555ULL;
 x=(x|(x>>1))&0x3333333333333333ULL;
 x=(x|(x>>2))&0x0f0f0f0f0f0f0f0fULL;
 x=(x|(x>>4))&0x00ff00ff00ff00ffULL;
 x=(x|(x>>8))&0x0000ffff0000ffffULL;
 x=(x|(x>>16))&0x00000000ffffffffULL;
 return uint32_t(x);
#endif
}
struct Bits {
 vector<U> a,b; int w=0;
 explicit Bits(int max):a((max+63)/64+2),b(a.size()){}
 void init(int c){fill(a.begin(),a.end(),0);a[c/64]=1ULL<<(c%64);w=c/64+1;}
 U rd(int p) const {
  if(p<0)return p<=-64?0:a[0]<<(-p);
  int j=p/64,k=p%64;
  if(j>=w)return 0;
  return (a[j]>>k)|(k&&j+1<w?a[j+1]<<(64-k):0);
 }
 // Output bit c iff input bit 2c+y or 2c+y-weight is present.
 bool step(int weight,int y){
  int count=(weight+63)/64+1,nonzero=0;
  for(int j=0;j<count;j++){
   int p=128*j+y;
   U lo=rd(p)|rd(p-weight),hi=rd(p+64)|rd(p+64-weight);
   b[j]=U(even(lo))|(U(even(hi))<<32);
   if(b[j])nonzero=j+1;
  }
  w=nonzero;swap(a,b);return w!=0;
 }
};
// x and y are little-endian low-prefix words for B and 7B.
// c is the weighted arithmetic carry; r is multiplication-by-seven carry.
struct Prefix {string x,y;int c,r;};
int gap(const string &y){
 int s=y.size(),j=s-1;
 while(j>=0&&y[j]==y.back())j--;
 return min(s,s-j);
}
int run(int n,int K,int cap,int block){
 if(n<14||n%2||K<=n||K>100000||block<1)return -4;
 Bits z(n+K+200);
 vector<Prefix> p={{"1","1",(n+2)/2,3}};
 int peak=1,prepeak=1,maxgap=1;
 long long work=0,tests=0;
 auto start=chrono::steady_clock::now();
 U A=n+K+2,L=2*(n+3*K+10)+6,product=A*L;
 // Given K<=100000 and n<K, all products fit uint64_t.
 auto safe=[&](int g){int e=n-g;return e>=62||(e>=0&&(U(6)<<e)>product);};
 if((n<63&&A>(U(1)<<n))||!safe(0))return -2;
 // The first low prefix is forced; extend in blocks thereafter.
 for(int s=1;s<=K-n;){
  int end=s==1?1:min(s+block-1,K-n);
  // Every intervening valid prefix extends a previously retained prefix.
  // Its leading run gap can grow by at most the block length.
  for(auto &u:p){
   int g=gap(u.y)+end-s+1;maxgap=max(maxgap,g);
   if(!safe(g)){cerr<<"margin failed "<<n<<" "<<s<<" "<<g<<endl;return -2;}
  }
  for(int i=s-1;i<end;i++){
   if(i==0)continue;
   vector<Prefix> q;
   for(auto &u:p){
    int a=n+i+3,y=i>=n?u.y[i-n]-'0':0;
    for(int x=0;x<2;x++){
     int v=u.c+a*x-y;if(v<0||v%2)continue;
     int r=u.r+7*x;
     q.push_back({u.x+char('0'+x),u.y+char('0'+r%2),v/2,r/2});
    }
   }
   p=move(q);prepeak=max(prepeak,int(p.size()));
   if(int(p.size())>cap)return -3;
  }
  vector<Prefix> q;
  for(auto &u:p){
   z.init(u.c);bool ok=true;tests++;
   for(int i=end;i<n+end;i++){
    int y=i>=n?u.y[i-n]-'0':0;work++;
    if(!z.step(n+i+3,y)){ok=false;break;}
   }
   if(ok)q.push_back(move(u));
  }
  p=move(q);peak=max(peak,int(p.size()));
  if(end==1||end%1024<block||p.empty())
   cout<<n<<" s="<<end<<" live="<<p.size()<<" peak="<<peak
       <<" prepeak="<<prepeak<<" maxgap="<<maxgap<<" tests="<<tests
       <<" work="<<work<<" sec="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
  if(p.empty())return end+n;
  s=end+1;
 }
 return 0;
}
int main(int argc,char**argv){
 if(argc>=3){
  int n=stoi(argv[1]),K=stoi(argv[2]),b=argc>3?stoi(argv[3]):32;
  int result=run(n,K,100000,b);cout<<"END "<<n<<" "<<result<<endl;
  return result>0?0:1;
 }
 bool ok=true;
 for(auto [n,K]:vector<pair<int,int>>{{30,82},{286,1442},{350,586},{1614,5824},{2990,6154},{3342,13730}}){
  int result=run(n,K,100000,n==30?4:32);cout<<"END "<<n<<" "<<result<<endl;
  ok=ok&&result==K;
 }
 return ok?0:1;
}
