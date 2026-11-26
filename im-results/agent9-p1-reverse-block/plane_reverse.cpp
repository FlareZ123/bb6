
#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <random>
#include <stdexcept>
#include <vector>
using U=uint64_t;
using I=uint32_t;
using std::vector;
static U dw(U b){return (b&0xAAAAAAAAAAAAAAAAull)+2*(b&0xCCCCCCCCCCCCCCCCull)+4*(b&0xF0F0F0F0F0F0F0F0ull)+8*(b&0xFF00FF00FF00FF00ull)+16*(b&0xFFFF0000FFFF0000ull)+32*(b&0xFFFFFFFF00000000ull);}
static U lowmask(unsigned n){return n==64?~U(0):(U(1)<<n)-1;}
struct Bits {
 I n;
 vector<U> a;
 explicit Bits(I n0):n(n0),a((U(n)+63)/64+1){}
 void set(I i){a[i>>6]|=U(1)<<(i&63);}
 bool get(I i)const{return (a[i>>6]>>(i&63))&1;}
 U read(U i)const {
  U j=i>>6; unsigned s=i&63;
  if(j>=a.size()-1)return 0;
  return s?(a[j]>>s)|(a[j+1]<<(64-s)):a[j];
 }
 U count()const{U n=0;for(U w:a)n+=__builtin_popcountll(w);return n;}
};
static void transpose(U* a){
 constexpr U masks[]={0x5555555555555555ull,0x3333333333333333ull,0x0f0f0f0f0f0f0f0full,0x00ff00ff00ff00ffull,0x0000ffff0000ffffull,0x00000000ffffffffull};
 for(unsigned h=0;h<6;h++){
  unsigned s=1u<<h; U m=masks[h];
  for(unsigned i=0;i<64;i+=2*s)for(unsigned j=i;j<i+s;j++){
   U t=((a[j]>>s)^a[j+s])&m;
   a[j]^=t<<s; a[j+s]^=t;
  }
 }
}
// Exact broad reverse image of a k-bit target word. No fitted-window
// assumption: the full digit interval partition is used.
static Bits planes(const Bits& ends,unsigned k,U Y){
 if(k<6||k>20||ends.n<=k||Y>=(U(1)<<k))throw std::runtime_error("parameters");
 U M=U(1)<<k,q=ends.n-k,F=ends.n;
 U rows=(q+M-1)/M, stride=(rows+63)/64;
 vector<U> lane(M*stride);
 for(U B=0;B<M;B++){
  U W=q*B+dw(B);
  U z0=(W+M-1-Y)/M;
  U c0=M*z0+Y-W;
  if(c0>=q||z0>=F)continue;
  U count=std::min((q-1-c0)/M+1,F-z0);
  U* out=lane.data()+c0*stride;
  for(U j=0;j<count/64;j++)out[j]|=ends.read(z0+64*j);
  if(count%64)out[count/64]|=ends.read(z0+64*(count/64))&lowmask(count%64);
 }
 Bits ans{I(q)};
 for(U b=0;b<stride;b++)for(U r=0;r<M;r+=64){
  U a[64];
  for(U i=0;i<64;i++)a[i]=lane[(r+i)*stride+b];
  transpose(a);
  for(U i=0;i<64&&64*b+i<rows;i++){
   U off=(64*b+i)*(M/64)+r/64;
   if(off<ans.a.size()-1)ans.a[off]=a[i];
  }
 }
 if(q%64)ans.a[q/64]&=lowmask(q%64);
 return ans;
}
static Bits scalar(Bits a,unsigned k,U Y){
 for(unsigned j=k;j-->0;){
  I q=a.n-1;
  Bits b(q);
  unsigned y=(Y>>j)&1;
  for(I z=0;z<a.n;z++)if(a.get(z)){
   U X=2*U(z)+y;
   if(X<2*U(q))b.set(I(X%q));
  }
  a=std::move(b);
 }
 return a;
}
static Bits sparse(const Bits& a,unsigned k,U Y){
 U M=U(1)<<k,F=a.n,q=F-k;
 if(2*M>F)throw std::runtime_error("fit");
 Bits b{I(q)};
 double inv=1.0/F;
 for(U w=0;w<a.a.size()-1;w++){
  U bits=a.a[w];
  while(bits){
   U z=64*w+__builtin_ctzll(bits);
   bits&=bits-1;
   U X=M*z+Y,B=U(double(X)*inv);
   if(B*F>X)--B;else if((B+1)*F<=X)++B;
   if(B*F>X||(B+1)*F<=X)B=X/F;
   for(int j=0;j<2;++j,++B)if(B<M){
    U W=q*B+dw(B);
    if(W<=X&&X-W<q){b.set(I(X-W));break;}
   }
  }
 }
 return b;
}
static void test(){
 for(unsigned i=0;i<64;i++)for(unsigned j=0;j<64;j++){
  U a[64]={};a[i]=U(1)<<j;transpose(a);
  for(unsigned r=0;r<64;r++)assert(a[r]==(r==j?U(1)<<i:0));
 }
 std::mt19937_64 rng(20261126);
 unsigned cases=0;
 for(I F:{7,8,9,15,32,63,64,65,127,128,129,200,255,256,257,1023,1024,1025,2000,4096})
  for(unsigned k=6;k<=10&&k<F;k++)for(int t=0;t<12;t++){
   U Y=rng()% (U(1)<<k);
   Bits a(F);
   for(I z=0;z<F;z++)if(t==0||((rng()&7)<unsigned(t%8)))a.set(z);
   auto x=planes(a,k,Y),y=scalar(a,k,Y);
   if(x.a!=y.a)throw std::runtime_error("scalar mismatch");
   if((U(2)<<k)<=F&&sparse(a,k,Y).a!=y.a)throw std::runtime_error("sparse mismatch");
   ++cases;
  }
 std::cout<<"Passed "<<cases<<" exact block comparisons and 4096 transpose basis vectors\n";
}
int main(int argc,char**argv){
 if(argc==1){test();return 0;}
 I F=std::stoul(argv[1]);unsigned k=std::stoul(argv[2]),density=std::stoul(argv[3]);
 std::mt19937_64 rng(9);Bits a(F);
 for(I z=0;z<F;z++)if(rng()%1000<density)a.set(z);
 U Y=rng()% (U(1)<<k);
 auto t=std::chrono::steady_clock::now();auto x=planes(a,k,Y);
 double d=std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count();
 t=std::chrono::steady_clock::now();auto y=sparse(a,k,Y);
 double s=std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count();
 if(x.a!=y.a)throw std::runtime_error("mismatch");
 std::cout<<F<<" "<<k<<" "<<density<<" "<<a.count()<<" -> "<<x.count()<<" planes="<<d<<" sparse="<<s<<" ratio="<<s/d<<"\n";
 return 0;
}
