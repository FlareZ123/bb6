// Exact delayed-carry scanner; no large integer per transition.
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <utility>
#include <vector>
using I=int64_t; using U=uint64_t;
struct State { I s; int last[2]; };
struct Root { std::vector<U> word; State st; };
static I floor2(I x){return x>=0?x/2:(x-1)/2;}
static int bit(const std::vector<U>&w,int i){return (w[i>>6]>>(i&63))&1;}
static void put(std::vector<U>&w,int i){w[i>>6]|=U(1)<<(i&63);}
static int prev_bit(I& s,I u,I C,int d){ I x=2*s-7*d; int b=x<=u-C; s=x+C*b; assert(u-C<s&&s<=u); return b; }
struct Scanner {
 int n, cap, safeExp; I L; U visits=0; int maxWidth=0, deepest=0; bool marginOK=true; U near=0;
 Scanner(int n_,int cap_):n(n_),cap(cap_),L(2*(I(n)+3*I(cap)+10)+6){safeExp=0;while((I(1)<<safeExp)<L+n+I(cap)+10)++safeExp;}
 // Current prefix can be reconstructed exactly from s and old block, using the anchor.
 std::vector<U> reconstruct(const Root&r,const std::vector<I>&u,int j0,int i,I s){
   std::vector<U> w((n+63)/64);for(int k=i-1;k>=0;--k){int b=prev_bit(s,u[k],I(n)+3+j0+k,bit(r.word,k));if(b)put(w,k);}assert(s==r.st.s);return w;
 }
 // Near-boundary checks only need the low safeExp window bits; all high bits are equal.
 void margin(const Root&r,const std::vector<I>&u,int j0,int i,const State&s){
   int j=j0+i;if(j==0)return;
   bool low=s.last[1]<j-n+safeExp, high=s.last[0]<j-n+safeExp;
   if(!low&&!high)return;
   ++near;std::vector<U> w;
   if(i+safeExp>n)w=reconstruct(r,u,j0,i,s.s);
   I z=0,zc=0;
   for(int k=0;k<safeExp&&k<n;++k){int ix=i+k,b=ix<n?bit(r.word,ix):bit(w,ix-n);z+=I(b)<<k;zc+=I(1-b)<<k;}
   if(low){I c=7*z+s.s;if(c==2||c<=0){marginOK=false;std::cerr<<"bad lower margin n="<<n<<" j="<<j<<" c="<<c<<"\n";}}
   if(high){I m=7*zc+6-n-j-s.s;if(m<L){marginOK=false;std::cerr<<"bad upper margin n="<<n<<" j="<<j<<" margin="<<m<<" L="<<L<<"\n";}}
 }
 bool scan_group(const Root&r,int j0){
   int limit=std::min(n,cap-j0);std::vector<I> u(limit+1);std::vector<State> cur(1,r.st),nxt;u[0]=r.st.s;int i=0;
   for(;i<limit&&!cur.empty();++i){int j=j0+i;I C=I(n)+3+j;int d=bit(r.word,i);u[i+1]=floor2(u[i]+7*d);nxt.clear();
     for(const State&s:cur){assert(u[i]-C<s.s&&s.s<=u[i]);margin(r,u,j0,i,s);I base=s.s+7*d;for(int b=0;b<2;++b){I x=base-C*b;if(x%2==0){State t=s;t.s=x/2;t.last[b]=j;nxt.push_back(t);}}}
     visits+=cur.size();cur.swap(nxt);maxWidth=std::max(maxWidth,(int)cur.size());
     if(j0==0&&i%10000==0)std::cerr<<"n="<<n<<" j="<<i+1<<" width="<<cur.size()<<" visits="<<visits<<"\n";
   }
   deepest=std::max(deepest,j0+i);
   if(cur.empty())return true;
   if(j0+i==cap)return false;
   assert(i==n);
   size_t done=0,count=cur.size();
   for(const State&s:cur){Root child{reconstruct(r,u,j0,n,s.s),s};if(!scan_group(child,j0+n))return false;if(j0==0&&++done%10000==0)std::cerr<<"n="<<n<<" roots="<<done<<"/"<<count<<" visits="<<visits<<"\n";}
   return true;
 }
 void scan(){
   assert(n>safeExp&&n>=14&&n%2==0&&cap>0);
   Root root{std::vector<U>((n+63)/64),{1,{-1,-n-1}}};
   bool extinct=scan_group(root,0);
   std::cout<<(extinct?"EXTINCT":"OPEN")<<" n="<<n<<" K="<<deepest<<" cap="<<cap<<" L="<<L<<" margin="<<marginOK<<" visits="<<visits<<" near="<<near<<"\n";
 }
};
int main(int argc,char**argv){if(argc<3)return 2;Scanner(std::stoi(argv[1]),std::stoi(argv[2])).scan();}
