#include <array>
#include <algorithm>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <fstream>
#include <vector>
#include <cassert>
using namespace std;
using Table=array<int,12>;
constexpr int W=16,C=512;
struct State {
 int q=0,h=0;
 array<uint64_t,W> b{};
 bool read()const{return b[C/64]&1;}
 State next(int v)const{
  State z=*this;z.q=v>>2;
  z.b[C/64]=(z.b[C/64]&~uint64_t(1))|((v>>1)&1);
  if(v&1){++z.h;for(int i=0;i<W;i++)z.b[i]=(z.b[i]>>1)|(i+1<W?z.b[i+1]<<63:0);}
  else{--z.h;for(int i=W-1;i>=0;i--)z.b[i]=(z.b[i]<<1)|(i?z.b[i-1]>>63:0);}
  return z;
 }
};
// At least one of the compared heads is at the translated origin.  The
// tape arrays are head-relative and contain every possibly written cell.
static bool suffix(const State&a,const State&b,int lo){
 int k=C+lo-a.h, i=k/64, bit=k%64;
 assert(k>=0&&k<1024);
 if((a.b[C/64]^b.b[C/64]) && i<C/64)return false;
 if(((a.b[i]^b.b[i])>>bit)!=0)return false;
 return memcmp(a.b.data()+i+1,b.b.data()+i+1,(W-i-1)*8)==0;
}
static bool prefix(const State&a,const State&b,int hi){
 int k=C+hi-a.h, i=k/64, bit=k%64;
 assert(k>=0&&k<1024);
 if((a.b[C/64]^b.b[C/64]) && i>C/64)return false;
 uint64_t mask=bit==63?~uint64_t(0):(uint64_t(1)<<(bit+1))-1;
 if(((a.b[i]^b.b[i])&mask)!=0)return false;
 return memcmp(a.b.data(),b.b.data(),i*8)==0;
}
struct Far {int rev,d;vector<int>D;vector<uint32_t>T;uint32_t z;};
static bool far(const Table&p,int rev,const vector<int>&D,Far&out){
 int d=D.size()/2,N=6*d+1;uint32_t h=1u<<(N-1);vector<uint32_t>T(2*N);T[N-1]=T[2*N-1]=h;
 vector<array<int,3>> rules;
 for(int b=0;b<2;b++)for(int l=0;l<d;l++)for(int q=0;q<6;q++){
  int a=p[2*q+b],dst=b*N+6*l+q;
  if(a==24){T[dst]=h;continue;}
  int n=a>>2,w=(a>>1)&1,r=a&1;
  if(r!=rev)T[dst]=1u<<(6*D[2*l+w]+n);
  else for(int j=0;j<d;j++)for(int x=0;x<2;x++)if(D[2*j+x]==l)rules.push_back({dst,x*N+6*j+n,w*N});
 }
 bool changed;
 do{changed=false;for(auto [dst,src,off]:rules){uint32_t v=T[src],nw=T[dst];while(v){int b=__builtin_ctz(v);v&=v-1;nw|=T[off+b];}if(nw!=T[dst]){T[dst]=nw;changed=true;}}}while(changed);
 uint32_t z=h,old;do{old=z;for(int i=0;i<N;i++)if(T[i]&z)z|=1u<<i;}while(old!=z);
 if(z&1)return false;out={rev,d,D,T,z};return true;
}
static bool find_far(const Table&p,int maxd,Far&f){
 for(int d=1;d<=maxd;d++){int n=1;for(int i=1;i<2*d;i++)n*=d;
  for(int j=0;j<n;j++){vector<int>D(2*d);int x=j;for(int i=2*d-1;i>0;i--){D[i]=x%d;x/=d;}
   for(int rev=0;rev<2;rev++)if(far(p,rev,D,f))return true;
  }
 }return false;
}
template<class T>static void arr(ostream&o,const T&x){o<<'[';bool first=true;for(auto a:x){if(!first)o<<',';first=false;o<<a;}o<<']';}
struct Runner{
 int limit=450,maxd=2;array<State,451> hist;vector<Table> opens;uint64_t cycles=0,last=0,splits=0,fars=0;int maxquery=0;ostream&out;
 explicit Runner(ostream&o):out(o){}
 void visit(Table&p,int t,State cur){
  for(;t<=limit;t++){
   int lo=cur.h,hi=cur.h;
   for(int i=t-1;i>=0;i--){const auto&z=hist[i];lo=min(lo,z.h);hi=max(hi,z.h);if(z.q!=cur.q)continue;
    int d=cur.h-z.h;
    if(d>=0&&suffix(z,cur,lo)){++cycles;out<<"[\"cycle\","<<i<<','<<t-i<<",true,"<<lo<<']';return;}
    if(d<=0&&prefix(z,cur,hi)){++cycles;out<<"[\"cycle\","<<i<<','<<t-i<<",false,"<<hi<<']';return;}
   }
   int s=2*cur.q+cur.read(),v=p[s];
   if(v==24){maxquery=max(maxquery,t);if(count(p.begin(),p.end(),24)==1){++last;out<<"[\"last\","<<t<<','<<s<<']';return;}
    ++splits;out<<"[\"split\","<<t<<','<<s<<",[";hist[t]=cur;bool first=true;
    for(int w=0;w<2;w++)for(int r=0;r<2;r++)for(int q=0;q<6;q++){int mv=4*q+2*w+r;if(!first)out<<',';first=false;p[s]=mv;visit(p,t+1,cur.next(mv));}
    p[s]=24;out<<"]]";return;
   }
   hist[t]=cur;cur=cur.next(v);
  }
  Far f;if(find_far(p,maxd,f)){++fars;out<<"[\"far\","<<f.rev<<','<<f.d<<',';arr(out,f.D);out<<',';int N=6*f.d+1;arr(out,vector<uint32_t>(f.T.begin(),f.T.begin()+N));out<<',';arr(out,vector<uint32_t>(f.T.begin()+N,f.T.end()));out<<','<<f.z<<']';return;}
  opens.push_back(p);out<<"[\"open\",";arr(out,p);out<<']';
 }
 void run(Table p){out<<"{\"tree\":";visit(p,0,State{});out<<",\"open\":[";bool first=true;for(auto&t:opens){if(!first)out<<',';first=false;arr(out,t);}out<<"],\"counts\":{\"cycle\":"<<cycles<<",\"last\":"<<last<<",\"split\":"<<splits<<",\"far\":"<<fars<<",\"open\":"<<opens.size()<<",\"maxquery\":"<<maxquery<<"}}\n";cerr<<"cycles="<<cycles<<" last="<<last<<" split="<<splits<<" far="<<fars<<" open="<<opens.size()<<" maxquery="<<maxquery<<'\n';}
};
int main(int argc,char**argv){
 Table p{7,24,11,24,14,24,24,16,17,11,24,24};Runner r(cout);
 if(argc==15){r.limit=stoi(argv[1]);r.maxd=stoi(argv[2]);assert(r.limit>=0&&r.limit<=450&&r.maxd>=1&&r.maxd<=2);for(int i=0;i<12;i++)p[i]=stoi(argv[i+3]);}
 else if(argc!=1)return 2;
 r.run(p);
}
