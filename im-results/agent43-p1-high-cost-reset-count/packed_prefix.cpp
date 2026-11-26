// Exact delayed-carry prefix experiment. Derived from Agent9's prefix_bitmap.cpp.
// Fixed-size immutable shared bit blocks avoid one byte per target bit per prefix.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <cstdio>
#include <string>
#include <vector>
#include <omp.h>
using U=uint64_t;
using std::vector;
static inline U dw(U b){return (b&0xAAAAAAAAAAAAAAAAull)+2*(b&0xCCCCCCCCCCCCCCCCull)+4*(b&0xF0F0F0F0F0F0F0F0ull)+8*(b&0xFF00FF00FF00FF00ull)+16*(b&0xFFFF0000FFFF0000ull)+32*(b&0xFFFFFFFF00000000ull);}
static int fit(int F,int rem){return std::min({rem,28,63-__builtin_clzll(F)-1});}
struct Block {
 int q,k; U Y,F,M; double inv;
 Block(int end,int rem):q(end-fit(end,rem)),k(fit(end,rem)),Y(0),F(end),M((U(1)<<k)-1),inv(1.0/F){}
 int parent(int z)const {
  U X=(U(z)<<k)+Y,b=U(double(X)*inv);
  if(b*F>X)--b; else if((b+1)*F<=X)++b;
  if(b*F>X || (b+1)*F<=X)b=X/F;
  for(int j=0;j<2;++j,++b)if(b<=M){U f=U(q)*b+dw(b);if(f<=X&&X-f<U(q))return int(X-f);}
  return -1;
 }
};
struct Seen {
 vector<U> bits;
 explicit Seen(int n):bits((U(n)+63)/64){}
 bool insert(int x){U m=U(1)<<(x&63);U& w=bits[x>>6];if(w&m)return false;w|=m;return true;}
 void clear(int x){bits[x>>6]&=~(U(1)<<(x&63));}
};
struct Bits {
 vector<U> a;
 explicit Bits(int n):a((U(n)+63)/64){}
 int get(int i)const{return (a[i>>6]>>(i&63))&1;}
 void set(int i,int b){if(b)a[i>>6]|=U(1)<<(i&63);}
};
struct Prefix {
 vector<std::shared_ptr<const Bits>> blocks;
 int carry,r,last,run;
 int get(int i,int h)const {if(i==0)return 1;--i;return blocks[i/h]->get(i%h);}
};
struct DSU {
 vector<int> p; explicit DSU(int n):p(n,-1){}
 int find(int x){int r=x;while(p[r]>=0)r=p[r];while(x!=r){int y=p[x];p[x]=r;x=y;}return r;}
 int unite(int a,int b){a=find(a);b=find(b);if(a==b)return a;if(p[a]>p[b])std::swap(a,b);p[a]+=p[b];p[b]=a;return a;}
};
struct Entry{int c,id;};
template<class Bit>vector<int> live(int start,int F,Bit y,U&work){
 int r=std::min(22,F-start),q=F-r;uint32_t M=1u<<r,mask=M-1,Y=0;
 for(int j=0;j<r;j++)Y|=uint32_t(y(q+j))<<j;
 Seen small(M);vector<uint32_t>res{Y};small.insert(Y);
 for(int j=0;j<r;j++){
  uint32_t shift=uint32_t((U(q+j)<<j)&mask),count=res.size();
  for(uint32_t i=0;i<count;i++){uint32_t c=(res[i]-shift)&mask;if(small.insert(c))res.push_back(c);}
 }
 vector<int>a;
 a.reserve(std::min(U(q), U(res.size())*((U(q)+M-1)/M)));
 for(U base=0;base<U(q);base+=M)for(auto x:res)if(base+x<U(q))a.push_back(int(base+x));
 Seen seen(q);
 while(q>start&&!a.empty()){
  Block b(q,q-start);for(int j=0;j<b.k;j++)b.Y|=U(y(b.q+j))<<j;
  work+=a.size();size_t w=0;
  for(int z:a){int c=b.parent(z);if(c>=0&&seen.insert(c))a[w++]=c;}
  a.resize(w);for(int c:a)seen.clear(c);q=b.q;
 }
 return a;
}
template<class Bit>vector<int> filter(int start,int F,Bit y,int root,const vector<int>&ends,U&work){
 vector<Entry>a;a.reserve(ends.size());for(int i=0;i<(int)ends.size();i++)a.push_back({ends[i],i});DSU d(a.size());
 while(F>start&&!a.empty()){
  Block b(F,F-start);for(int j=0;j<b.k;j++)b.Y|=U(y(b.q+j))<<j;work+=a.size();size_t w=0;
  for(auto e:a){int c=b.parent(e.c);if(c>=0)a[w++]={c,e.id};}a.resize(w);
  std::sort(a.begin(),a.end(),[](Entry x,Entry y){return x.c<y.c;});w=0;
  for(auto e:a){if(w&&a[w-1].c==e.c)a[w-1].id=d.unite(a[w-1].id,e.id);else a[w++]=e;}a.resize(w);F=b.q;
 }
 auto it=std::find_if(a.begin(),a.end(),[&](Entry e){return e.c==root;});if(it==a.end())return {};
 int label=d.find(it->id);vector<int>out;
 for(int i=0;i<(int)ends.size();i++)if(d.find(i)==label)out.push_back(ends[i]);std::sort(out.begin(),out.end());return out;
}
// Each checkpoint is a reproducible computational artifact, not a proof certificate.
static void save(const std::string& path,int n,int K,int h,bool half,int s,int gap,const vector<Prefix>&gs){
 if(path.empty())return;
 std::ofstream f(path+".tmp",std::ios::binary|std::ios::trunc);
 auto put=[&](int x){f.write(reinterpret_cast<const char*>(&x),sizeof x);};
 put(0x50314331);put(n);put(K);put(h);put(half);put(s);put(gap);put(int(gs.size()));
 for(const auto&g:gs){put(g.carry);put(g.r);put(g.last);put(g.run);for(auto& b:g.blocks)f.write(reinterpret_cast<const char*>(b->a.data()),b->a.size()*sizeof(U));}
 f.close();if(!f||std::rename((path+".tmp").c_str(),path.c_str()))throw std::runtime_error("checkpoint write");
}
static void load(const std::string& path,int n,int K,int h,bool half,int&s,int&gap,vector<Prefix>&gs){
 if(path.empty())return;
 std::ifstream f(path,std::ios::binary);if(!f)return;
 auto get=[&](){int x=0;f.read(reinterpret_cast<char*>(&x),sizeof x);if(!f)throw std::runtime_error("checkpoint read");return x;};
 if(get()!=0x50314331||get()!=n||get()!=K||get()!=h||get()!=half)throw std::runtime_error("checkpoint parameters");
 s=get();gap=get();int count=get();if(s<1||(s-1)%h||s+n>K||count<1)throw std::runtime_error("checkpoint state");
 gs.clear();
 for(int i=0;i<count;i++){Prefix g;g.carry=get();g.r=get();g.last=get();g.run=get();for(int j=0;j<(s-1)/h;j++){auto b=std::make_shared<Bits>(h);f.read(reinterpret_cast<char*>(b->a.data()),b->a.size()*sizeof(U));if(!f)throw std::runtime_error("checkpoint block");g.blocks.push_back(b);}gs.push_back(std::move(g));}
 std::cout<<"RESUME s="<<s<<" count="<<count<<std::endl;
}
int main(int argc,char**argv){
 if(argc<4||argc>6)return 2;
 bool half=argc>=5&&std::string(argv[4])=="half";
 if(argc>=5&&!half&&std::string(argv[4])!="full")return 2;
 std::string path=argc==6?argv[5]:"";
 int n=std::stoi(argv[1]),K=std::stoi(argv[2]),h=std::stoi(argv[3]);
 if(n<14||n%2||K<=n||n>250000000||K>1000000000||h<1||h>n)return 2;
 U A=U(n)+K+2,L=2*(U(n)+3*U(K)+10)+6,prod=A*L;
 auto safe=[&](int g){int e=n-g;return e>=62||(e>=0&&(U(6)<<e)>prod);};
 if((n<63&&A>(U(1)<<n))||!safe(0)||!safe(1))return 3;
 auto t=std::chrono::steady_clock::now();int s=1,maxgap=1;vector<Prefix>gs={Prefix{{},(n+2)/2,3,1,1}};
 load(path,n,K,h,half,s,maxgap,gs);
 for(;s+n<=K;){
  struct Part{vector<Prefix>next;U work=0,fw=0;size_t mids=0;int maxgap=0;};vector<Part>parts(gs.size());
#pragma omp parallel for schedule(dynamic)
  for(int gi=0;gi<(int)gs.size();gi++){
   const auto&g=gs[gi];auto&part=parts[gi];auto y=[&](int q){int i=q-n-3;return i<n?0:g.get(i-n,h);};
   auto mids=live(n+s+h+3,2*n+s+3,y,part.work);part.mids=mids.size();
   auto good=filter(n+s+3,n+s+h+3,y,g.carry,mids,part.fw);
   for(int a:good){
    int c=a;Bits extra(h);
    for(int i=s+h-1;i>=s;i--){int q=n+i+3; U v=2*U(c)+y(q);if(v>=2*U(q))throw std::runtime_error("rewind");if(v>=q){extra.set(i-s,1);v-=q;}c=v;}
    if(c!=g.carry)throw std::runtime_error("root");
    if(half&&s==1&&extra.get(0)!=0)continue; // B mod 4 = 1
    Prefix g2=g;g2.carry=a;auto appended=std::make_shared<Bits>(h);
    for(int j=0;j<h;j++){
     int v=g2.r+7*extra.get(j),bit=v%2;g2.r=v/2;appended->set(j,bit);
     g2.run=bit==g2.last?g2.run+1:1;g2.last=bit;int gap=std::min(s+j+1,g2.run+1);
     part.maxgap=std::max(part.maxgap,gap);if(!safe(gap))throw std::runtime_error("margin");
    }
    g2.blocks.push_back(appended);part.next.push_back(std::move(g2));
   }
  }
  vector<Prefix>next;U work=0,fw=0,mid=0;
  for(auto&part:parts){work+=part.work;fw+=part.fw;mid+=part.mids;maxgap=std::max(maxgap,part.maxgap);for(auto&g:part.next)next.push_back(std::move(g));}
  std::cout<<"s="<<s<<" h="<<h<<" old="<<gs.size()<<" mids="<<mid<<" next="<<next.size()<<" work="<<work<<" filter="<<fw<<" gap="<<maxgap<<" sec="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count()<<std::endl;
  if(next.empty()){std::cout<<"END "<<n<<" "<<n+s<<std::endl;return 0;}
  if(s+h+n>K)break;s+=h;gs=std::move(next);save(path,n,K,h,half,s,maxgap,gs);
 }
 std::cout<<"END "<<n<<" 0"<<std::endl;return 1;
}
