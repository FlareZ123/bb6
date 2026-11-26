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
#include <climits>
#include <vector>
#include <omp.h>
using U=uint64_t; using I=uint32_t; using W=__uint128_t;
constexpr I missing=UINT32_MAX;
using std::vector;
static inline U dw(U b){return (b&0xAAAAAAAAAAAAAAAAull)+2*(b&0xCCCCCCCCCCCCCCCCull)+4*(b&0xF0F0F0F0F0F0F0F0ull)+8*(b&0xFF00FF00FF00FF00ull)+16*(b&0xFFFF0000FFFF0000ull)+32*(b&0xFFFFFFFF00000000ull);}
static int fit(I F,I rem){return int(std::min({rem,I(30),I(63-__builtin_clzll(F)-1)}));}
struct Block {
 I q; int k; U Y,F,M; double inv;
 Block(I end,I rem):q(end-fit(end,rem)),k(fit(end,rem)),Y(0),F(end),M((U(1)<<k)-1),inv(1.0/F){}
 I parent(I z)const {
  U X=(U(z)<<k)+Y,b=U(double(X)*inv);
  if(b*F>X)--b; else if((b+1)*F<=X)++b;
  if(b*F>X || (b+1)*F<=X)b=X/F;
  for(int j=0;j<2;++j,++b)if(b<=M){U f=U(q)*b+dw(b);if(f<=X&&X-f<U(q))return I(X-f);}
  return missing;
 }
};
struct Seen {
 vector<U> bits;
 explicit Seen(I n):bits((U(n)+63)/64){}
 bool insert(I x){U m=U(1)<<(x&63);U& w=bits[x>>6];if(w&m)return false;w|=m;return true;}
 void clear(I x){bits[x>>6]&=~(U(1)<<(x&63));}
};
struct Bits {
 vector<U> a;
 explicit Bits(I n):a((U(n)+63)/64){}
 int get(I i)const{return (a[i>>6]>>(i&63))&1;}
 void set(I i,int b){if(b)a[i>>6]|=U(1)<<(i&63);}
};
struct Prefix {
 vector<std::shared_ptr<const Bits>> blocks;
 I carry,r,last,run;
 int get(I i,I h)const {if(i==0)return 1;--i;return blocks[i/h]->get(i%h);}
};
struct DSU {
 vector<int> p; explicit DSU(int n):p(n,-1){}
 int find(int x){int r=x;while(p[r]>=0)r=p[r];while(x!=r){int y=p[x];p[x]=r;x=y;}return r;}
 int unite(int a,int b){a=find(a);b=find(b);if(a==b)return a;if(p[a]>p[b])std::swap(a,b);p[a]+=p[b];p[b]=a;return a;}
};
struct Entry{I c;int id;};
template<class Bit>vector<I> live(I start,I F,Bit y,U&work){
 I r=std::min(I(22),F-start),q=F-r;uint32_t M=1u<<r,mask=M-1,Y=0;
 for(int j=0;j<r;j++)Y|=uint32_t(y(q+j))<<j;
 Seen small(M);vector<uint32_t>res{Y};small.insert(Y);
 for(int j=0;j<r;j++){
  uint32_t shift=uint32_t((U(q+j)<<j)&mask),count=res.size();
  for(uint32_t i=0;i<count;i++){uint32_t c=(res[i]-shift)&mask;if(small.insert(c))res.push_back(c);}
 }
 vector<I>a;
 a.reserve(std::min(U(q), U(res.size())*((U(q)+M-1)/M)));
 for(U base=0;base<U(q);base+=M)for(auto x:res)if(base+x<U(q))a.push_back(I(base+x));
 Seen seen(q);
 while(q>start&&!a.empty()){
  Block b(q,q-start);for(int j=0;j<b.k;j++)b.Y|=U(y(b.q+j))<<j;
  work+=a.size();size_t w=0;
  for(I z:a){I c=b.parent(z);if(c!=missing&&seen.insert(c))a[w++]=c;}
  a.resize(w);for(I c:a)seen.clear(c);q=b.q;
 }
 return a;
}
template<class Bit>vector<I> filter(I start,I F,Bit y,I root,const vector<I>&ends,U&work){
 if(ends.size()>INT_MAX)throw std::runtime_error("mid count");
 vector<Entry>a;a.reserve(ends.size());for(int i=0;i<(int)ends.size();i++)a.push_back({ends[i],i});DSU d(a.size());
 while(F>start&&!a.empty()){
  Block b(F,F-start);for(int j=0;j<b.k;j++)b.Y|=U(y(b.q+j))<<j;work+=a.size();size_t w=0;
  for(auto e:a){I c=b.parent(e.c);if(c!=missing)a[w++]={c,e.id};}a.resize(w);
  std::sort(a.begin(),a.end(),[](Entry x,Entry y){return x.c<y.c;});w=0;
  for(auto e:a){if(w&&a[w-1].c==e.c)a[w-1].id=d.unite(a[w-1].id,e.id);else a[w++]=e;}a.resize(w);F=b.q;
 }
 auto it=std::find_if(a.begin(),a.end(),[&](Entry e){return e.c==root;});if(it==a.end())return {};
 int label=d.find(it->id);vector<I>out;
 for(int i=0;i<(int)ends.size();i++)if(d.find(i)==label)out.push_back(ends[i]);std::sort(out.begin(),out.end());return out;
}
// Each checkpoint is a reproducible computational artifact, not a proof certificate.
static void save(const std::string& path,I n,I K,I h,bool half,I s,I gap,const vector<Prefix>&gs){
 if(path.empty())return;
 std::ofstream f(path+".tmp",std::ios::binary|std::ios::trunc);
 auto put=[&](I x){f.write(reinterpret_cast<const char*>(&x),sizeof x);};
 put(0x50314331);put(n);put(K);put(h);put(half);put(s);put(gap);put(I(gs.size()));
 for(const auto&g:gs){put(g.carry);put(g.r);put(g.last);put(g.run);for(auto& b:g.blocks)f.write(reinterpret_cast<const char*>(b->a.data()),b->a.size()*sizeof(U));}
 f.close();if(!f||std::rename((path+".tmp").c_str(),path.c_str()))throw std::runtime_error("checkpoint write");
}
static void load(const std::string& path,I n,I K,I h,bool half,I&s,I&gap,vector<Prefix>&gs){
 if(path.empty())return;
 std::ifstream f(path,std::ios::binary);if(!f)return;
 auto get=[&](){I x=0;f.read(reinterpret_cast<char*>(&x),sizeof x);if(!f)throw std::runtime_error("checkpoint read");return x;};
 if(get()!=0x50314331||get()!=n)throw std::runtime_error("checkpoint index");
 I oldK=get();if(oldK>K||get()!=h||get()!=half)throw std::runtime_error("checkpoint parameters");
 s=get();gap=get();I count=get();if(s<1||(s-1)%h||U(s)+n>K||count<1||count>INT_MAX)throw std::runtime_error("checkpoint state");
 gs.clear();
 for(I i=0;i<count;i++){Prefix g;g.carry=get();g.r=get();g.last=get();g.run=get();for(I j=0;j<(s-1)/h;j++){auto b=std::make_shared<Bits>(h);f.read(reinterpret_cast<char*>(b->a.data()),b->a.size()*sizeof(U));if(!f)throw std::runtime_error("checkpoint block");g.blocks.push_back(b);}gs.push_back(std::move(g));}
 std::cout<<"RESUME s="<<s<<" count="<<count<<std::endl;
}
int main(int argc,char**argv){
 if(argc<4||argc>6)return 2;
 bool half=argc>=5&&std::string(argv[4])=="half";
 if(argc>=5&&!half&&std::string(argv[4])!="full")return 2;
 std::string path=argc==6?argv[5]:"";
 U nn=std::stoull(argv[1]),KK=std::stoull(argv[2]),hh=std::stoull(argv[3]);
 if(nn>UINT32_MAX||KK>UINT32_MAX||hh>UINT32_MAX||nn+KK+3>=UINT32_MAX)return 2;
 I n=I(nn),K=I(KK),h=I(hh);
 if(n<14||n%2||K<=n||h<1||h>n)return 2;
 U A=U(n)+K+2,L=2*(U(n)+3*U(K)+10)+6;W prod=W(A)*L;
 auto safe=[&](I g){int64_t e=int64_t(n)-g;return e>=126||(e>=0&&(W(6)<<e)>prod);};
 if((n<128&&A>(W(1)<<n))||!safe(0)||!safe(1))return 3;
 auto t=std::chrono::steady_clock::now();I s=1,maxgap=1;vector<Prefix>gs={Prefix{{},(n+2)/2,3,1,1}};
 load(path,n,K,h,half,s,maxgap,gs);
 if(!safe(maxgap))throw std::runtime_error("checkpoint margin");
 for(;U(s)+n<=K;){
  struct Part{vector<Prefix>next;U work=0,fw=0;size_t mids=0;I maxgap=0;};vector<Part>parts(gs.size());
#pragma omp parallel for schedule(dynamic)
  for(int gi=0;gi<(int)gs.size();gi++){
   const auto&g=gs[gi];auto&part=parts[gi];auto y=[&](I q){I i=q-n-3;return i<n?0:g.get(i-n,h);};
   auto mids=live(n+s+h+3,2*n+s+3,y,part.work);part.mids=mids.size();
   auto good=filter(n+s+3,n+s+h+3,y,g.carry,mids,part.fw);
   for(I a:good){
    I c=a;Bits extra(h);
    for(I i=s+h;i-->s;){I q=n+i+3; U v=2*U(c)+y(q);if(v>=2*U(q))throw std::runtime_error("rewind");if(v>=q){extra.set(i-s,1);v-=q;}c=I(v);}
    if(c!=g.carry)throw std::runtime_error("root");
    if(half&&s==1&&extra.get(0)!=0)continue; // B mod 4 = 1
    Prefix g2=g;g2.carry=a;auto appended=std::make_shared<Bits>(h);
    for(I j=0;j<h;j++){
     I v=g2.r+7*extra.get(j),bit=v%2;g2.r=v/2;appended->set(j,bit);
     g2.run=bit==g2.last?g2.run+1:1;g2.last=bit;I gap=std::min(s+j+1,g2.run+1);
     part.maxgap=std::max(part.maxgap,gap);if(!safe(gap))throw std::runtime_error("margin");
    }
    g2.blocks.push_back(appended);part.next.push_back(std::move(g2));
   }
  }
  vector<Prefix>next;U work=0,fw=0,mid=0;
  for(auto&part:parts){work+=part.work;fw+=part.fw;mid+=part.mids;maxgap=std::max(maxgap,part.maxgap);for(auto&g:part.next)next.push_back(std::move(g));}
  std::cout<<"s="<<s<<" h="<<h<<" old="<<gs.size()<<" mids="<<mid<<" next="<<next.size()<<" work="<<work<<" filter="<<fw<<" gap="<<maxgap<<" sec="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count()<<std::endl;
  if(next.empty()){std::cout<<"END "<<n<<" "<<n+s<<std::endl;return 0;}
  s+=h;gs=std::move(next);save(path,n,K,h,half,s,maxgap,gs);
 }
 std::cout<<"END "<<n<<" 0"<<std::endl;return 1;
}
