// Derived from Agent43 packed_wide.cpp and Agent9 plane_prefix_v2.cpp.
// Exact broad carry sweep with AVX512 fitted queries and packed target words.
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
#include <immintrin.h>
#include <omp.h>
using U=uint64_t; using I=uint32_t; using W=__uint128_t;
constexpr I missing=UINT32_MAX;
using std::vector;
static inline U mask(unsigned k){return k==64?~U(0):(U(1)<<k)-1;}
static inline U dw(U b){return (b&0xAAAAAAAAAAAAAAAAull)+2*(b&0xCCCCCCCCCCCCCCCCull)+4*(b&0xF0F0F0F0F0F0F0F0ull)+8*(b&0xFF00FF00FF00FF00ull)+16*(b&0xFFFF0000FFFF0000ull)+32*(b&0xFFFFFFFF00000000ull);}
static int fit(I F,I rem){return int(std::min({rem,I(30),I(63-__builtin_clzll(F)-1)}));}
struct Block {
 I q; int k; U Y,F,M; double inv;
 Block(I end,I rem):q(end-fit(end,rem)),k(fit(end,rem)),Y(0),F(end),M((U(1)<<k)-1),inv(1.0/F){}
 I parent(I z,U* word=nullptr)const {
  U X=(U(z)<<k)+Y,b=U(double(X)*inv);
  if(b*F>X)--b; else if((b+1)*F<=X)++b;
  if(b*F>X || (b+1)*F<=X)b=X/F;
  for(int j=0;j<2;++j,++b)if(b<=M){U f=U(q)*b+dw(b);if(f<=X&&X-f<U(q)){if(word)*word=b;return I(X-f);}}
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
 explicit Bits(I n):a((U(n)+63)/64+1){}
 int get(I i)const{return (a[i>>6]>>(i&63))&1;}
 U read(I i,unsigned k)const{unsigned s=i&63;U v=a[i>>6]>>s;if(s&&k>64-s)v|=a[(i>>6)+1]<<(64-s);return v&mask(k);}
 void put(I i,unsigned k,U v){unsigned s=i&63;a[i>>6]|=v<<s;if(s&&k>64-s)a[(i>>6)+1]|=v>>(64-s);}
};
struct Prefix {
 vector<std::shared_ptr<const Bits>> blocks;
 I carry,r,last,run;
 U word(int64_t i,unsigned k,I h)const {
  U v=0;unsigned out=0;
  if(i<0){auto gap=std::min<int64_t>(k,-i);i+=gap;out+=gap;}
  if(out<k&&i==0){v|=U(1)<<out;++i;++out;}
  while(out<k){U off=U(i-1);I j=off/h,p=off%h;unsigned t=std::min<unsigned>(k-out,h-p);v|=blocks.at(j)->read(p,t)<<out;out+=t;i+=t;}
  return v;
 }
};
struct DSU {
 vector<int> p; explicit DSU(int n):p(n,-1){}
 int find(int x){int r=x;while(p[r]>=0)r=p[r];while(x!=r){int y=p[x];p[x]=r;x=y;}return r;}
 int unite(int a,int b){a=find(a);b=find(b);if(a==b)return a;if(p[a]>p[b])std::swap(a,b);p[a]+=p[b];p[b]=a;return a;}
};
struct Entry{I c;int id;};
#if defined(__AVX512F__) && defined(__AVX512DQ__) && defined(__AVX512VL__)
struct Block8 {
 const Block& b; __m512i F,q,M,Y,shift,one;__m512d inv;
 explicit Block8(const Block& x):b(x),F(_mm512_set1_epi64(x.F)),q(_mm512_set1_epi64(x.q)),M(_mm512_set1_epi64(x.M)),Y(_mm512_set1_epi64(x.Y)),shift(_mm512_set1_epi64(x.k)),one(_mm512_set1_epi64(1)),inv(_mm512_set1_pd(x.inv)){}
 static __m512i wt(__m512i w){
  auto a=_mm512_and_si512(w,_mm512_set1_epi64(0xAAAAAAAAAAAAAAAAull));
  auto b=_mm512_slli_epi64(_mm512_and_si512(w,_mm512_set1_epi64(0xCCCCCCCCCCCCCCCCull)),1);
  auto c=_mm512_slli_epi64(_mm512_and_si512(w,_mm512_set1_epi64(0xF0F0F0F0F0F0F0F0ull)),2);
  auto d=_mm512_slli_epi64(_mm512_and_si512(w,_mm512_set1_epi64(0xFF00FF00FF00FF00ull)),3);
  auto e=_mm512_slli_epi64(_mm512_and_si512(w,_mm512_set1_epi64(0xFFFF0000FFFF0000ull)),4);
  return _mm512_add_epi64(_mm512_add_epi64(a,b),_mm512_add_epi64(c,d),e);
 }
 void parent8(const I* in,I* out)const{
  auto z=_mm512_cvtepu32_epi64(_mm256_loadu_si256((const __m256i*)in));
  auto X=_mm512_add_epi64(_mm512_sllv_epi64(z,shift),Y);
  auto B=_mm512_cvttpd_epu64(_mm512_mul_pd(_mm512_cvtepu64_pd(X),inv));
  auto BF=_mm512_mullo_epi64(B,F);
  auto hi=_mm512_cmp_epu64_mask(BF,X,_MM_CMPINT_GT);
  auto lo=_mm512_cmp_epu64_mask(_mm512_add_epi64(BF,F),X,_MM_CMPINT_LE);
  B=_mm512_mask_sub_epi64(B,hi,B,one);B=_mm512_mask_add_epi64(B,lo,B,one);
  BF=_mm512_mullo_epi64(B,F);
  auto bad=_mm512_cmp_epu64_mask(BF,X,_MM_CMPINT_GT)|_mm512_cmp_epu64_mask(_mm512_add_epi64(BF,F),X,_MM_CMPINT_LE);
  auto c0=_mm512_sub_epi64(X,_mm512_add_epi64(_mm512_mullo_epi64(B,q),wt(B)));
  auto good0=_mm512_cmp_epu64_mask(c0,q,_MM_CMPINT_LT)&_mm512_cmp_epu64_mask(B,M,_MM_CMPINT_LE);
  auto B1=_mm512_add_epi64(B,one);
  auto c1=_mm512_sub_epi64(X,_mm512_add_epi64(_mm512_mullo_epi64(B1,q),wt(B1)));
  auto good1=_mm512_cmp_epu64_mask(c1,q,_MM_CMPINT_LT)&_mm512_cmp_epu64_mask(B1,M,_MM_CMPINT_LE);
  auto c=_mm512_mask_blend_epi64(good1,_mm512_set1_epi64(missing),c1);
  c=_mm512_mask_mov_epi64(c,good0,c0);
  _mm256_storeu_si256((__m256i*)out,_mm512_cvtepi64_epi32(c));
  while(bad){unsigned j=__builtin_ctz(bad);bad&=bad-1;out[j]=b.parent(in[j]);}
 }
};
#endif
template<class Word>vector<I> live(I start,I F,Word y,U&work){
 I r=std::min(I(22),F-start),q=F-r;uint32_t M=1u<<r,mask=M-1,Y=y(q,r);
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
  Block b(q,q-start);b.Y=y(b.q,b.k);work+=a.size();size_t w=0,j=0;
#if defined(__AVX512F__) && defined(__AVX512DQ__) && defined(__AVX512VL__)
  if(a.size()>=64){Block8 b8(b);for(;j+8<=a.size();j+=8){I c[8];b8.parent8(a.data()+j,c);for(I x:c)if(x!=missing&&seen.insert(x))a[w++]=x;}}
#endif
  for(;j<a.size();j++){I c=b.parent(a[j]);if(c!=missing&&seen.insert(c))a[w++]=c;}
  a.resize(w);for(I c:a)seen.clear(c);q=b.q;
 }
 return a;
}
template<class Word>vector<I> filter(I start,I F,Word y,I root,const vector<I>&ends,U&work){
 if(ends.size()>INT_MAX)throw std::runtime_error("mid count");
 vector<Entry>a;a.reserve(ends.size());for(int i=0;i<(int)ends.size();i++)a.push_back({ends[i],i});DSU d(a.size());
 while(F>start&&!a.empty()){
  Block b(F,F-start);b.Y=y(b.q,b.k);work+=a.size();size_t w=0;
  for(auto e:a){I c=b.parent(e.c);if(c!=missing)a[w++]={c,e.id};}a.resize(w);
  if(a.size()>1)std::sort(a.begin(),a.end(),[](Entry x,Entry y){return x.c<y.c;});w=0;
  for(auto e:a){if(w&&a[w-1].c==e.c)a[w-1].id=d.unite(a[w-1].id,e.id);else a[w++]=e;}a.resize(w);F=b.q;
 }
 auto it=std::find_if(a.begin(),a.end(),[&](Entry e){return e.c==root;});if(it==a.end())return {};
 int label=d.find(it->id);vector<I>out;
 for(int i=0;i<(int)ends.size();i++)if(d.find(i)==label)out.push_back(ends[i]);std::sort(out.begin(),out.end());return out;
}
// Reconstruct a chosen child from its endpoint. The fixed h-step word is
// unique for a given upper endpoint. Every block is exactly checked.
static Prefix child(I n,I s,I h,const Prefix& g,I a){
 auto y=[&](I q,unsigned k){return g.word(int64_t(q)-2*int64_t(n)-3,k,h);};
 I start=n+s+3,F=start+h,c=a;Bits extra(h);
 while(F>start){Block b(F,F-start);b.Y=y(b.q,b.k);U code=0;c=b.parent(c,&code);if(c==missing)throw std::runtime_error("rewind");extra.put(b.q-start,b.k,code);F=b.q;}
 if(c!=g.carry)throw std::runtime_error("root");
 Prefix g2=g;g2.carry=a;auto appended=std::make_shared<Bits>(h);
 for(U j=0;j<h;j+=64){unsigned t=std::min<U>(64,U(h)-j);W v=W(7)*extra.read(I(j),t)+g2.r;g2.r=I(v>>t);appended->a[j/64]=U(v)&mask(t);}
 g2.blocks.push_back(appended);g2.last=appended->get(h-1);g2.run=0;for(I j=h;j>0&&appended->get(j-1)==g2.last;--j)++g2.run;if(g2.run==h&&g.last==g2.last)g2.run+=g.run;
 return g2;
}
// Compact restart file: a transcript of chosen (parent index, midpoint) pairs.
// It preserves a numerical computation, not a coverage certificate.
static void save(const std::string& path,I n,I K,I h,bool half,const vector<vector<std::pair<I,I>>>& layers){
 if(path.empty())return;std::ofstream f(path+".tmp",std::ios::trunc);f<<n<<" "<<K<<" "<<h<<" "<<half<<"\n";
 for(const auto& layer:layers){f<<layer.size()<<"\n";for(auto e:layer)f<<e.first<<" "<<e.second<<"\n";}
 f.close();if(!f||std::rename((path+".tmp").c_str(),path.c_str()))throw std::runtime_error("checkpoint write");
}
static void load(const std::string& path,I n,I K,I h,bool half,I&s,vector<Prefix>&gs,vector<vector<std::pair<I,I>>>&layers){
 if(path.empty())return;std::ifstream f(path);if(!f)return;I nn,kk,hh,ha;if(!(f>>nn>>kk>>hh>>ha)||nn!=n||kk>K||hh!=h||ha!=half)throw std::runtime_error("checkpoint parameters");
 I cnt;while(f>>cnt){if(U(s)+n>K||cnt>INT_MAX)throw std::runtime_error("checkpoint layer");vector<Prefix> next;vector<std::pair<I,I>> layer;
 for(I j=0;j<cnt;j++){I i,a;if(!(f>>i>>a)||i>=gs.size()||a>=n+s+h+3)throw std::runtime_error("checkpoint child");next.push_back(child(n,s,h,gs[i],a));layer.push_back({i,a});}
 layers.push_back(std::move(layer));gs=std::move(next);if(gs.empty())break;s+=h;}
 std::cout<<"RESUME s="<<s<<" count="<<gs.size()<<std::endl;
}
int main(int argc,char**argv){
 if(argc<4||argc>6)return 2;
 bool half=argc>=5&&std::string(argv[4])=="half";
 if(argc>=5&&!half&&std::string(argv[4])!="full")return 2;
 std::string path=argc==6?argv[5]:"";
 U nn=std::stoull(argv[1]),KK=std::stoull(argv[2]),hh=std::stoull(argv[3]);
 if(nn>UINT32_MAX||KK>UINT32_MAX||hh>UINT32_MAX||nn+KK+3>=UINT32_MAX)return 2;
 I n=I(nn),K=I(KK),h=I(hh);if(n<14||n%2||K<=n||h<1||h>n)return 2;
 U A=U(n)+K+2,L=2*(U(n)+3*U(K)+10)+6;W prod=W(A)*L;
 auto safe=[&](U g){int64_t e=int64_t(n)-int64_t(g);return e>=126||(e>=0&&(W(6)<<e)>prod);};
 if((n<128&&A>(W(1)<<n))||!safe(0)||!safe(1))return 3;
 auto t=std::chrono::steady_clock::now();I s=1;vector<Prefix>gs={Prefix{{},(n+2)/2,3,1,1}};vector<vector<std::pair<I,I>>> layers;
 load(path,n,K,h,half,s,gs,layers);
 // A conservative bound on every internal new run: initial suffix run+h.
 // This can be very loose but is sufficient for h=n/2 and large n.
 for(;U(s)+n<=K&&!gs.empty();){
  struct Part{vector<Prefix>next;vector<I>accepted;U work=0,fw=0;size_t mids=0;};vector<Part>parts(gs.size());
  for(auto&g:gs)if(!safe(U(g.run)+h+1))throw std::runtime_error("conservative margin");
#pragma omp parallel for schedule(dynamic)
  for(int gi=0;gi<(int)gs.size();gi++){
   const auto&g=gs[gi];auto&part=parts[gi];auto y=[&](I q,unsigned k){return g.word(int64_t(q)-2*int64_t(n)-3,k,h);};
   auto mids=live(n+s+h+3,2*n+s+3,y,part.work);part.mids=mids.size();
   auto good=filter(n+s+3,n+s+h+3,y,g.carry,mids,part.fw);
   for(I a:good){Prefix g2=child(n,s,h,g,a);if(half&&s==1&&g2.blocks[0]->get(0)!=1)continue; // low appended 7B bit = (3+7*x)%2; x=0 iff bit=1
    part.next.push_back(std::move(g2));part.accepted.push_back(a);}
  }
  vector<Prefix>next;vector<std::pair<I,I>> layer;U work=0,fw=0,mid=0;I maxrun=0;
  for(I i=0;i<parts.size();i++){auto&part=parts[i];work+=part.work;fw+=part.fw;mid+=part.mids;for(auto a:part.accepted)layer.push_back({i,a});for(auto&g:part.next){maxrun=std::max(maxrun,g.run);next.push_back(std::move(g));}}
  std::cout<<"s="<<s<<" h="<<h<<" old="<<gs.size()<<" mids="<<mid<<" next="<<next.size()<<" work="<<work<<" filter="<<fw<<" run="<<maxrun<<" sec="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count()<<std::endl;
  for(auto e:layer)std::cout<<"CHILD "<<e.first<<" "<<e.second<<"\n";std::cout<<std::flush;
  layers.push_back(std::move(layer));save(path,n,K,h,half,layers);
  if(next.empty()){std::cout<<"END "<<n<<" "<<n+s<<std::endl;return 0;}s+=h;gs=std::move(next);
 }
 if(gs.empty()){std::cout<<"END "<<n<<" "<<n+s<<std::endl;return 0;}
 std::cout<<"END "<<n<<" 0"<<std::endl;return 1;
}
