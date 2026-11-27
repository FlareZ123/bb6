// Fixed-width continuation of Agent43 fastprefix.cpp (blob e96bdaa1870a4770f0f773c0cccac739e160570f).
// The future query window is [s-n,s); discard earlier product blocks.
// Old P1C1 checkpoints are imported by skipping obsolete blocks; P1C2 stores only retained blocks.
// Numerical experiment: checkpoints are not completeness certificates.
// Exact broad carry sweep with AVX512 fitted queries and packed target words.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <climits>
#include <vector>
#include <immintrin.h>
#include <omp.h>
#include "wide_jump.hpp"
#include "wide_reverse.hpp"

using U=uint64_t; using I=uint32_t; using W=__uint128_t;
constexpr I missing=UINT32_MAX;
using std::vector;
static inline U mask(unsigned k){return k==64?~U(0):(U(1)<<k)-1;}
using bb6_shifted::Block;
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
 I first=0; // absolute index of blocks[0], counting from product bit 1
 U word(int64_t i,unsigned k,I h)const {
  U v=0;unsigned out=0;
  if(i<0){auto gap=std::min<int64_t>(k,-i);i+=gap;out+=gap;}
  if(out<k&&i==0){v|=U(1)<<out;++i;++out;}
  while(out<k){U off=U(i-1);I j=off/h,p=off%h;unsigned t=std::min<unsigned>(k-out,h-p);if(j<first)throw std::runtime_error("discarded target");v|=blocks.at(j-first)->read(p,t)<<out;out+=t;i+=t;}
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
using bb6_shifted::Block8;
using bb6_shifted::Block16;
#endif
// Deduplication at the boundary of a composed partial function is exact:
// duplicate intermediate carries have identical remaining paths.
// A labelled intermediate union is needed only if its path survives.
static unsigned fusion_limit=1;
template<class Word>vector<Block> make_pipe(I F,I start,const Word& y,unsigned limit){
 vector<Block> bs;bs.reserve(limit);
 while(F>start&&bs.size()<limit){bs.emplace_back(F,F-start);auto& b=bs.back();b.Y=y(b.q,b.k);F=b.q;}
 return bs;
}
template<class T,class Get,class Put>size_t apply_pipe(vector<T>& a,const vector<Block>& bs,Get get,Put put,U&work){
 size_t j=0,w=0;
#if defined(__AVX512F__) && defined(__AVX512DQ__) && defined(__AVX512VL__)
 if(bb6_shifted::fit_mode==7&&bs.front().F<=INT32_MAX&&a.size()>=16){
  vector<Block16> simd;simd.reserve(bs.size());for(auto& b:bs)simd.emplace_back(b);
  for(;j+16<=a.size();j+=16){
   T saved[16];I in[16];for(unsigned k=0;k<16;k++){saved[k]=a[j+k];in[k]=get(saved[k]);}
   auto z=_mm512_loadu_si512(in);__mmask16 active=65535;
   for(auto& b:simd){
    work+=__builtin_popcount(unsigned(active));z=b.parent_vec(z,active);
    active=_mm512_cmp_epu32_mask(z,_mm512_set1_epi32(missing),_MM_CMPINT_NE);
    if(!active)break;
   }
   I out[16];_mm512_storeu_si512(out,z);
   for(unsigned k=0;k<16;k++)if(out[k]!=missing&&put(saved[k],out[k]))a[w++]=saved[k];
  }
 }else if(a.size()>=8){
  vector<Block8> simd;simd.reserve(bs.size());for(auto& b:bs)simd.emplace_back(b);
  for(;j+8<=a.size();j+=8){
   T saved[8];I in[8];for(unsigned k=0;k<8;k++){saved[k]=a[j+k];in[k]=get(saved[k]);}
   auto z=_mm512_cvtepu32_epi64(_mm256_loadu_si256((const __m256i*)in));
   __mmask8 active=255;
   for(auto& b:simd){
    work+=__builtin_popcount(unsigned(active));z=b.parent_vec(z,active);
    active=_mm512_cmp_epu64_mask(z,_mm512_set1_epi64(missing),_MM_CMPINT_NE);
    if(!active)break;
   }
   I out[8];_mm256_storeu_si256((__m256i*)out,_mm512_cvtepi64_epi32(z));
   for(unsigned k=0;k<8;k++)if(out[k]!=missing&&put(saved[k],out[k]))a[w++]=saved[k];
  }
 }
#endif
 for(;j<a.size();j++){
  T e=a[j];I c=get(e);
  for(auto&b:bs){++work;c=b.parent(c);if(c==missing)break;}
  if(c!=missing&&put(e,c))a[w++]=e;
 }
 return w;
}
static unsigned jump_limit=22;
// Reuse the exact target-independent modular support across all prefixes
// of a stage. Only the cyclic translation by each target Y changes.
template<class Word>vector<I> live_with_plan(I start,I F,Word y,U&work,const bb6_jump::Plan& plan){
 I r=I(plan.r),q=I(plan.q);if(U(q)+r!=F||q<start)throw std::runtime_error("jump plan clock");
 vector<I>a;
 a.reserve(std::min(U(q),U(plan.residues.size())*((U(q)+plan.modulus-1)/plan.modulus)));
 plan.lift(y(q,r),[&](I c){a.push_back(I(c));});
 Seen seen(q);
 while(q>start&&!a.empty()){
  // Dense early images dedup more frequently; sparse late images are fused.
  unsigned lim=std::min(fusion_limit,std::max(1u,(F-q)/128u));
  auto bs=make_pipe(q,start,y,lim);
  auto w=apply_pipe(a,bs,[](I e){return e;},[&](I& e,I c){e=c;return seen.insert(c);},work);
  a.resize(w);for(I c:a)seen.clear(c);q=bs.back().q;
 }
 return a;
}
template<class Word>vector<I> live(I start,I F,Word y,U&work){
 I r=std::min(I(jump_limit),F-start);
 bb6_jump::Plan plan(F-r,int(r));
 return live_with_plan(start,F,y,work,plan);
}
template<class Word>vector<I> filter(I start,I F,Word y,I root,const vector<I>&ends,U&work){
 if(ends.size()>INT_MAX)throw std::runtime_error("mid count");
 vector<Entry>a;a.reserve(ends.size());for(int i=0;i<(int)ends.size();i++)a.push_back({ends[i],i});DSU d(a.size());
 while(F>start&&!a.empty()){
  auto bs=make_pipe(F,start,y,fusion_limit);
  auto w=apply_pipe(a,bs,[](Entry e){return e.c;},[](Entry& e,I c){e.c=c;return true;},work);a.resize(w);
  if(a.size()>1)std::sort(a.begin(),a.end(),[](Entry x,Entry y){return x.c<y.c;});w=0;
  for(auto e:a){if(w&&a[w-1].c==e.c)a[w-1].id=d.unite(a[w-1].id,e.id);else a[w++]=e;}a.resize(w);F=bs.back().q;
 }
 auto it=std::find_if(a.begin(),a.end(),[&](Entry e){return e.c==root;});if(it==a.end())return {};
 int label=d.find(it->id);vector<I>out;
 for(int i=0;i<(int)ends.size();i++)if(d.find(i)==label)out.push_back(ends[i]);std::sort(out.begin(),out.end());return out;
}
// Reconstruct a chosen child from its endpoint. The fixed h-step word is
// unique for a given upper endpoint. Every block is exactly checked.
static I keep_blocks(I n,I h){return I((U(n)+h-1)/h);}
static Prefix child(I n,I s,I h,const Prefix& g,I a){
 auto y=[&](I q,unsigned k){return g.word(int64_t(q)-2*int64_t(n)-3,k,h);};
 I start=n+s+3,F=start+h,c=a;Bits extra(h);
 while(F>start){Block b(F,F-start);b.Y=y(b.q,b.k);U code=0;c=b.parent(c,&code);if(c==missing)throw std::runtime_error("rewind");extra.put(b.q-start,b.k,code);F=b.q;}
 if(c!=g.carry)throw std::runtime_error("root");
 Prefix g2=g;g2.carry=a;auto appended=std::make_shared<Bits>(h);
 for(U j=0;j<h;j+=64){unsigned t=std::min<U>(64,U(h)-j);W v=W(7)*extra.read(I(j),t)+g2.r;g2.r=I(v>>t);appended->a[j/64]=U(v)&mask(t);}
 g2.blocks.push_back(appended);g2.last=appended->get(h-1);g2.run=0;for(I j=h;j>0&&appended->get(j-1)==g2.last;--j)++g2.run;if(g2.run==h&&g.last==g2.last)g2.run+=g.run;
 const I keep=keep_blocks(n,h);
 if(g2.blocks.size()>keep){I drop=I(g2.blocks.size()-keep);g2.blocks.erase(g2.blocks.begin(),g2.blocks.begin()+drop);g2.first+=drop;}
 return g2;
}
// Binary P1C2 uses the P1C1 eight-word header and four-word prefix metadata.
// Words are little-endian uint32_t, as in the archived x86-64 P1C1 run.
// Each retained block has ceil(h/64) uint64_t words, excluding the sentinel.
static constexpr I old_magic=0x50314331,new_magic=0x50314332;
static void save(const std::string& path,I n,I K,I h,bool half,I s,I gap,const vector<Prefix>&gs){
 if(path.empty())return;
 std::ofstream f(path+".tmp",std::ios::binary|std::ios::trunc);
 auto put=[&](I x){f.write(reinterpret_cast<const char*>(&x),sizeof x);};
 I total=(s-1)/h,keep=std::min(total,keep_blocks(n,h));
 U words=(U(h)+63)/64;
 put(new_magic);put(n);put(K);put(h);put(half);put(s);put(gap);put(I(gs.size()));
 for(const auto&g:gs){
  if(g.first!=total-keep||g.blocks.size()!=keep)throw std::runtime_error("checkpoint window");
  put(g.carry);put(g.r);put(g.last);put(g.run);
  for(auto&b:g.blocks)f.write(reinterpret_cast<const char*>(b->a.data()),words*sizeof(U));
 }
 f.close();if(!f||std::rename((path+".tmp").c_str(),path.c_str()))throw std::runtime_error("checkpoint write");
}
static void load(const std::string& path,I n,I K,I h,bool half,I&s,I&gap,vector<Prefix>&gs){
 if(path.empty())return;
 std::ifstream f(path,std::ios::binary);if(!f)return;
 auto get=[&](){I x=0;f.read(reinterpret_cast<char*>(&x),sizeof x);if(!f)throw std::runtime_error("checkpoint read");return x;};
 I magic=get(),nn=get(),oldK=get(),hh=get(),ha=get();
 if((magic!=old_magic&&magic!=new_magic)||nn!=n||oldK>K||hh!=h||ha!=I(half))throw std::runtime_error("checkpoint parameters");
 s=get();gap=get();I count=get();
 if(s<1||(s-1)%h||U(s)+n>K||count<1||gap<1)throw std::runtime_error("checkpoint state");
 I total=(s-1)/h,keep=std::min(total,keep_blocks(n,h)),stored=magic==old_magic?total:keep;
 U words=(U(h)+63)/64,block_bytes=words*sizeof(U);
 W expected=W(32)+W(count)*(16+W(stored)*block_bytes);
 f.seekg(0,std::ios::end);auto length=f.tellg();
 if(length<0||W(length)!=expected)throw std::runtime_error("checkpoint length");
 f.seekg(32,std::ios::beg);gs.clear();
 for(I j=0;j<count;j++){
  Prefix g;g.carry=get();g.r=get();g.last=get();g.run=get();g.first=total-keep;
  if(U(g.carry)>=U(n)+s+3||g.r>6||g.last>1||g.run<1||g.run>s)throw std::runtime_error("checkpoint prefix metadata");
  f.seekg(std::streamoff(U(stored-keep)*block_bytes),std::ios::cur);
  for(I i=0;i<keep;i++){
   auto b=std::make_shared<Bits>(h);f.read(reinterpret_cast<char*>(b->a.data()),block_bytes);
   if(!f)throw std::runtime_error("checkpoint block");
   if(h%64&&(b->a[words-1]&~mask(h%64)))throw std::runtime_error("checkpoint padding");
   g.blocks.push_back(std::move(b));
  }
  if(g.word(s-1,1,h)!=g.last)throw std::runtime_error("checkpoint final bit");
  gs.push_back(std::move(g));
 }
 std::cout<<"RESUME s="<<s<<" count="<<count<<" retained="<<keep<<" legacy="<<(magic==old_magic)<<" gap="<<gap<<std::endl;
}
int main(int argc,char**argv){
 if(argc<4||argc>6)return 2;
 bb6_shifted::fit_mode=7; // wide eight-lane fallback above INT32_MAX
 if(auto p=std::getenv("P1_FIT")){auto x=std::stoul(p);if(x!=6&&x!=7)return 2;bb6_shifted::fit_mode=unsigned(x);}
 if(auto p=std::getenv("P1_JUMP")){auto x=std::stoul(p);if(x>30)return 2;jump_limit=unsigned(x);}
 if(auto p=std::getenv("P1_FUSE")){auto x=std::stoul(p);if(x<1||x>256)return 2;fusion_limit=unsigned(x);}
 if(auto p=std::getenv("P1_PLAN")){auto x=std::stoul(p);if(x>1)return 2;bb6_jump::bitmap_plan=bool(x);}
 bool half=argc>=5&&std::string(argv[4])=="half";
 if(argc>=5&&!half&&std::string(argv[4])!="full")return 2;
 std::string path=argc==6?argv[5]:"";
 U nn=std::stoull(argv[1]),KK=std::stoull(argv[2]),hh=std::stoull(argv[3]);
 if(nn>UINT32_MAX||KK>UINT32_MAX||hh>UINT32_MAX||nn+KK+3>=UINT32_MAX)return 2;
 I n=I(nn),K=I(KK),h=I(hh);if(n<14||n%2||K<=n||h<1||h>n)return 2;
 U A=U(n)+K+2,L=2*(U(n)+3*U(K)+10)+6;W prod=W(A)*L;
 auto safe=[&](U g){int64_t e=int64_t(n)-int64_t(g);return e>=126||(e>=0&&(W(6)<<e)>prod);};
 if((n<128&&A>(W(1)<<n))||!safe(0)||!safe(1))return 3;
 auto t=std::chrono::steady_clock::now();I s=1,maxgap=1;vector<Prefix>gs={Prefix{{},(n+2)/2,3,1,1}};
 load(path,n,K,h,half,s,maxgap,gs);
 if(!safe(maxgap))throw std::runtime_error("historical margin at requested K");
 // A conservative bound on every internal new run: initial suffix run+h.
 // This can be very loose but is sufficient for h=n/2 and large n.
 for(;U(s)+n<=K&&!gs.empty();){
  struct Part{vector<Prefix>next;vector<I>accepted;U work=0,fw=0;size_t mids=0;};vector<Part>parts(gs.size());
  for(auto&g:gs){U bound=U(g.run)+h+1;if(!safe(bound))throw std::runtime_error("conservative margin");maxgap=std::max(maxgap,I(bound));}
  I end=2*n+s+3,jump=std::min(I(jump_limit),n-h);
  std::unique_ptr<bb6_jump::Plan> plan;
  plan=std::make_unique<bb6_jump::Plan>(end-jump,int(jump));
#pragma omp parallel for schedule(dynamic)
  for(int gi=0;gi<(int)gs.size();gi++){
   const auto&g=gs[gi];auto&part=parts[gi];auto y=[&](I q,unsigned k){return g.word(int64_t(q)-2*int64_t(n)-3,k,h);};
   auto mids=live_with_plan(n+s+h+3,end,y,part.work,*plan);part.mids=mids.size();
   auto good=filter(n+s+3,n+s+h+3,y,g.carry,mids,part.fw);
   for(I a:good){Prefix g2=child(n,s,h,g,a);if(half&&s==1&&g2.blocks[0]->get(0)!=1)continue; // low appended 7B bit = (3+7*x)%2; x=0 iff bit=1
    part.next.push_back(std::move(g2));part.accepted.push_back(a);}
  }
  vector<Prefix>next;vector<std::pair<I,I>> layer;U work=0,fw=0,mid=0;I maxrun=0;
  for(I i=0;i<parts.size();i++){auto&part=parts[i];work+=part.work;fw+=part.fw;mid+=part.mids;for(auto a:part.accepted)layer.push_back({i,a});for(auto&g:part.next){maxrun=std::max(maxrun,g.run);next.push_back(std::move(g));}}
  std::cout<<"s="<<s<<" h="<<h<<" old="<<gs.size()<<" mids="<<mid<<" next="<<next.size()<<" work="<<work<<" filter="<<fw<<" run="<<maxrun<<" gapBound="<<maxgap<<" fit="<<bb6_shifted::fit_mode<<" fuse="<<fusion_limit<<" sec="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count()<<std::endl;
  for(auto e:layer)std::cout<<"CHILD "<<e.first<<" "<<e.second<<"\n";std::cout<<std::flush;
  if(next.empty()){std::cout<<"END "<<n<<" "<<n+s<<std::endl;return 0;}
  s+=h;gs=std::move(next);save(path,n,K,h,half,s,maxgap,gs);
 }
 if(gs.empty()){std::cout<<"END "<<n<<" "<<n+s<<std::endl;return 0;}
 std::cout<<"END "<<n<<" 0"<<std::endl;return 1;
}
