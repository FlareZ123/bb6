
#define BB6_PLANE_PREFIX_LIBRARY
#include "plane_prefix.cpp"
#include "plane_sparse_simd.hpp"
#include <fstream>
#include <cstdio>
using W=__uint128_t;
template<class Word>vector<I> fast_live(I start,I F,Word y,U& visits,U& denseSteps){
 Bits bm(F);
 std::fill(bm.a.begin(),bm.a.end()-1,~U(0));
 if(F%64)bm.a[F/64]&=lowmask(F%64);
 I q=F;
 while(q>start&&bm.count()>q/12){
  unsigned k=std::min({unsigned(q-start),18u,unsigned(63-__builtin_clzll(q/64+1))});
  if(k<6)break;
  bm=planes(bm,k,y(q-k,k));q-=k;denseSteps+=k;
 }
 auto a=list_bits(bm);Bits seen(q);
 while(q>start&&!a.empty()){
  Block b(q,q-start);b.Y=y(b.q,b.k);visits+=a.size();simd_reverse(a,b,seen);q=b.q;
 }
 return a;
}
// Distinct parents cannot merge: each legal z has the unique predecessor
// (2z+y)%q. A capped probe is never interpreted as extinction.
template<class Word>bool forward_probe(I start,I end,Word y,I root,U budget,vector<I>& endpoints,U& visits){
 vector<I> a{root},b;
 for(I q=start;q<end&&!a.empty();q++){
  if(a.size()>budget-visits)return false;
  visits+=a.size();
  I v=I(y(q,1));
  b.clear();b.reserve(a.size()*(q%2?1:2));
  for(I c:a){
   if((c%2)==v)b.push_back((c-v)/2);
   if(((c+U(q))%2)==v)b.push_back(I((c+U(q)-v)/2));
  }
  a.swap(b);
 }
 endpoints=std::move(a);return true;
}
template<class Word>vector<I> rewind_set(I start,I end,Word y,vector<I> a){
 Bits seen(end);
 while(end>start&&!a.empty()){
  Block b(end,end-start);b.Y=y(b.q,b.k);simd_reverse(a,b,seen);end=b.q;
 }
 return a;
}
static I loss(const Prefix& g,I s,I h){
 U last=g.word(s-1,1,h);I run=0;
 while(run<s){
  unsigned k=std::min(I(64),s-run);
  U v=g.word(s-run-k,k,h),diff=(last?~v:v)&lowmask(k);
  if(diff)return run+k-(64-__builtin_clzll(diff))+1;
  run+=k;
 }
 return s;
}
// resMin(s,B) >= 2^(s-loss). Monotonicity under extension
// supplies every intermediate margin through s+h.
static bool margin(I n,I K,I h,I ell){
 W a=W(n)+K+2,L=2*(W(n)+3*W(K)+10)+6,prod=a*L;
 int64_t e=int64_t(n)-h-ell;
 return e>=126||(e>=0&&(W(6)<<e)>prod);
}
struct Stage {I s;vector<std::pair<I,I>> mids;};
static Prefix child(const Prefix& g,I n,I s,I h,I a){
 auto y=[&](I q,unsigned k){return g.word(int64_t(q)-(2*int64_t(n)+3),k,h);};
 auto extra=recover(n+s+3,n+s+h+3,y,g.carry,a);
 if(s==1&&extra.get(0))throw std::runtime_error("noncanonical checkpoint");
 Prefix next=g;next.carry=a;next.blocks.push_back(multiply7(extra,next.r));return next;
}
static void save(const std::string& path,I n,I h,const vector<Stage>& stages){
 if(path.empty())return;
 std::ofstream f(path+".tmp");
 f<<"P1PLANE 1 "<<n<<" "<<h<<"\n";
 for(auto& t:stages){
  f<<"stage "<<t.s<<" "<<t.mids.size()<<"\n";
  for(auto [parent,mid]:t.mids)f<<parent<<" "<<mid<<"\n";
 }
 f.close();
 if(!f||std::rename((path+".tmp").c_str(),path.c_str()))throw std::runtime_error("checkpoint write");
}
static bool load(const std::string& path,I n,I K,I h,I& s,vector<Prefix>& gs,vector<Stage>& stages){
 if(path.empty())return false;
 std::ifstream f(path);if(!f)return false;
 std::string tag;I v,nn,hh;
 if(!(f>>tag>>v>>nn>>hh)||tag!="P1PLANE"||v!=1||nn!=n||hh!=h)throw std::runtime_error("checkpoint header");
 while(f>>tag){
  I st,count;
  if(tag!="stage"||!(f>>st>>count)||st!=s||U(s)+n>K||count>INT32_MAX)throw std::runtime_error("checkpoint stage");
  for(auto&g:gs)if(!margin(n,K,h,loss(g,s,h)))throw std::runtime_error("checkpoint margin");
  Stage rec{s,{}};vector<Prefix> next;
  for(I i=0;i<count;i++){
   I par,mid;
   if(!(f>>par>>mid)||par>=gs.size()||mid>=U(n)+s+h+3)throw std::runtime_error("checkpoint child");
   rec.mids.emplace_back(par,mid);next.push_back(child(gs[par],n,s,h,mid));
  }
  stages.push_back(std::move(rec));
  if(next.empty()){
   if(f>>tag)throw std::runtime_error("data after terminal stage");
   std::cout<<"RESUME empty s="<<s<<std::endl;return true;
  }
  s+=h;gs=std::move(next);
 }
 if(!f.eof())throw std::runtime_error("checkpoint parse");
 std::cout<<"RESUME s="<<s<<" count="<<gs.size()<<std::endl;return false;
}
static void test_v2(){
 test_prefix();
 std::mt19937_64 rng(20261126);
 for(I n:{32,100,1024,4096}){
  for(unsigned k:{1,5,10,20}){
   U Y=rng()&lowmask(k);I root=rng()%n;
   auto y=[&](I q,unsigned j){return (Y>>(q-n))&lowmask(j);};
   U v=0;vector<I>a;
   assert(forward_probe(n,n+k,y,root,10000000,a,v));
   std::sort(a.begin(),a.end());
   vector<I> b;for(I z=0;z<n+k;z++){
    auto got=rewind_set(n,n+k,y,{z});
    if(got.size()&&got[0]==root)b.push_back(z);
   }
   assert(a==b);
   U d=0;v=0;auto live=fast_live(n,n+k,y,v,d);
   Bits all(n+k);for(I i=0;i<n+k;i++)all.set(i);
   auto expect=list_bits(scalar(all,k,Y));std::sort(live.begin(),live.end());assert(live==expect);
  }
 }
 // Test exact loss lower bound on all odd residues up to length 12.
 U checked=0;
 for(I s=1;s<=12;s++)for(I R=1;R<(1u<<s);R+=2){
  auto a=std::make_shared<Bits>(s>1?s-1:1);for(I i=1;i<s;i++)if((R>>i)&1)a->set(i-1);
  Prefix g{{},0,0};if(s>1)g.blocks.push_back(a);
  I ell=loss(g,s,s>1?s-1:1);
  U bound=U(1)<<(s-ell);assert(bound<=R&&bound<=(U(1)<<s)-R);checked++;
 }
 std::cout<<"Probe/reverse comparisons and "<<checked<<" exact residue loss checks passed\n";
}
int main(int argc,char**argv){
 if(argc==1){test_v2();return 0;}
 if(argc<4||argc>6)return 2;
 U nn=std::stoull(argv[1]),KK=std::stoull(argv[2]),hh=std::stoull(argv[3]),budget=argc>=5?std::stoull(argv[4]):10000000;
 std::string path=argc==6?argv[5]:"";
 if(nn<14||nn%2||KK<=nn||hh<1||hh>nn||nn+KK+3>=UINT32_MAX)return 2;
 I n=I(nn),K=I(KK),h=I(hh),s=1;
 if((n<128&&W(n)+K+2>(W(1)<<n))||!margin(n,K,0,0))return 3;
 vector<Prefix> gs={{ {},(n+2)/2,3 }};vector<Stage> stages;
 if(load(path,n,K,h,s,gs,stages)){std::cout<<"END "<<n<<" "<<n+s<<std::endl;return 0;}
 auto clock=std::chrono::steady_clock::now();
 while(U(s)+n<=K){
  I maxloss=0;for(auto&g:gs)maxloss=std::max(maxloss,loss(g,s,h));
  if(!margin(n,K,h,maxloss)){std::cout<<"MARGIN_STOP s="<<s<<" loss="<<maxloss<<std::endl;return 3;}
  struct Part{vector<Prefix> next;vector<I> midsKept;U v=0,d=0,f=0,mids=0,probe=0,complete=0;};vector<Part>parts(gs.size());
#pragma omp parallel for schedule(dynamic)
  for(int gi=0;gi<(int)gs.size();gi++){
   auto&g=gs[gi];auto&part=parts[gi];auto y=[&](I q,unsigned k){return g.word(int64_t(q)-(2*int64_t(n)+3),k,h);};
   vector<I> good,term;
   if(forward_probe(n+s+3,2*n+s+3,y,g.carry,budget,term,part.probe)){
    part.complete=1;
    good=rewind_set(n+s+h+3,2*n+s+3,y,std::move(term));
    part.mids=good.size();
   }else{
    auto mids=fast_live(n+s+h+3,2*n+s+3,y,part.v,part.d);part.mids=mids.size();
    good=filter(n+s+3,n+s+h+3,y,g.carry,mids,part.f);
   }
   std::sort(good.begin(),good.end());
   for(I a:good){
    auto extra=recover(n+s+3,n+s+h+3,y,g.carry,a);
    if(s==1&&extra.get(0))continue;
    Prefix next=g;next.carry=a;next.blocks.push_back(multiply7(extra,next.r));part.next.push_back(std::move(next));part.midsKept.push_back(a);
   }
  }
  vector<Prefix> next;Stage rec{s,{}};U v=0,d=0,f=0,m=0,pv=0,cp=0;
  for(I gi=0;gi<parts.size();gi++){auto&part=parts[gi];v+=part.v;d+=part.d;f+=part.f;m+=part.mids;pv+=part.probe;cp+=part.complete;for(I a:part.midsKept)rec.mids.emplace_back(gi,a);for(auto&g:part.next)next.push_back(std::move(g));}
  std::cout<<"s="<<s<<" h="<<h<<" old="<<gs.size()<<" mids="<<m<<" next="<<next.size()<<" dense_steps="<<d<<" visits="<<v<<" filter="<<f<<" probe="<<pv<<" probe_complete="<<cp<<" loss="<<maxloss<<" sec="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-clock).count()<<std::endl;
  stages.push_back(std::move(rec));save(path,n,h,stages);
  if(next.empty()){std::cout<<"END "<<n<<" "<<n+s<<std::endl;return 0;}
  s+=h;gs=std::move(next);
 }
 std::cout<<"END "<<n<<" 0"<<std::endl;return 1;
}
