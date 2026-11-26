
#define main plane_reverse_test_main
#include "plane_reverse.cpp"
#undef main
#include <memory>
#include <numeric>
#include <omp.h>
static unsigned fit(I F,I rem){
 return std::min({unsigned(rem),30u,unsigned(63-__builtin_clzll(F)-1)});
}
struct Block{
 I F,q; unsigned k; U Y,M; double inv;
 Block(I F0,I rem,U Y0=0):F(F0),q(F0-fit(F0,rem)),k(fit(F0,rem)),Y(Y0),M(U(1)<<k),inv(1.0/F){}
 bool parent(I z,I& c,U& word)const {
  U X=M*z+Y,b=U(double(X)*inv);
  if(b*F>X)--b;else if((b+1)*F<=X)++b;
  if(b*F>X||(b+1)*F<=X)b=X/F;
  for(int j=0;j<2;++j,++b)if(b<M){
   U w=U(q)*b+dw(b);if(w<=X&&X-w<q){c=I(X-w);word=b;return true;}
  }
  return false;
 }
};
static void put(Bits& a,U i,unsigned k,U v){
 v&=lowmask(k);
 U j=i>>6;unsigned s=i&63;
 a.a[j]|=v<<s;
 if(s+k>64)a.a[j+1]|=v>>(64-s);
}
static vector<I> list_bits(const Bits& a){
 vector<I> out;out.reserve(a.count());
 for(U j=0;j<a.a.size()-1;j++){
  U v=a.a[j];
  while(v){out.push_back(I(64*j+__builtin_ctzll(v)));v&=v-1;}
 }
 return out;
}
template<class Word>vector<I> live(I start,I F,Word y,U& visits,U& denseSteps){
 Bits bm(F);
 std::fill(bm.a.begin(),bm.a.end()-1,~U(0));
 if(F%64)bm.a[F/64]&=lowmask(F%64);
 I q=F;
 while(q>start&&bm.count()>q/12){
  unsigned k=std::min({unsigned(q-start),18u,unsigned(63-__builtin_clzll(q/64+1))});
  if(k<6)break;
  bm=planes(bm,k,y(q-k,k));q-=k;denseSteps+=k;
 }
 auto a=list_bits(bm);
 Bits seen(q);
 while(q>start&&!a.empty()){
  Block b(q,q-start);b.Y=y(b.q,b.k);visits+=a.size();size_t w=0;
  for(I z:a){I c;U B;if(b.parent(z,c,B)&&!seen.get(c)){seen.set(c);a[w++]=c;}}
  a.resize(w);for(I c:a)seen.a[c>>6]&=~(U(1)<<(c&63));q=b.q;
 }
 return a;
}
struct DSU {
 vector<int> p; explicit DSU(int n):p(n,-1){}
 int find(int x){int r=x;while(p[r]>=0)r=p[r];while(x!=r){int y=p[x];p[x]=r;x=y;}return r;}
 int unite(int a,int b){a=find(a);b=find(b);if(a==b)return a;if(p[a]>p[b])std::swap(a,b);p[a]+=p[b];p[b]=a;return a;}
};
struct Entry{I c;int id;};
template<class Word>vector<I> filter(I start,I F,Word y,I root,const vector<I>& ends,U&work){
 if(ends.size()>INT32_MAX)throw std::runtime_error("mid count");
 vector<Entry>a;for(int i=0;i<(int)ends.size();i++)a.push_back({ends[i],i});DSU d(a.size());
 while(F>start&&!a.empty()){
  Block b(F,F-start);b.Y=y(b.q,b.k);work+=a.size();size_t w=0;
  for(auto e:a){I c;U B;if(b.parent(e.c,c,B))a[w++]={c,e.id};}a.resize(w);
  std::sort(a.begin(),a.end(),[](Entry x,Entry y){return x.c<y.c;});
  w=0;for(auto e:a){if(w&&a[w-1].c==e.c)a[w-1].id=d.unite(a[w-1].id,e.id);else a[w++]=e;}a.resize(w);F=b.q;
 }
 auto it=std::find_if(a.begin(),a.end(),[&](Entry e){return e.c==root;});if(it==a.end())return {};
 int label=d.find(it->id);vector<I>out;
 for(int i=0;i<(int)ends.size();i++)if(d.find(i)==label)out.push_back(ends[i]);
 return out;
}
struct Prefix{
 vector<std::shared_ptr<const Bits>> blocks;
 I carry,r;
 U word(int64_t i,unsigned k,I h)const{
  U v=0;
  if(i>=1&&(U(i)-1)%h+k<=h){
   U a=U(i)-1;return blocks.at(a/h)->read(a%h)&lowmask(k);
  }
  for(unsigned j=0;j<k;j++){
   int64_t a=i+j;if(a<0)continue;if(!a){v|=U(1)<<j;continue;}
   --a;v|=U(blocks.at(U(a)/h)->get(I(U(a)%h)))<<j;
  }
  return v;
 }
};
template<class Word>Bits recover(I start,I end,Word y,I root,I endpoint){
 Bits bits(end-start);
 I c=endpoint;
 for(I F=end;F>start;){
  Block b(F,F-start);b.Y=y(b.q,b.k);U B;I p;
  if(!b.parent(c,p,B))throw std::runtime_error("invalid path");
  put(bits,b.q-start,b.k,B);F=b.q;c=p;
 }
 if(c!=root)throw std::runtime_error("root mismatch");
 return bits;
}
static std::shared_ptr<const Bits> multiply7(const Bits& bits,I& r){
 auto out=std::make_shared<Bits>(bits.n);
 for(U i=0;i<bits.n;i+=32){
  unsigned k=std::min(U(32),U(bits.n)-i);
  U B=bits.read(i)&lowmask(k);
  U v=7*B+r;put(*out,i,k,v);r=I(v>>k);
 }
 return out;
}
static void test_prefix(){
 std::mt19937_64 rng(123);
 for(I F:{100,1000,10000,100000}){
  for(unsigned k:{1,5,10,20}){
   if(k>=F)continue;
   U Y=rng()&lowmask(k);
   auto w=[&](I q,unsigned n){return (Y>>(q-(F-k)))&lowmask(n);};
   U a=0,b=0;auto got=live(F-k,F,w,a,b);
   Bits all(F);for(I i=0;i<F;i++)all.set(i);
   auto expect=list_bits(scalar(all,k,Y));
   std::sort(got.begin(),got.end());assert(got==expect);
  }
 }
 for(I n:{1,31,32,33,63,64,65,101,1000}){
  Bits bits(n);for(I i=0;i<n;i++)if(rng()&1)bits.set(i);
  for(I r0=0;r0<=6;r0++){
   I r=r0,rr=r0;auto out=multiply7(bits,r);
   for(I i=0;i<n;i++){I v=rr+7*bits.get(i);assert(out->get(i)==bool(v&1));rr=v/2;}
   assert(r==rr);
  }
 }
 // Exact block reconstruction from randomly generated broad forward walks.
 unsigned count=0;
 for(I q0=100;q0<200;q0++)for(unsigned k=1;k<=10;k++){
  U Y=rng()&lowmask(k);I c=rng()%q0,root=c;U selected=0;
  bool ok=true;
  for(unsigned i=0;i<k;i++){
   U y=(Y>>i)&1,q=q0+i;vector<std::pair<I,U>>next;
   for(U b=0;b<=1;b++){U v=c+q*b;if(v>=y&&(v-y)%2==0&&(v-y)/2<q)next.push_back({I((v-y)/2),b});}
   if(next.empty()){ok=false;break;}
   auto [z,b]=next[rng()%next.size()];c=z;selected|=b<<i;
  }
  if(!ok)continue;
  auto w=[&](I q,unsigned n){return (Y>>(q-q0))&lowmask(n);};
  auto got=recover(q0,q0+k,w,root,c);
  assert(got.read(0)==selected);++count;
 }
 std::cout<<"Prefix tests passed; "<<count<<" recovered legal words\n";
}
int main(int argc,char**argv){
 if(argc==1){test_prefix();return 0;}
 if(argc!=4)return 2;
 U nn=std::stoull(argv[1]),KK=std::stoull(argv[2]),hh=std::stoull(argv[3]);
 if(nn<14||nn%2||KK<=nn||hh<1||hh>nn||nn+KK+3>=UINT32_MAX)return 2;
 I n=I(nn),K=I(KK),h=I(hh),s=1;
 vector<Prefix> gs={{ {},(n+2)/2,3 }};
 auto clock=std::chrono::steady_clock::now();
 while(U(s)+n<=K){
  struct Part{vector<Prefix> next;U v=0,d=0,f=0,mids=0;};vector<Part>parts(gs.size());
#pragma omp parallel for schedule(dynamic)
  for(int gi=0;gi<(int)gs.size();gi++){
   auto&g=gs[gi];auto&p=parts[gi];auto y=[&](I q,unsigned k){return g.word(int64_t(q)-(2*int64_t(n)+3),k,h);};
   auto mids=live(n+s+h+3,2*n+s+3,y,p.v,p.d);p.mids=mids.size();
   auto good=filter(n+s+3,n+s+h+3,y,g.carry,mids,p.f);
   for(I a:good){
    auto extra=recover(n+s+3,n+s+h+3,y,g.carry,a);
    if(s==1&&extra.get(0))continue; // canonical half (Agent43)
    Prefix next=g;next.carry=a;next.blocks.push_back(multiply7(extra,next.r));p.next.push_back(std::move(next));
   }
  }
  vector<Prefix> next;U v=0,d=0,f=0,m=0;
  for(auto&p:parts){v+=p.v;d+=p.d;f+=p.f;m+=p.mids;for(auto&g:p.next)next.push_back(std::move(g));}
  std::cout<<"s="<<s<<" h="<<h<<" old="<<gs.size()<<" mids="<<m<<" next="<<next.size()<<" dense_steps="<<d<<" visits="<<v<<" filter="<<f<<" sec="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-clock).count()<<std::endl;
  if(next.empty()){std::cout<<"END "<<n<<" "<<n+s<<std::endl;return 0;}
  s+=h;gs=std::move(next);
 }
 std::cout<<"END "<<n<<" 0"<<std::endl;return 1;
}
