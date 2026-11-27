#include <random>
#define main birthloc_sparse_main
#include "birthloc.cpp"
#undef main
static inline U lowmask(unsigned n){return n==64?~U(0):(U(1)<<n)-1;}
struct Bitmap{
 I n;vector<U> a;
 explicit Bitmap(I n0):n(n0),a((U(n)+63)/64+1){}
 void set(I i){a[i>>6]|=U(1)<<(i&63);}
 bool get(I i)const{return (a[i>>6]>>(i&63))&1;}
 U read(U i)const{U j=i>>6;unsigned s=i&63;if(j>=a.size()-1)return 0;return s?(a[j]>>s)|(a[j+1]<<(64-s)):a[j];}
 U count()const{U n=0;for(U w:a)n+=__builtin_popcountll(w);return n;}
 void trim(){if(n%64)a[n/64]&=lowmask(n%64);a.back()=0;}
};
static inline U rev(U a){a=((a>>1)&0x5555555555555555ULL)|((a&0x5555555555555555ULL)<<1);a=((a>>2)&0x3333333333333333ULL)|((a&0x3333333333333333ULL)<<2);a=((a>>4)&0x0f0f0f0f0f0f0f0fULL)|((a&0x0f0f0f0f0f0f0f0fULL)<<4);return __builtin_bswap64(a);}
static void transpose(U* a){
 constexpr U masks[]={0x5555555555555555ull,0x3333333333333333ull,0x0f0f0f0f0f0f0f0full,0x00ff00ff00ff00ffull,0x0000ffff0000ffffull,0x00000000ffffffffull};
 for(unsigned h=0;h<6;h++){unsigned s=1u<<h;U m=masks[h];for(unsigned i=0;i<64;i+=2*s)for(unsigned j=i;j<i+s;j++){U t=((a[j]>>s)^a[j+s])&m;a[j]^=t<<s;a[j+s]^=t;}}
}
// Copy n bits from an arbitrary source offset to lane offset dest, ORing
// only the selected bits. The final guard word is zero on entry.
static void copy_bits(U* lane,U dest,const Bitmap& src,U pos,U n){
 U j=dest>>6;unsigned d=dest&63;
 for(U i=0;i<n;i+=64,++j){unsigned len=std::min(U(64),n-i);U bits=src.read(pos+i)&lowmask(len);lane[j]|=bits<<d;if(d&&len>64-d)lane[j+1]|=bits>>(64-d);}
}
// Exact enumeration of set bits in a skipped interval. Gaps are disjoint.
template<class Record>static void gap(const Bitmap& ends,U lo,U hi,I F,unsigned k,Record record,U& probes,U& failures){
 if(lo>hi)return;
 for(U a=lo;a<=hi;a+=64){U v=ends.read(a)&lowmask(std::min(U(64),hi-a+1));while(v){I z=I(a+__builtin_ctzll(v));v&=v-1;++failures;record(birth_clock(F,k,z,probes));}}
}
// All legal endpoints are partitioned into ordered disjoint intervals, one
// per selected word B, because W(B+1)-W(B)>=q. Map the live bits in each
// interval into a residue lane, and emit only the live bits in the gaps.
template<class Record>static Bitmap dense_parent(const Bitmap& ends,I F,unsigned k,Record record,U& probes,U& failures){
 U M=U(1)<<k,q=F-k,topF=(F-2)/2,topQ=(q-2)/2;
 if(k<6||k>20||2*M>F||q<128||ends.n!=topF+1)throw std::runtime_error("dense parameters");
 U rows=(q+M-1)/M,stride=(rows+63)/64+1;vector<U> lane(M*stride);
 U cursor=1;
 for(U B=0;B<M;B++){
  U W=q*B+dw(B),first=W/M+1,last=std::min((W+q-3)/M,topF);
  if(first>topF)break;
  if(first>last)continue;
  if(first<cursor)throw std::runtime_error("overlapping interval");
  gap(ends,cursor,first-1,F,k,record,probes,failures);
  U c0=M*first-W;
  copy_bits(lane.data()+(c0%M)*stride,c0/M,ends,first,last-first+1);
  cursor=last+1;
 }
 gap(ends,cursor,topF,F,k,record,probes,failures);
 Bitmap raw{I(q)};
 for(U b=0;b<stride-1;b++)for(U r=0;r<M;r+=64){U a[64];for(U i=0;i<64;i++)a[i]=lane[(r+i)*stride+b];transpose(a);for(U i=0;i<64&&64*b+i<rows;i++){U off=(64*b+i)*(M/64)+r/64;if(off<raw.a.size()-1)raw.a[off]=a[i];}}
 raw.trim();Bitmap ans{I(topQ+1)};
 for(U i=0;i<ans.a.size()-1;i++){U lo=64*i;ans.a[i]=raw.read(lo)|rev(raw.read(q-2-lo-63));}
 ans.trim();ans.a[0]&=~U(1);return ans;
}
static vector<I> list_bits(const Bitmap& bm){vector<I>a;a.reserve(bm.count());for(U w=0;w+1<bm.a.size();w++){U v=bm.a[w];while(v){a.push_back(I(64*w+__builtin_ctzll(v)));v&=v-1;}}return a;}
static Bitmap jump_bitmap(I q,unsigned r){I M=I(1)<<r,mask=M-1;Seen seen(M);vector<I>rs{0};seen.insert(0);for(unsigned j=0;j<r;j++){I shift=I((U(q+j)<<j)&mask),count=rs.size();for(I i=0;i<count;i++){I x=(rs[i]-shift)&mask;if(seen.insert(x))rs.push_back(x);}}Bitmap out((q-2)/2+1);for(U base=0;base<out.n;base+=M)for(I x:rs){U c=base+x;if(c&&c<out.n)out.set(I(c));}return out;}
static vector<I> dense_run(I L,I R,unsigned r,I F,unsigned cap,bool verbose,unsigned density=24){
 if(L<14||L>R||U(R)+4>F||F>U(2)*L+3||F>=4000000000U||r>26||!cap||cap>29||!density)throw std::runtime_error("arguments");r=std::min<unsigned>(r,F-(R+4));I q=F-r;auto t=std::chrono::steady_clock::now();auto bm=jump_bitmap(q,r);vector<I> hits;U visits=0,probes=0,failures=0,blocks=0,dense=0,denseClocks=0,cnt=bm.count();
 if(verbose)cout<<"F="<<F<<" q="<<q<<" jump="<<r<<" folded initial="<<cnt<<endl;
 auto record=[&](I b){if(b%2==0&&L+4<=b&&b<=R+4)hits.push_back(b-4);};
 while(q>L+4&&cnt>q/density){unsigned k=min({cap,unsigned(q-(L+4)),18u,unsigned(63-__builtin_clzll(q/64+1))});if(k<6||q-k<128)break;bm=dense_parent(bm,q,k,record,probes,failures);q-=k;cnt=bm.count();++dense;denseClocks+=k;}
 if(verbose)cout<<"dense blocks="<<dense<<" clocks="<<denseClocks<<" q="<<q<<" live="<<cnt<<" sec="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count()<<endl;
 auto a=list_bits(bm);bm=Bitmap(0);Seen next((q-2)/2+1);
 while(q>L+4&&!a.empty()){unsigned k=min({cap,unsigned(q-(L+4)),unsigned(63-__builtin_clzll(q)-1)});I p=q-k;Block block(q,k);visits+=a.size();size_t w=0;for(I z:a){I c=block.parent(z);if(c){if(next.insert(c))a[w++]=c;}else{++failures;record(birth_clock(q,k,z,probes));}}a.resize(w);for(I c:a)next.clear(c);q=p;++blocks;}
 if(q==L+4&&find(a.begin(),a.end(),(q-2)/2)!=a.end())record(q);
 sort(hits.begin(),hits.end());hits.erase(unique(hits.begin(),hits.end()),hits.end());if(verbose){cout<<"interval "<<L<<".."<<R<<" visits="<<visits<<" locate_probes="<<probes<<" failed_blocks="<<failures<<" sparse_blocks="<<blocks<<" hits="<<hits.size()<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count()<<endl;for(I n:hits)cout<<n<<" ";cout<<endl;}return hits;
}
static void dense_test(){
 std::mt19937_64 rng(20261127);unsigned cases=0;for(I F:{257,258,259,511,512,513,1023,1024,1025,8191,8192,8193,100000,100001})for(unsigned k=6;k<=12&&(2ull<<k)<=F;k++)for(unsigned t=0;t<8;t++){
  Bitmap a((F-2)/2+1),expect((F-k-2)/2+1);vector<I> x,y;U p=0,f=0,sp=0,sf=0;Block b(F,k);for(I z=1;z<a.n;z++)if(t==0||rng()%8<t){a.set(z);I c=b.parent(z);if(c)expect.set(c);else{++sf;y.push_back(birth_clock(F,k,z,sp));}}
  auto got=dense_parent(a,F,k,[&](I b){x.push_back(b);},p,f);sort(x.begin(),x.end());sort(y.begin(),y.end());if(got.a!=expect.a||x!=y||f!=sf)throw std::runtime_error("dense block mismatch");++cases;
 }
 for(I L=140;L<3000;L+=137){I R=L+L/3;I F=2*L+3;auto e=reference(L,R,F);for(unsigned r:{0,3,7,12})for(unsigned d:{2,12,24,100}){if(dense_run(L,R,r,F,29,false,d)!=e)throw std::runtime_error("dense sweep mismatch");++cases;}}
 cout<<"Dense strict/failure and sweep comparisons passed: "<<cases<<endl;
}
int main(int argc,char**argv){if(argc==1){dense_test();return 0;}if(argc<4||argc>7)return 2;I L=std::stoul(argv[1]),R=std::stoul(argv[2]),F=std::stoul(argv[3]);unsigned r=argc>=5?std::stoul(argv[4]):22,cap=argc>=6?std::stoul(argv[5]):29,density=argc>=7?std::stoul(argv[6]):24;dense_run(L,R,r,F,cap,true,density);}
