// Exact folded common-clock sweep with fitted blocks and in-block birth probes.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>
using U=uint64_t;using I=uint32_t;using namespace std;
static inline U dw(U b){return (b&0xAAAAAAAAAAAAAAAAull)+2*(b&0xCCCCCCCCCCCCCCCCull)+4*(b&0xF0F0F0F0F0F0F0F0ull)+8*(b&0xFF00FF00FF00FF00ull)+16*(b&0xFFFF0000FFFF0000ull)+32*(b&0xFFFFFFFF00000000ull);}
struct Seen{vector<U>bits;explicit Seen(I n):bits((U(n)+63)/64){}bool insert(I x){U m=U(1)<<(x&63),&w=bits[x>>6];if(w&m)return false;w|=m;return true;}bool has(I x)const{return (bits[x>>6]>>(x&63))&1;}void clear(I x){bits[x>>6]&=~(U(1)<<(x&63));}};
struct Block{I q,F;unsigned k;U M;double inv;Block(I F0,unsigned k0):q(F0-k0),F(F0),k(k0),M(U(1)<<k0),inv(1.0/F0){}
 I parent(I z)const{U X=U(z)<<k,b=U(double(X)*inv);if(b*F>X)--b;else if((b+1)*F<=X)++b;if(b*F>X||(b+1)*F<=X)b=X/F;for(int i=0;i<2;++i,++b)if(b<M){U w=U(q)*b+dw(b);if(w<=X&&X-w<q){I c=X-w;return c&&c+3<=q?min(c,q-2-c):0;}}return 0;}};
static vector<I> jump(I q,unsigned r){I M=I(1)<<r,mask=M-1;Seen seen(M);vector<I>rs{0};seen.insert(0);for(unsigned j=0;j<r;++j){I shift=I((U(q+j)<<j)&mask),count=rs.size();for(I i=0;i<count;++i){I x=(rs[i]-shift)&mask;if(seen.insert(x))rs.push_back(x);}}vector<I>out;I top=(q-2)/2;for(U base=0;base<=top;base+=M)for(I x:rs){U c=base+x;if(c&&c<=top)out.push_back(I(c));}return out;}
// Forward probe from a folded center: its descendants are a set of folded
// classes, since complement commutes with each strict zero-target edge.
// Each class has at most one folded parent, so descendants from distinct
// classes cannot collide. Siblings coincide only when c is self-complementary.
static bool probe(I q,I F,const Seen&live,vector<I>&a,vector<I>&b,U&work){a.assign(1,(q-2)/2);while(q<F&&!a.empty()){b.clear();work+=a.size();for(I c:a){I child1=0;if(c%2==0){I z=c/2;child1=min(z,q-1-z);b.push_back(child1);}if((c+q)%2==0){I z=(c+q)/2,zf=min(z,q-1-z);if(zf!=child1)b.push_back(zf);}}a.swap(b);++q;}for(I c:a)if(live.has(c))return true;return false;}
static vector<I> run(I L,I R,unsigned r,I F,unsigned cap,bool verbose){if(L<14||L>R||U(R)+4>F||F>U(2)*L+3||F>=1000000000||r>26||!cap||cap>26)throw runtime_error("arguments");r=min<unsigned>(r,F-(R+4));I q=F-r;auto t=chrono::steady_clock::now();auto seconds=[&](){return chrono::duration<double>(chrono::steady_clock::now()-t).count();};auto a=jump(q,r);Seen live((q-2)/2+1),next((q-2)/2+1);for(I c:a)live.insert(c);vector<I>hits,pa,pb;U visits=0,probes=0,blocks=0;
 if(verbose)cout<<"F="<<F<<" q="<<q<<" jump="<<r<<" folded initial="<<a.size()<<endl;
 if(q%2==0&&q-4<=R&&live.has((q-2)/2))hits.push_back(q-4);
 while(q>L+4&&!a.empty()){unsigned k=min({cap,unsigned(q-(L+4)),unsigned(63-__builtin_clzll(q)-1)});if(!k)throw runtime_error("fit");I p=q-k;Block block(q,k);
 // q itself was checked in the preceding block; probe all new clocks p..q-1.
 // Only b=2 mod 4 births can have a positive-length continuation.
 I top=min(q-1,R+4);for(I b=top-((top+2)%4);b>=p;){if(probe(b,q,live,pa,pb,probes))hits.push_back(b-4);if(b<4||b-4<p)break;b-=4;}
 visits+=a.size();size_t w=0;for(I z:a){I c=block.parent(z);if(c&&next.insert(c))a[w++]=c;live.clear(z);}a.resize(w);swap(live,next);q=p;++blocks;
 }
 reverse(hits.begin(),hits.end());if(verbose){cout<<"interval "<<L<<".."<<R<<" visits="<<visits<<" probe_work="<<probes<<" blocks="<<blocks<<" hits="<<hits.size()<<" seconds="<<seconds()<<endl;for(I n:hits)cout<<n<<" ";cout<<endl;}return hits;
}
static vector<I> reference(I L,I R,I F){vector<I>a,b,hits;for(I c=1;c<=F-3;++c)a.push_back(c);for(I q=F;;){if(q%2==0&&q-4<=R&&binary_search(a.begin(),a.end(),(q-2)/2))hits.push_back(q-4);if(q==L+4)break;--q;b.clear();for(I z:a){I c=2*z%q;if(c&&c+3<=q)b.push_back(c);}sort(b.begin(),b.end());b.erase(unique(b.begin(),b.end()),b.end());a.swap(b);}reverse(hits.begin(),hits.end());return hits;}
int main(int argc,char**argv){if(argc==2&&string(argv[1])=="test"){unsigned cases=0;for(I L=14;L<500;L+=3){I R=L+L/3;for(I F:{R+4,R+5,2*L+3}){if(F>2*L+3)continue;auto ref=reference(L,R,F);for(unsigned r:{0,1,3,7,12,20})for(unsigned cap:{1,2,3,7,26}){auto got=run(L,R,r,F,cap,false);if(got!=ref){cerr<<"mismatch L="<<L<<" F="<<F<<" r="<<r<<" cap="<<cap<<endl;return 1;}++cases;}}}cout<<"reference comparisons passed: "<<cases<<endl;return 0;}if(argc<3||argc>6)return 2;I L=stoul(argv[1]),R=stoul(argv[2]);unsigned r=argc>=4?stoul(argv[3]):22;I F=argc>=5?stoul(argv[4]):2*L+3;unsigned cap=argc>=6?stoul(argv[5]):26;if(argc<5&&F>2048){I aligned=F-((F-11)%2048);if(aligned>=R+4)F=aligned;}run(L,R,r,F,cap,true);}
