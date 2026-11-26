#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <stdexcept>
#include <omp.h>
using namespace std; using U=uint64_t;
static inline U dw(U b){return (b&0xAAAAAAAAAAAAAAAAull)+2*(b&0xCCCCCCCCCCCCCCCCull)+4*(b&0xF0F0F0F0F0F0F0F0ull)+8*(b&0xFF00FF00FF00FF00ull)+16*(b&0xFFFF0000FFFF0000ull)+32*(b&0xFFFFFFFF00000000ull);}
static int fit(int F,int rem){return min({rem,26,63-__builtin_clzll(F)-1});}
struct Block{int q,k;U Y,F,M;double inv;Block(int F0,int rem,U y=0):q(F0-fit(F0,rem)),k(fit(F0,rem)),Y(y),F(F0),M((U(1)<<k)-1),inv(1.0/F){} int parent(int z)const {U X=(U(z)<<k)+Y;U b=U(double(X)*inv); if(b*F>X)--b; else if((b+1)*F<=X)++b; if(b*F>X || (b+1)*F<=X) b=X/F; // exact quotient restored; range checked against legal broad carry
 for(int i=0;i<2;++i,++b)if(b<=M){U f=U(q)*b+dw(b);if(f<=X&&X-f<U(q))return int(X-f);}return -1;}};
struct Seen{vector<U> bits; explicit Seen(int n):bits((n+63)/64){} bool insert(int x){U mask=U(1)<<(x&63);U &w=bits[x>>6];if(w&mask)return false;w|=mask;return true;}void clear(int x){bits[x>>6]&=~(U(1)<<(x&63));}};
struct DSU{vector<int> p;explicit DSU(int n):p(n,-1){}int find(int x){int r=x;while(p[r]>=0)r=p[r];while(x!=r){int y=p[x];p[x]=r;x=y;}return r;}int unite(int a,int b){a=find(a);b=find(b);if(a==b)return a;if(p[a]>p[b])swap(a,b);p[a]+=p[b];p[b]=a;return a;}};
struct Prefix{string y;int c,r;};struct Entry{int c,id;};
// Exact carry set: no sort is needed; membership is tracked by a packed bitmap.
template<class Bit>vector<int> live(int q0,int F,Bit y,U& work){int r=min(22,F-q0),q=F-r;uint32_t M=1u<<r,mask=M-1,Y=0;for(int j=0;j<r;j++)Y|=uint32_t(y(q+j))<<j;Seen small(M);vector<uint32_t>res{Y};small.insert(Y);for(int j=0;j<r;j++){uint32_t shift=uint32_t((U(q+j)<<j)&mask),count=res.size();for(uint32_t i=0;i<count;i++){uint32_t c=(res[i]-shift)&mask;if(small.insert(c))res.push_back(c);}}
 vector<int>a; for(U base=0;base<U(q);base+=M)for(auto x:res)if(base+x<U(q))a.push_back(int(base+x)); Seen seen(q);
 while(q>q0&&!a.empty()){Block b(q,q-q0);for(int j=0;j<b.k;j++)b.Y|=U(y(b.q+j))<<j;work+=a.size();size_t w=0;for(int z:a){int c=b.parent(z);if(c>=0&&seen.insert(c))a[w++]=c;}a.resize(w);for(int c:a)seen.clear(c);q=b.q;}
 return a;}
// Maintain terminal labels using the exact reverse map and a packed bitmap.
// Sorting is used only on this usually-small midpoint set.
template<class Bit>vector<int> filter(int q0,int F,Bit y,int root,const vector<int>& ends,U&work){vector<Entry>a; a.reserve(ends.size());for(int i=0;i<(int)ends.size();i++)a.push_back({ends[i],i});DSU d(a.size());while(F>q0&&!a.empty()){Block b(F,F-q0);for(int j=0;j<b.k;j++)b.Y|=U(y(b.q+j))<<j;work+=a.size();size_t w=0;for(auto e:a){int c=b.parent(e.c);if(c>=0)a[w++]={c,e.id};}a.resize(w);sort(a.begin(),a.end(),[](Entry x,Entry y){return x.c<y.c;});w=0;for(auto e:a){if(w&&a[w-1].c==e.c)a[w-1].id=d.unite(a[w-1].id,e.id);else a[w++]=e;}a.resize(w);F=b.q;}auto it=find_if(a.begin(),a.end(),[&](Entry e){return e.c==root;});if(it==a.end())return {};int label=d.find(it->id);vector<int>out;for(int i=0;i<(int)ends.size();i++)if(d.find(i)==label)out.push_back(ends[i]);sort(out.begin(),out.end());return out;}
void save(const string&p,int n,int s,const vector<Prefix>&gs){ofstream o(p,ios::binary);auto w=[&](auto x){o.write(reinterpret_cast<const char*>(&x),sizeof(x));};w(n);w(s);U m=gs.size();w(m);for(auto&g:gs){w(g.c);w(g.r);o.write(g.y.data(),s);}if(!o)throw runtime_error("write");}
bool load(const string&p,int n,int&s,vector<Prefix>&gs){ifstream i(p,ios::binary);if(!i)return false;auto r=[&](auto&x){i.read(reinterpret_cast<char*>(&x),sizeof(x));};int nn;r(nn);if(nn!=n)throw runtime_error("n");r(s);U m;r(m);gs.resize(m);for(auto&g:gs){r(g.c);r(g.r);g.y.resize(s);i.read(g.y.data(),s);}if(!i)throw runtime_error("read");return true;}
int main(int argc,char**argv){if(argc<4)return 2;int n=stoi(argv[1]),K=stoi(argv[2]),block=stoi(argv[3]);if(n<14||n%2||K<=n||n>100000000||K>250000000||block<1||block>n)return 2;string path=argc>=5?argv[4]:"";int maxBlocks=argc>=6?stoi(argv[5]):-1;U A=U(n)+K+2,L=2*(U(n)+3*U(K)+10)+6,prod=A*L;auto safe=[&](int g){int e=n-g;return e>=62||(e>=0&&(U(6)<<e)>prod);};if((n<63&&A>(U(1)<<n))||!safe(0)||!safe(1))return 3;auto t=chrono::steady_clock::now();int s=1,maxgap=1;vector<Prefix>gs={{"1",(n+2)/2,3}};if(!path.empty())load(path,n,s,gs);for(int blocks=0;s+n<=K;blocks++){int h=min(block,n);struct Part{vector<Prefix>next;U work=0,filterWork=0;size_t mids=0;int maxgap=0;};vector<Part>parts(gs.size());
#pragma omp parallel for schedule(dynamic)
 for(int gi=0;gi<(int)gs.size();gi++){auto&g=gs[gi];auto&part=parts[gi];auto y=[&](int q){int i=q-n-3;return i<n?0:g.y[i-n]-'0';};auto mids=live(n+s+h+3,2*n+s+3,y,part.work);part.mids=mids.size();auto good=filter(n+s+3,n+s+h+3,y,g.c,mids,part.filterWork);for(int a:good){int c=a;string extra(h,'0');for(int i=s+h-1;i>=s;i--){int q=n+i+3,v=2*c+y(q);if(v>=2*q)throw runtime_error("rewind");if(v>=q){extra[i-s]='1';v-=q;}c=v;}if(c!=g.c)throw runtime_error("root");Prefix g2={g.y,a,g.r};int last=g2.y.back()-'0',run=0;for(int k=s-1;k>=0&&g2.y[k]==g2.y.back();k--)run++;for(int j=0;j<h;j++){int v=g2.r+7*(extra[j]-'0'),bit=v%2;g2.r=v/2;g2.y+=char('0'+bit);run=bit==last?run+1:1;last=bit;int gap=min(s+j+1,run+1);part.maxgap=max(part.maxgap,gap);if(!safe(gap))throw runtime_error("margin");}part.next.push_back(move(g2));}}
 vector<Prefix>next;U work=0,fw=0,mid=0;for(auto&part:parts){work+=part.work;fw+=part.filterWork;mid+=part.mids;maxgap=max(maxgap,part.maxgap);for(auto&g:part.next)next.push_back(move(g));}cout<<"s="<<s<<" h="<<h<<" old="<<gs.size()<<" mids="<<mid<<" next="<<next.size()<<" work="<<work<<" filter="<<fw<<" gap="<<maxgap<<" sec="<<chrono::duration<double>(chrono::steady_clock::now()-t).count()<<endl;if(next.empty()){cout<<"END "<<n<<" "<<n+s<<endl;return 0;}if(s+h+n>K)break;s+=h;gs=move(next);if(!path.empty())save(path,n,s,gs);if(blocks+1==maxBlocks)break;}cout<<"END "<<n<<" 0"<<endl;return 1;}
