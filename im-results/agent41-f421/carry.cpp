#define F421_NO_MAIN
#include "compressed.cpp"
#include <boost/multiprecision/cpp_int.hpp>

// A regular cell P^p Z^e Q^q, p>=1,q>=2, e in {0,1}.
// For a nonzero marker integer, even macros decrement the marker integer;
// count visits and terminal hits at each cell over an entire interval.
using Int=boost::multiprecision::cpp_int;
struct Cell{U p,q;bool e;};
struct Skip{U k;Big steps;};
Skip carry(Word& w,U limit){
 if(!limit||w.size()<2||w[0].p!=2||w[1].p!=1||w[1].n<2)return {};
 U a=w[0].n,b=w[1].n;vector<Cell> cells;size_t pos=2;Int V=0,d=1;
 while(pos<w.size()&&w[pos].p==2){size_t j=pos+1;bool e=false;if(j<w.size()&&w[j].p==0&&w[j].n==1){e=true;++j;}if(j==w.size()||w[j].p!=1||w[j].n<2)break;cells.push_back({w[pos].n,w[j].n,e});if(e)V+=d;d<<=1;pos=j+1;}
 if(V==0)return {};
 U k=limit;if(V<k)k=V.convert_to<U>();
 // Keep every retained P run positive throughout the skip.
 d=1;for(auto c:cells){Int cap=V%d+Int(c.p-1)*d;if(cap<k)k=cap.convert_to<U>();d<<=1;}
 if(!k)return {};
 Int W=V-k;Big K=k;Big steps=8*K*(Big(a)+b)+12*K*(K-1)+16*K;
 Word out;out.reserve(w.size()+cells.size());push(out,2,a+2*k);push(out,1,b+k);d=1;
 for(auto c:cells){Int upper=V/d,lower=W/d;U n=(upper-lower).convert_to<U>();U t=((upper+1)/2-(lower+1)/2).convert_to<U>();U s=n-t;bool firstOdd=(upper&1)!=0;
  assert(n<=c.p-1);steps+=4*(Big(n)*c.p-Big(n)*(n? n-1:0)/2);steps+=8*(Big(s)*c.q+Big(s)*(s?s-1:0)/2+Big(firstOdd)*s);
  push(out,2,c.p-n);if((lower&1)!=0)push(out,0);push(out,1,c.q+t);d<<=1;}
 for(;pos<w.size();++pos)push(out,w[pos].p,w[pos].n);
 w.swap(out);return {k,steps};
}
bool equal(const Word&a,const Word&b){if(a.size()!=b.size())return false;for(size_t i=0;i<a.size();++i)if(a[i].p!=b[i].p||a[i].n!=b[i].n)return false;return true;}
int main(int argc,char**argv){
 U N=argc>1?stoull(argv[1]):1000000;assert(N<=1000000000000000000ULL);
 bool check=argc>2&&string(argv[2])=="--check";Word w=pack("10010101");Big time=24;U head=4,odd=0,maxruns=0,skips=0,skipped=0,singles=0,largest=0;
 for(U i=0;i<N;){Word old;if(check)old=w;auto s=carry(w,N-i);if(s.k){++skips;skipped+=s.k;largest=max(largest,s.k);if(check){Big cost=0;for(U j=0;j<s.k;++j){auto r=advance(old);assert(!r.bad&&r.dx==4);cost+=r.steps;}assert(equal(old,w)&&cost==s.steps);}time+=s.steps;head+=4*s.k;i+=s.k;}
  else{auto r=advance(w);++singles;time+=r.steps;head+=r.dx;if(r.bad){cout<<"F1 after macro "<<i<<" at primitive step "<<decimal(time)<<"\n";return 2;}++i;if(r.firstL%2)++odd;}
  maxruns=max(maxruns,U(w.size()));}
 cout<<"macros="<<N<<" steps="<<decimal(time)<<" head="<<head<<" odd="<<odd<<" runs="<<w.size()<<" maxruns="<<maxruns<<" skips="<<skips<<" skipped="<<skipped<<" singles="<<singles<<" largest="<<largest<<"\n";for(auto [p,n]:w)cout<<"ZQPR"[p]<<n<<" ";cout<<"\n";}
