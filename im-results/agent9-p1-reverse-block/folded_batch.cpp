// Exact symmetry-quotiented common-clock carry sweep with modular jump.
// g++ -O3 -std=c++17 folded_batch.cpp -o folded_batch
// ./folded_batch L R [jump=20] [F=largest <=2L+3 congruent 11 mod 2048]
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>
using namespace std;
using U=uint64_t;
using I=uint32_t;
// c in 1..q-3; fold(c)=min(c,q-2-c).
// At child clock q+1, a=min(z,q-1-z). If 2a<=q-3 the
// unique folded parent is min(2a,q-2-2a); otherwise none.
static void back(I q,vector<I>&a,vector<I>&b,U&visits){
 visits+=a.size(); b.clear();
 auto mid=upper_bound(a.begin(),a.end(),(q-2)/4);
 auto end=upper_bound(mid,a.end(),(q-3)/2);
 auto l=a.begin(),r=end;
 while(l!=mid && r!=mid){
  I x=2*(*l),y=q-2-2*(*(r-1));
  if(x<=y){b.push_back(x);++l;if(x==y)--r;}
  else{b.push_back(y);--r;}
 }
 while(l!=mid){b.push_back(2*(*l));++l;}
 while(r!=mid){--r;b.push_back(q-2-2*(*r));}
 a.swap(b);
}
// A length-r legal continuation exists from interior c iff
// c is a residue in {-sum (q+j)2^j b_j mod 2^r}. All intermediate
// interior guards follow automatically from parity and the input interior.
static vector<I> jump(I q,unsigned r){
 I M=I(1)<<r,mask=M-1;
 vector<uint8_t>seen(M);vector<I> residues{0};seen[0]=1;
 for(unsigned j=0;j<r;++j){
  I shift=I((U(q+j)<<j)&mask),count=residues.size();
  for(I i=0;i<count;i++){I x=(residues[i]-shift)&mask;if(!seen[x]){seen[x]=1;residues.push_back(x);}}
 }
 sort(residues.begin(),residues.end());
 vector<I> out;I top=(q-2)/2;
 for(U base=0;base<=top;base+=M){
  for(I x:residues){U c=base+x;if(c>top)break;if(c)out.push_back(I(c));}
 }
 return out;
}
static vector<I> run(I L,I R,unsigned r,I F,bool verbose){
 if(L<14||L>R||U(R)+4>F||F>U(2)*L+3||F>=1000000000||r>26)throw runtime_error("invalid arguments");
 r=min<unsigned>(r,F-(R+4));I q=F-r;
 auto start=chrono::steady_clock::now();auto seconds=[&](){return chrono::duration<double>(chrono::steady_clock::now()-start).count();};
 auto a=jump(q,r);vector<I>b;b.reserve(a.size());vector<I>hits;U visits=0;
 if(verbose)cout<<"F="<<F<<" q="<<q<<" jump="<<r<<" folded initial="<<a.size()<<endl;
 while(true){
  if(q%2==0&&q-4<=R&&!a.empty()&&a.back()==(q-2)/2)hits.push_back(q-4);
  if(q==L+4||a.empty())break;
  back(--q,a,b,visits);
 }
 reverse(hits.begin(),hits.end());
 if(verbose){cout<<"interval "<<L<<".."<<R<<" visits="<<visits<<" hits="<<hits.size()<<" seconds="<<seconds()<<endl;for(I n:hits)cout<<n<<" ";cout<<endl;}
 return hits;
}
// Independent unquotiented reverse sweep for small test cases.
static vector<I> reference(I L,I R,I F){
 vector<I>a,b,hits;for(I c=1;c<=F-3;++c)a.push_back(c);
 for(I q=F;;){
  if(q%2==0&&q-4<=R&&binary_search(a.begin(),a.end(),(q-2)/2))hits.push_back(q-4);
  if(q==L+4)break;
  --q;b.clear();for(I z:a){I c=2*z%q;if(c&&c+3<=q)b.push_back(c);}sort(b.begin(),b.end());b.erase(unique(b.begin(),b.end()),b.end());a.swap(b);
 }
 reverse(hits.begin(),hits.end());return hits;
}
int main(int argc,char**argv){
 if(argc==2&&string(argv[1])=="test"){
  unsigned cases=0;for(I L=14;L<500;L+=3){I R=L+L/3;for(I F:{R+4, R+5, 2*L+3}){if(F>2*L+3)continue;auto ref=reference(L,R,F);for(unsigned r:{0,1,3,7,12,20}){if(run(L,R,r,F,false)!=ref)throw runtime_error("test mismatch");++cases;}}}
  cout<<"reference comparisons passed: "<<cases<<endl;return 0;
 }
 if(argc<3||argc>5)return 2;I L=stoul(argv[1]),R=stoul(argv[2]);unsigned r=argc>=4?stoul(argv[3]):20;I F=argc==5?stoul(argv[4]):2*L+3; if(argc!=5&&F>2048){I aligned=F-((F-11)%2048);if(aligned>=R+4)F=aligned;}
 run(L,R,r,F,true);
}
