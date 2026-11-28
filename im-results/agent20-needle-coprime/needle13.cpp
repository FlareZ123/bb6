#include <gmpxx.h>
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <chrono>
#include <iostream>
#include <set>
#include <vector>
#include <omp.h>
using U=unsigned long;using Z=mpz_class;
static Z pow2(U e){Z z=1;mpz_mul_2exp(z.get_mpz_t(),z.get_mpz_t(),e);return z;}
static U bits(const Z&z){return mpz_sizeinbase(z.get_mpz_t(),2);}
static U mod(const Z&z,U p){return mpz_fdiv_ui(z.get_mpz_t(),p);}
static U powmod(U a,U e,U p){U z=1;while(e){if(e&1)z=z*a%p;a=a*a%p;e>>=1;}return z;}
static U apmod(U r,U a,U p){U A=powmod(2,a,p),P=0,n=1;for(U i=0;i<r;i++){P=(A*A%p*P+n*((A+p-3)%p))%p;n=n*9%p;}return A*P%p;}
struct Cache{U k=0;Z v=1;Z get(U n){if(n==k)return v;if(n<k&&k-n<=5000){U delta=k-n;if(delta<=20){U p=1;for(U i=0;i<delta;i++)p*=3;mpz_divexact_ui(v.get_mpz_t(),v.get_mpz_t(),p);}else{Z p;mpz_ui_pow_ui(p.get_mpz_t(),3,delta);mpz_divexact(v.get_mpz_t(),v.get_mpz_t(),p.get_mpz_t());}}else mpz_ui_pow_ui(v.get_mpz_t(),3,n);k=n;return v;}};
static void fold(Z& s,U m){Z hi,lo;while(bits(s)>m){mpz_tdiv_q_2exp(hi.get_mpz_t(),s.get_mpz_t(),m);mpz_tdiv_r_2exp(lo.get_mpz_t(),s.get_mpz_t(),m);s=lo-3*hi;}}
static Z pow3special(U k,U m){Z z=1;int b=0;for(U t=k;t>>=1;)++b;for(;b>=0;--b){z*=z;fold(z,m);if((k>>b)&1){z*=3;fold(z,m);}}return z;}
static Z red(U e,U m,const Z&D,Cache&cache){U k=e/m,s=e%m;Z z,three=3;if(m>=25000&&k<=8*m)z=cache.get(k);else if(m>=8)z=pow3special(k,m);else mpz_powm_ui(z.get_mpz_t(),three.get_mpz_t(),k,D.get_mpz_t());mpz_mul_2exp(z.get_mpz_t(),z.get_mpz_t(),s);if(k&1)z=-z;return z;}
static bool divisible(Z s,U m,const Z&D){Z hi,lo;while(bits(s)>m){if(m<8)return mpz_divisible_p(s.get_mpz_t(),D.get_mpz_t());mpz_tdiv_q_2exp(hi.get_mpz_t(),s.get_mpz_t(),m);mpz_tdiv_r_2exp(lo.get_mpz_t(),s.get_mpz_t(),m);s=lo-3*hi;}return s==0;}
static void divisors(U n,U lo,U hi,std::set<U>&out){for(U d=1;d<=n/d;++d)if(n%d==0){U q=n/d;if(lo<=d&&d<=hi)out.insert(d);if(lo<=q&&q<=hi)out.insert(q);}}
// Exact zero test for rotated sparse sum, without allocating any large shift.
template<class T> static bool sparseZero(T t){std::sort(t.begin(),t.end(),[](const auto&x,const auto&y){return x.first<y.first;});Z acc=t[0].second;for(U i=1;i<t.size();i++){U gap=t[i].first-t[i-1].first;if(!mpz_divisible_2exp_p(acc.get_mpz_t(),gap))return false;mpz_tdiv_q_2exp(acc.get_mpz_t(),acc.get_mpz_t(),gap);acc+=t[i].second;}return acc==0;}
static U bitsu(U z){return z?8*sizeof(U)-__builtin_clzl(z):0;}
static bool rotation_reject(U m,U a,U E,U N){const long C=5-2*long(m);const U HC=bitsu(3*U(std::abs(C))),HD=bitsu(U(std::abs(C-long(N))));if(a/m<HC)return false;auto good=[&](U h,U e,U H){U q=(e+h)/m,s=(e+h)%m;return s+H+8*((q+4)/5)+2<m;};for(U h:{U(0),(m-E%m)%m,(m-a%m)%m})if(good(h,E,1)&&good(h,a,HD)&&good(h,0,HC))return true;return false;}
int main(int argc,char**argv){assert(argc==7);U r=std::stoul(argv[1]);assert(r>=8&&r<=14);Z c(argv[2]),d(argv[3]),den(argv[4]);assert(c>0&&mpz_popcount(c.get_mpz_t())==1&&mpz_even_p(d.get_mpz_t())&&den>0&&mpz_odd_p(den.get_mpz_t())&&mod(den,3)!=0);bool root=c==1;assert(!root||(d==0&&den==1));U N=1;for(U i=0;i<r;i++)N*=9;U a=(N+5)/2,M=2*r*a,E=M+a;assert(bits(6*den+abs(d))<M-1);U vc=mpz_scan1(c.get_mpz_t(),0);Z Cmax=abs(d)+den*(2*M+5);U H=bits(c*(N+1)+4*Cmax);U cut;std::set<U> extra;
if(root){Z L=(Z(13)*(r+1)*a-1)/4,sq;mpz_sqrt(sq.get_mpz_t(),L.get_mpz_t());cut=sq.get_ui();}else{U lo=1,hi=M;while(lo<hi){U mid=(lo+hi)/2;if(mid>=3*(H+2*((E+mid-1)/mid)))hi=mid;else lo=mid+1;}cut=lo-1;divisors(E+vc,cut+1,M,extra);divisors(a,cut+1,M,extra);divisors(E-a+vc,cut+1,M,extra);}
U lo=std::stoul(argv[5]),hi=std::min(cut,std::stoul(argv[6]));assert(lo>=1&&lo<=hi);std::vector<bool> blocked(cut+1,false);U rotation=0;if(root)for(U m=lo;m<=hi;++m)if(rotation_reject(m,a,E,N)){blocked[m]=true;++rotation;}U sieve=0;for(U p=5;p<=100000;p+=2){bool prime=true;for(U z=3;z*z<=p;z+=2)if(p%z==0){prime=false;break;}if(!prime)continue;U res=0,per=0,t=1;do{++per;t=t*2%p;if(t==p-3)res=per;}while(t!=1);if(!res)continue;U ap=apmod(r,a,p),cm=mod(c,p),dm=mod(d,p),lm=mod(den,p);for(U m=res;m<=hi;m+=per){if(m>=lo&&!blocked[m]&&(cm*ap+dm+lm*((5+p-2*(m%p)%p)%p))%p){blocked[m]=true;++sieve;}}}
U sparse=0,full=0,largeZero=0;std::vector<U> parents;auto start=std::chrono::steady_clock::now();
auto exact=[&](U m,const Z&C,const Z&D){Z LD=den*D,A,two=2,P=0,n=1;mpz_powm_ui(A.get_mpz_t(),two.get_mpz_t(),a,LD.get_mpz_t());for(U i=0;i<r;i++){P=(A*A*P+n*(A-3))%LD;n*=9;}Z F=c*A*P+C;if(!mpz_divisible_p(F.get_mpz_t(),LD.get_mpz_t()))return false;assert(bits(3*LD+abs(C))<M-1);return true;};
#pragma omp parallel reduction(+:sparse,full)
{Cache ce,ca;
#pragma omp for schedule(static)
for(U m=lo;m<=hi;m++){if(blocked[m])continue;Z D=pow2(m)+3,C=d+den*(5-2*Z(m));Z S=c*red(E,m,D,ce)+(C-c*N)*red(a,m,D,ca)+3*C;bool hit=divisible(S,m,D);if(m%997==0||hit)assert(hit==bool(mpz_divisible_p(S.get_mpz_t(),D.get_mpz_t())));if(!hit){++sparse;continue;}++full;if(exact(m,C,D)){
#pragma omp critical
parents.push_back(m-1);}}}
assert(rotation+sieve+sparse+full==hi-lo+1);
// Large candidates belong to the final chunk. A nonzero rotated sum excludes
// them via the source-checked gap lemma; large zero remains explicitly open.
if(hi==cut)for(U m:extra){Z C=d+den*(5-2*Z(m));U B=H+2*((E+m-1)/m);assert(3*B<=m);U h=0;while(h<=2*B&&((E+h)%m>m-B||(a+h)%m>m-B))h+=B;assert(h<=2*B);auto term=[&](U e,Z k){U q=(e+h)/m;Z f;mpz_ui_pow_ui(f.get_mpz_t(),3,q);if(q&1)f=-f;return std::make_pair((e+h)%m,Z(k*f));};std::array<std::pair<U,Z>,3> ts={term(E,c),term(a,C-c*N),term(0,3*C)};assert(bits(abs(ts[0].second)+abs(ts[1].second)+abs(ts[2].second))<=B);if(sparseZero(ts)){
    // The three-term necessary condition may be spurious when A+3 shares a factor with D.
    // Check the original sparse polynomial by an independent good rotation.
    U B2=bits(c*Z((N-1)/2)+Cmax)+2*((M+m-1)/m);
    if((2*r+1)*B2<=m){
      U shift=0;auto good=[&](U sh){for(U j=0;j<=2*r;j++)if((j*a+sh)%m>m-B2)return false;return true;};
      while(shift<=2*r*B2&&!good(shift))shift+=B2;assert(shift<=2*r*B2);
      std::vector<std::pair<U,Z>> poly;Z mass=0;
      for(U j=0;j<=2*r;j++){Z k;if(j==0)k=C;else{mpz_ui_pow_ui(k.get_mpz_t(),3,2*r-j);if((2*r-j)&1)k=-k;k*=c;}U q=(j*a+shift)/m;Z f;mpz_ui_pow_ui(f.get_mpz_t(),3,q);if(q&1)f=-f;k*=f;mass+=abs(k);poly.emplace_back((j*a+shift)%m,k);}
      assert(bits(mass)<=B2);if(!sparseZero(poly)){std::cout<<"EXTRA_POLY_REJECT m="<<m<<"\n";continue;}
    }
    if(m<=2000000){Z D=pow2(m)+3;if(exact(m,C,D))parents.push_back(m-1);continue;}
    ++largeZero;std::cout<<"LARGE_UNRESOLVED m="<<m<<"\n";
}}
std::sort(parents.begin(),parents.end());std::cout<<"r="<<r<<" c="<<c<<" d="<<d<<" L="<<den<<" range="<<lo<<".."<<hi<<" cut="<<cut<<" rotation="<<rotation<<" sieve="<<sieve<<" sparse="<<sparse<<" exact="<<full<<" extras="<<(hi==cut?extra.size():0)<<" largeZero="<<largeZero<<" parents=";for(U v:parents){U m=v+1;Z C=d+den*(5-2*Z(m));std::cout<<v<<"["<<c*pow2(m)<<","<<C*pow2(m)<<","<<den*(pow2(m)+3)<<"],";}std::cout<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"\n";return largeZero?3:0;}
