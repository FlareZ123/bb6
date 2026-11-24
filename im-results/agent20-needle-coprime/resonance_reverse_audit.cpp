#include <gmpxx.h>
#include <algorithm>
#include <cassert>
#include <iostream>
#include <set>
#include <vector>
#include <string>
#include <functional>
using U=unsigned long;
using Z=mpz_class;
static Z pow2(U n){Z z=1;mpz_mul_2exp(z.get_mpz_t(),z.get_mpz_t(),n);return z;}
static Z reduce2(U e,U m,const Z& D){U q=e/m,s=e%m;Z z,three=3;if(q<=m/2+16)mpz_ui_pow_ui(z.get_mpz_t(),3,q);else mpz_powm_ui(z.get_mpz_t(),three.get_mpz_t(),q,D.get_mpz_t());mpz_mul_2exp(z.get_mpz_t(),z.get_mpz_t(),s);if(q&1)z=-z;return z;}
static U modpow(U b,U e,U m){U x=1;while(e){if(e&1)x=x*b%m;b=b*b%m;e>>=1;}return x;}
static U APmod(U r,U a,U p){U A=modpow(2,a,p),P=0,n=1;for(U i=0;i<r;i++){P=(A*A%p*P+n*(A+p-3)%p)%p;n=n*9%p;}return A*P%p;}
static U modui(const Z& x,U p){return mpz_fdiv_ui(x.get_mpz_t(),p);}
static U bits(const Z& x){return mpz_sizeinbase(x.get_mpz_t(),2);}
static U v2(const Z& x){assert(x!=0);Z y=abs(x);return mpz_scan1(y.get_mpz_t(),0);}
static Z APmodBig(U r,U a,const Z& mod){Z A=2,P=0,n=1;mpz_powm_ui(A.get_mpz_t(),A.get_mpz_t(),a,mod.get_mpz_t());Z aa=(A*A)%mod;for(U i=0;i<r;i++){P=(aa*P+n*(A-3))%mod;n*=9;}return A*P%mod;}
static void divisorsIn(U n,U lo,U hi,std::set<U>& out){if(!n)return;for(U d=1;d<=n/d;++d)if(n%d==0){U q=n/d;if(lo<=d&&d<=hi)out.insert(d);if(lo<=q&&q<=hi)out.insert(q);}}
struct Prime{U p,residue,period,ap;};
struct Target{Z c,d,L;};
int main(int argc,char**argv){
    if(argc!=2)return 2;U r=std::stoul(argv[1]);assert(r>=4&&r<=12);
    U N=1;for(U i=0;i<r;i++)N*=9;U a=(N+5)/2,M=2*r*a,E=M+a;
    std::vector<Prime> primes;
    for(U p=5;p<=10000;p+=2){bool prime=true;for(U d=3;d*d<=p;d+=2)if(p%d==0){prime=false;break;}if(!prime)continue;U residue=0,period=0,t=1;do{period++;t=t*2%p;if(t==p-3)residue=period;}while(t!=1);if(residue)primes.push_back({p,residue,period,APmod(r,a,p)});}
    U nodes=0,leaves=0,edges=0;bool cutoffFailure=false;
    std::function<void(const Target&,const std::string&)> walk=[&](const Target& t,const std::string& path){
        ++nodes;
        assert(t.c>0&&t.L>0&&mpz_odd_p(t.L.get_mpz_t())&&mpz_even_p(t.d.get_mpz_t())&&modui(t.L,3)!=0&&mpz_popcount(t.c.get_mpz_t())==1);
        // AP=(A^(2r+1)-NA)/(A+3)>2^(M-1) for these parameters.
        // This bound certifies that the state differs from shifted blank-entry 3.
        if(bits(6*t.L+abs(t.d))>M-1){std::cout<<path<<" root lower bound unavailable\n";cutoffFailure=true;return;}
        U vc=v2(t.c);
        Z maxC=abs(t.d)+t.L*(2*M+5),bound=maxC+t.c*N+1;
        U H=bits(bound)+4,B=H+4*r+4;
        if(a<(4*r+1)*B){std::cout<<path<<" high cutoff unavailable\n";cutoffFailure=true;return;}
        auto oldExcluded=[&](U m){U k=(a+m-1)/m;return m>=(2*r+1)*(H+4*r*k+2*r);};
        U lo=1,hi=a;assert(oldExcluded(hi));while(lo<hi){U mid=(lo+hi)/2;if(oldExcluded(mid))hi=mid;else lo=mid+1;}U oldCut=lo-1;
        Z inv,modulus=N,twoL=2*t.L;assert(mpz_invert(inv.get_mpz_t(),twoL.get_mpz_t(),modulus.get_mpz_t()));
        U ex=modui(inv*(t.d+5*t.L),N);
        std::set<U> oldExtra;if(ex>oldCut&&ex<=a)oldExtra.insert(ex);for(U s=1;s<2*B&&2*r*s<=vc;s++)oldExtra.insert(a+s);
        U H3=bits(4*maxC+t.c*(N+1));
        auto massCut=[&](U m){return m>=3*(H3+2*((E+m-1)/m));};
        lo=1;hi=a;assert(massCut(hi));while(lo<hi){U mid=(lo+hi)/2;if(massCut(mid))hi=mid;else lo=mid+1;}U ordinary=std::min(lo-1,oldCut);
        auto resonant=[&](U m){Z C=t.d+t.L*(5-2*Z(m)),mid=C-t.c*N;if(mid==0)return true;U y=v2(mid),z=v2(3*C);U x0=(E+vc)%m,x1=(a+y)%m,x2=z%m;return x0==x1||x0==x2||x1==x2;};
        // Above the mass threshold, a binary-valuation collision is necessary.
        std::set<U> extra;
        if(ordinary<oldCut){
            U l=ordinary+1,h=oldCut;
            divisorsIn(E+vc,l,h,extra);
            if(vc>0){ // C and C-cN are odd.
                divisorsIn(a,l,h,extra);divisorsIn(E-a+vc,l,h,extra);
            }else{
                // At the original feeder c=1 and C-cN!=0; its valuation <= H3.
                for(U j=0;j<=H3;j++){divisorsIn(a+j,l,h,extra);divisorsIn(E-a-j,l,h,extra);}
            }
        }
        for(auto it=extra.begin();it!=extra.end();){if(!resonant(*it))it=extra.erase(it);else ++it;}
        for(U m:oldExtra)if(!massCut(m)||resonant(m))extra.insert(m);
        std::vector<bool> blocked(ordinary+1,false);U sieve=0,sparse=0,full=0;
        for(auto p:primes){U cm=modui(t.c,p.p),dm=modui(t.d,p.p),lm=modui(t.L,p.p);for(U m=p.residue;m<=ordinary;m+=p.period){if(!blocked[m]&&(cm*p.ap+dm+lm*((5+p.p-2*(m%p.p)%p.p)%p.p))%p.p){blocked[m]=true;sieve++;}}}
        std::vector<std::pair<U,Target>> parents;
        auto check=[&](U m){
            Z C=t.d+t.L*(5-2*Z(m)),D=pow2(m)+3;
            Z S=t.c*reduce2(E,m,D)+(C-t.c*N)*reduce2(a,m,D)+3*C;
            if(!mpz_divisible_p(S.get_mpz_t(),D.get_mpz_t())){sparse++;return;}
            full++;
            Z LD=t.L*D,AP=APmodBig(r,a,LD),F=t.c*AP+C;
            if(!mpz_divisible_p(F.get_mpz_t(),LD.get_mpz_t()))return;
            // Exact congruence plus an independently bounded positive odd quotient >=3.
            if(bits(3*LD+abs(C))>M-1){std::cout<<path<<" quotient lower bound unavailable m="<<m<<"\n";cutoffFailure=true;return;}
            parents.emplace_back(m-1,Target{pow2(m)*t.c,pow2(m)*C,LD});
        };
        for(U m=1;m<=ordinary;m++)if(!blocked[m])check(m);
        for(U m:extra)check(m);
        assert(sieve+sparse+full==ordinary+extra.size());
        std::cout<<path<<" bitsUpper="<<M<<" oldCut="<<oldCut<<" ordinary="<<ordinary<<" resonantExtras="<<extra.size()<<" sieve="<<sieve<<" sparse="<<sparse<<" exact="<<full<<" parents=";
        for(auto& p:parents)std::cout<<p.first<<",";
        std::cout<<"\n"<<std::flush;
        if(parents.empty())++leaves;
        for(auto& p:parents){++edges;walk(p.second,path+"/"+std::to_string(p.first));}
    };
    walk({1,0,1},"r="+std::to_string(r));
    std::cout<<"nodes="<<nodes<<" leaves="<<leaves<<" edges="<<edges<<" cutoffFailure="<<cutoffFailure<<"\n";
    return cutoffFailure?3:0;
}
