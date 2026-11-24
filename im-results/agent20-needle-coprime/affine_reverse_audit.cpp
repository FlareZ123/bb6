#include <gmpxx.h>
#include <algorithm>
#include <cassert>
#include <iostream>
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
struct Prime{U p,residue,period,ap;};
struct Target{Z c,d,L;};
int main(int argc,char**argv){
    if(argc!=2)return 2;U r=std::stoul(argv[1]);assert(r>=4&&r<=8);
    U N=1;for(U i=0;i<r;i++)N*=9;U a=(N+5)/2,M=2*r*a;
    Z A=pow2(a),top=pow2(M)-N,den=A+3,P;
    assert(mpz_divisible_p(top.get_mpz_t(),den.get_mpz_t()));
    mpz_divexact(P.get_mpz_t(),top.get_mpz_t(),den.get_mpz_t());
    Z AP=A*P;A=0;P=0;top=0;den=0;
    std::vector<Prime> primes;
    for(U p=5;p<=10000;p+=2){bool prime=true;for(U d=3;d*d<=p;d+=2)if(p%d==0){prime=false;break;}if(!prime)continue;
        U residue=0,period=0,t=1;do{period++;t=t*2%p;if(t==p-3)residue=period;}while(t!=1);
        if(residue)primes.push_back({p,residue,period,APmod(r,a,p)});
    }
    U nodes=0,leaves=0,edges=0;bool rootReached=false,cutoffFailure=false;
    std::function<void(const Target&,const std::string&)> walk=[&](const Target& t,const std::string& path){
        ++nodes;
        assert(t.c>0&&t.L>0&&mpz_odd_p(t.L.get_mpz_t())&&mpz_even_p(t.d.get_mpz_t())&&modui(t.L,3)!=0);
        assert(mpz_popcount(t.c.get_mpz_t())==1);
        Z twiceNum=t.c*AP+t.d;
        assert(mpz_divisible_p(twiceNum.get_mpz_t(),t.L.get_mpz_t()));
        Z twiceB=twiceNum/t.L;
        assert(twiceB>=6&&mpz_even_p(twiceB.get_mpz_t())&&twiceB<=AP);
        if(twiceB==6){std::cout<<path<<" ROOT\n";rootReached=true;return;}
        Z bound=abs(t.d)+t.L*(2*M+5)+t.c*N+1;
        U H=mpz_sizeinbase(bound.get_mpz_t(),2)+4,B=H+4*r+4;
        U vc=mpz_scan1(t.c.get_mpz_t(),0);
        if(a<(4*r+1)*B){std::cout<<path<<" cutoff unavailable (B="<<B<<")\n";cutoffFailure=true;return;}
        auto lowExcluded=[&](U m){U k=(a+m-1)/m;return m>=(2*r+1)*(H+4*r*k+2*r);};
        U lo=1,hi=a;assert(lowExcluded(hi));
        while(lo<hi){U mid=(lo+hi)/2;if(lowExcluded(mid))hi=mid;else lo=mid+1;}
        U cutoff=lo-1;
        Z inv,modulus=N,twoL=2*t.L;
        assert(mpz_invert(inv.get_mpz_t(),twoL.get_mpz_t(),modulus.get_mpz_t()));
        Z exz=inv*(t.d+5*t.L);U ex=modui(exz,N);
        std::vector<U> extra;
        if(ex>cutoff&&ex<=a)extra.push_back(ex);
        for(U s=1;s<2*B&&2*r*s<=vc;s++)extra.push_back(a+s);
        std::vector<bool> blocked(cutoff+1,false);U sieve=0,sparse=0,full=0;
        for(auto p:primes){U cm=modui(t.c,p.p),dm=modui(t.d,p.p),lm=modui(t.L,p.p);
            for(U m=p.residue;m<=cutoff;m+=p.period){
                if(!blocked[m]&&(cm*p.ap+dm+lm*((5+p.p-2*(m%p.p)%p.p)%p.p))%p.p){blocked[m]=true;sieve++;}
            }
        }
        std::vector<std::pair<U,Target>> parents;
        auto check=[&](U m){
            Z D=pow2(m)+3,C=t.d+t.L*(5-2*Z(m));
            Z S=t.c*reduce2((2*r+1)*a,m,D)+(C-t.c*N)*reduce2(a,m,D)+3*C;
            if(!mpz_divisible_p(S.get_mpz_t(),D.get_mpz_t())){sparse++;return;}
            full++;
            Z F=twiceNum+t.L*(5-2*Z(m)),LD=t.L*D;
            if(F<3*LD||!mpz_divisible_p(F.get_mpz_t(),LD.get_mpz_t()))return;
            Z odd=F/LD;assert(mpz_odd_p(odd.get_mpz_t()));
            Z twiceParent=pow2(m)*odd;
            assert(twiceParent<twiceB);
            parents.emplace_back(m-1,Target{pow2(m)*t.c,pow2(m)*C,LD});
        };
        for(U m=1;m<=cutoff;m++)if(!blocked[m])check(m);
        for(U m:extra)check(m);
        assert(sieve+sparse+full==cutoff+extra.size());
        std::cout<<path<<" bits="<<mpz_sizeinbase(twiceB.get_mpz_t(),2)<<" B="<<B<<" cutoff="<<cutoff<<" extra=";
        for(U m:extra)std::cout<<m<<",";
        std::cout<<" sieve="<<sieve<<" sparse="<<sparse<<" exact="<<full<<" parents=";
        for(auto& p:parents)std::cout<<p.first<<",";
        std::cout<<"\n"<<std::flush;
        if(parents.empty())++leaves;
        for(auto& p:parents){++edges;walk(p.second,path+"/"+std::to_string(p.first));}
    };
    walk({1,0,1},"r="+std::to_string(r));
    std::cout<<"nodes="<<nodes<<" leaves="<<leaves<<" edges="<<edges<<" rootReached="<<rootReached<<" cutoffFailure="<<cutoffFailure<<"\n";
    return cutoffFailure?3:0;
}
