#include <gmpxx.h>
#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>
using U=unsigned long;
using Z=mpz_class;
static Z pow2(U n){Z z=1;mpz_mul_2exp(z.get_mpz_t(),z.get_mpz_t(),n);return z;}
static Z pow3(U n){Z z;mpz_ui_pow_ui(z.get_mpz_t(),3,n);return z;}
static Z reduce2(U e,U m,const Z& D){
    U q=e/m,s=e%m; Z z;
    if(q<=m/2+16) z=pow3(q); else {Z three=3;mpz_powm_ui(z.get_mpz_t(),three.get_mpz_t(),q,D.get_mpz_t());}
    mpz_mul_2exp(z.get_mpz_t(),z.get_mpz_t(),s);
    if(q&1) z=-z;
    return z;
}
static U isqrt(U x){Z z=x,root;mpz_sqrt(root.get_mpz_t(),z.get_mpz_t());return root.get_ui();}
static U modpow(U b,U e,U m){U x=1;while(e){if(e&1)x=x*b%m;b=b*b%m;e>>=1;}return x;}
static U APmod(U r,U a,U p){U A=modpow(2,a,p),P=0,n=1;for(U i=0;i<r;i++){P=(A*A%p*P+n*(A+p-3)%p)%p;n=n*9%p;}return A*P%p;}
int main(int argc,char**argv){
    if(argc!=2)return 2; U r=std::stoul(argv[1]);assert(r>=4&&r<=11);
    U N=1;for(U i=0;i<r;i++)N*=9;U a=(N+5)/2;
    U cutoff=isqrt(64*r*r*a-1);
    cutoff=std::min(cutoff,a-1);
    std::vector<bool> blocked(cutoff+1,false);
    U sieve=0;
    for(U p=5;p<=10000;p+=2){bool prime=true;for(U d=3;d*d<=p;d+=2)if(p%d==0){prime=false;break;}if(!prime)continue;
        U residue=0,period=0,t=1;
        do {period++;t=t*2%p;if(t==p-3)residue=period;}while(t!=1);
        if(!residue)continue;
        U ap=APmod(r,a,p);
        for(U m=residue;m<=cutoff;m+=period){if(!blocked[m]&&(ap+5+p-2*(m%p)%p)%p){blocked[m]=true;sieve++;}}
    }
    U sparse=0,full=0;std::vector<U> parents;
    auto start=std::chrono::steady_clock::now();
    for(U m=1;m<=cutoff;m++){
        if(blocked[m])continue;
        Z D=pow2(m)+3,C=5-2*Z(m);
        Z s=reduce2((2*r+1)*a,m,D)+(C-Z(N))*reduce2(a,m,D)+3*C;
        if(!mpz_divisible_p(s.get_mpz_t(),D.get_mpz_t())){sparse++;continue;}
        full++;
        Z A=reduce2(a,m,D)%D,P=0,n=1;
        for(U i=0;i<r;i++){P=(A*A*P+n*(A-3))%D;n*=9;}
        Z exact=A*P+C;
        if(mpz_divisible_p(exact.get_mpz_t(),D.get_mpz_t()))parents.push_back(m-1);
    }
    std::cout<<"r="<<r<<" a="<<a<<" max_m="<<cutoff<<" sieve="<<sieve<<" sparse="<<sparse<<" full="<<full<<" parents=";
    for(auto v:parents)std::cout<<v<<",";
    std::cout<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"\n";
    assert(sieve+sparse+full==cutoff);
}
