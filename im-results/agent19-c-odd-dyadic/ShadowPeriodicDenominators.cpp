// Necessary-condition census for periodic root32 shadow costs.
// Requires C++17 plus compiler support for unsigned __int128.
#include <iostream>
#include <vector>
#include <numeric>
#include <cstdlib>
#include <cstdint>
using U=uint64_t;
U powmod(U b,U e,U m){
    U r=1;
    while(e){
        if(e&1)r=(__uint128_t)r*b%m;
        b=(__uint128_t)b*b%m;
        e>>=1;
    }
    return r;
}
int main(int argc,char**argv){
    U maxq=argc>1?std::strtoull(argv[1],nullptr,10):200000;
    U candidates=0,pass=0,qs=0;
    for(U q=211;q<=maxq;q+=422){
        std::vector<bool> seen(q);
        bool has=false;
        for(U a=1;a<q;a++){
            if(seen[a]||std::gcd(a,q)!=1)continue;
            U x=a,b=0,L=0,odd=0;
            do{
                seen[x]=true;
                if(x&1)odd=x;
                b++;
                L+=2*x>=q;
                x=2*x%q;
            }while(x!=a);
            U W=3*b+L;
            if(W%2||211*W%q)continue;
            candidates++;
            U k=211*W/q;
            if(k%2)continue;
            U h=(powmod(2,b,q*211)-1)/q;
            if(k%211!=5*h%211)continue;
            pass++;
            has=true;
            std::cout<<"q="<<q<<" a="<<odd<<" b="<<b<<" L="<<L
                     <<" W="<<W<<" k="<<k<<" h="<<h<<'\n';
        }
        qs+=has;
    }
    std::cerr<<"candidates="<<candidates<<" pass="<<pass<<" qwithpass="<<qs<<"\n";
}
