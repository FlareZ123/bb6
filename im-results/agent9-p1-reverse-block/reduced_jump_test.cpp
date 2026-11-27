#include "reduced_jump.hpp"
#include <cassert>
#include <chrono>
#include <iostream>
#include <random>
using bb6_jump::Plan; using bb6_jump::U; using bb6_jump::W;
static std::vector<int> direct(int q,int r,U Y) {
    W M=W(1)<<r,mask=M-1;
    std::vector<bool> seen(M);
    std::vector<W> rs{W(Y)&mask}; seen[rs[0]]=true;
    for(int j=0;j<r;j++) {
        W shift=W((U(q)+j)<<j)&mask;
        auto count=rs.size();
        for(std::size_t i=0;i<count;i++) {
            W c=(rs[i]-shift)&mask;
            if(!seen[c]) { seen[c]=true;rs.push_back(c); }
        }
    }
    std::sort(rs.begin(),rs.end());
    std::vector<int> a;
    for(U base=0;base<U(q);base+=M)
        for(W x:rs) { if(base+x>=U(q)) break; a.push_back(int(base+x)); }
    return a;
}
static std::vector<int> literal(int q,int r,U Y) {
    std::vector<bool> seen(q+r,true);
    for(int j=r;j-- >0;) {
        std::vector<bool> a(q+j);
        U y=(Y>>j)&1, C=q+j;
        for(U z=0;z<seen.size();z++) if(seen[z]&&2*z+y<2*C)
            a[(2*z+y)%C]=true;
        seen=std::move(a);
    }
    std::vector<int> out;
    for(int c=0;c<q;c++) if(seen[c]) out.push_back(c);
    return out;
}
static std::vector<int> lift(const Plan& p,U y) {
    std::vector<int> a; p.lift(y,[&](int c){a.push_back(c);});return a;
}
int main() {
    std::uint64_t checked=0;
    for(int q=0;q<=128;q++) for(int r=0;r<=9;r++) {
        Plan p(q,r);
        for(U Y=0;Y<(U(1)<<r);Y++) {
            assert(lift(p,Y)==direct(q,r,Y));
            assert(lift(p,Y)==literal(q,r,Y)); ++checked;
        }
    }
    std::mt19937_64 rng(45);
    for(int i=0;i<1000;i++) {
        int q=1+rng()%10000,r=1+rng()%15;U y=rng()&((U(1)<<r)-1);
        Plan p(q,r);assert(lift(p,y)==direct(q,r,y));++checked;
    }
    std::cout<<checked<<" exact cases passed\n";
    for(auto F : {1000024,1310744,45400024,45352466,100000001}) {
        int r=22,q=F-r;
        const auto start=std::chrono::steady_clock::now();
        Plan p(q,r);
        auto prep=std::chrono::steady_clock::now();
        U sum=0,expected=0;double baseline=0;
        for(int i=0;i<8;i++) {
            U y=rng()&((U(1)<<r)-1);
            auto t=std::chrono::steady_clock::now();
            auto old=direct(q,r,y);
            baseline+=std::chrono::duration<double>(std::chrono::steady_clock::now()-t).count();
            expected+=old.size();
            auto a=lift(p,y);assert(a==old);sum+=a.size();
        }
        auto end=std::chrono::steady_clock::now();
        std::cout<<"F="<<F<<" exponent="<<p.exponent<<" support="<<p.residues.size()
                 <<" prep="<<std::chrono::duration<double>(prep-start).count()
                 <<" eight baseline="<<baseline<<" reduced incl prep="
                 <<std::chrono::duration<double>(end-start).count()-baseline
                 <<" output="<<sum<<"\n";
        assert(sum==expected);
    }
}
