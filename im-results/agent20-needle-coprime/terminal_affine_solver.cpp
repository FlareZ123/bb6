// Exact compact reverse-tree solver for the shifted Space Needle map.
// Build: g++ -O3 -std=c++17 terminal_affine_solver.cpp -lgmpxx -lgmp -o terminal_affine_solver
// Use: ./terminal_affine_solver K [node_limit]; optional limit reports INCOMPLETE.
// Mathematical correctness: TerminalAffineRotation.lean and TerminalAffine.md.
#include <gmpxx.h>
#include <algorithm>
#include <cassert>
#include <climits>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

using U = unsigned long;
using Z = mpz_class;
struct Node { U n; Z L, d; };
struct Parent { U m; Node node; };

static Z pow2(U n) { Z z=1; mpz_mul_2exp(z.get_mpz_t(),z.get_mpz_t(),n); return z; }
static Z pow3(U n) { Z z; mpz_ui_pow_ui(z.get_mpz_t(),3,n); return z; }
static U bits(const Z& z) { return mpz_sizeinbase(z.get_mpz_t(),2); }
static U checked_add(U a,U b) { if(a>ULONG_MAX-b) throw std::overflow_error("exponent overflow"); return a+b; }
static bool power_ge(U n,const Z& z) {
    if(z<=0) return true;
    const U B=bits(z);
    return B<=n || (B-1==n && mpz_popcount(z.get_mpz_t())==1);
}
static bool is_root(const Node& x) {
    Z t=6*x.L-x.d;
    return t>0 && bits(t)-1==x.n && mpz_popcount(t.get_mpz_t())==1;
}
static Z correction(const Node& x,U m) { return x.d+x.L*(5-Z(m)*2); }
static bool exact_parent(const Node& x,U m,Parent& out) {
    Z C=correction(x,m), D=pow2(m)+3, modulus=x.L*D;
    // Avoid power 2^n: the quotient is >=3 iff 2^n>=3LD-C.
    if(!power_ge(x.n,3*modulus-C)) return false;
    Z residue, two=2;
    mpz_powm_ui(residue.get_mpz_t(),two.get_mpz_t(),x.n,modulus.get_mpz_t());
    residue+=C;
    if(!mpz_divisible_p(residue.get_mpz_t(),modulus.get_mpz_t())) return false;
    // Quotient is odd (n>0, d even, L,D odd).
    Z nextd=C; mpz_mul_2exp(nextd.get_mpz_t(),nextd.get_mpz_t(),m);
    out={m,{checked_add(x.n,m),std::move(modulus),std::move(nextd)}};
    assert(out.node.d<2*out.node.L);
    return true;
}

// The ordinary cutoff m < H + 2 floor(n/m) + 2 is monotone in m.
// Rearrange to avoid overflowing the addition and multiplication.
static bool ordinary_exact(U n,U H,U m) {
    if(m<=H || m-H<=1) return true;
    // m-H-2 < 2 floor(n/m).
    return (m-H-2)/2 < n/m;
}
static U ordinary_cut(const Node& x,U H,U K) {
    U lo=0,hi=K;
    while(lo<hi) {
        U mid=lo+(hi-lo)/2+1;
        if(ordinary_exact(x.n,H,mid)) lo=mid; else hi=mid-1;
    }
    return lo;
}
// Exact cancellation: n=m*k, k even, k(d+5L+3^k)=2Ln.
// The left hand side is strictly increasing wherever it is positive;
// comparison with the positive RHS is monotone even if it starts negative.
static U unique_exception(const Node& x,U H,U K,U cut) {
    if(cut>=K) return 0;
    U min_m=std::max<U>(4,cut+1);
    U hi=std::min(H-1,x.n/min_m)/2, lo=1;
    if(hi<lo) return 0;
    Z rhs=2*x.L*x.n, base=x.d+5*x.L;
    auto lhs=[&](U half)->Z { U k=half*2; Z y=base+pow3(k); return y*k; };
    while(lo<hi) { U mid=lo+(hi-lo)/2; if(lhs(mid)>=rhs) hi=mid; else lo=mid+1; }
    U k=2*lo;
    if(lhs(lo)!=rhs || x.n%k!=0) return 0;
    U m=x.n/k;
    return (m>=min_m && m<=K)?m:0;
}

static std::vector<Parent> parents(const Node& x,U K) {
    assert(x.n>0 && x.L>0 && mpz_odd_p(x.L.get_mpz_t()) && mpz_even_p(x.d.get_mpz_t()) && x.d<2*x.L);
    Z absd=abs(x.d); U H=bits(absd+x.L*(2*Z(K)+5));
    U cut=ordinary_cut(x,H,K);
    std::vector<Parent> out;
    Parent p;
    for(U m=1;m<=cut;++m) if(exact_parent(x,m,p)) out.push_back(std::move(p));
    U m=unique_exception(x,H,K,cut);
    if(m && exact_parent(x,m,p)) out.push_back(std::move(p));
    return out;
}

// Small regression only: materialized independent inverse equation.
static void regression(U maxK) {
    for(U K=2;K<=maxK;++K) {
        std::vector<Node> stack{{K+1,1,0}};
        while(!stack.empty()) {
            Node x=std::move(stack.back()); stack.pop_back();
            Z b=(pow2(x.n)+x.d)/(2*x.L);
            auto pp=parents(x,K);
            std::vector<U> exact;
            for(U m=1;m<=K;++m) {
                Z D=pow2(m)+3,F=2*b+5-2*Z(m);
                if(F>=3*D && mpz_divisible_p(F.get_mpz_t(),D.get_mpz_t())) exact.push_back(m);
            }
            if(exact.size()!=pp.size()) throw std::runtime_error("wrong parent count");
            for(size_t i=0;i<exact.size();++i) {
                if(exact[i]!=pp[i].m) throw std::runtime_error("wrong parent valuation");
                const Node &y=pp[i].node;
                Z p=(pow2(y.n)+y.d)/(2*y.L);
                Z expected=pow2(exact[i]-1)*((2*b+5-2*Z(exact[i]))/(pow2(exact[i])+3));
                if(p!=expected || p>=b) throw std::runtime_error("wrong parent value");
                if(!is_root(y)) stack.push_back(y);
            }
        }
    }
    std::cout<<"complete regression through K="<<maxK<<" passed\n";
}

int main(int argc,char**argv) {
    if(argc>=2 && std::string(argv[1])=="--regression") { regression(argc>2?std::stoul(argv[2]):12); return 0; }
    if(argc<2 || argc>3) { std::cerr<<"usage: terminal_affine_solver K [node_limit]\n"; return 2; }
    U K=std::stoul(argv[1]),limit=argc==3?std::stoul(argv[2]):ULONG_MAX;
    if(K<2 || K==ULONG_MAX) throw std::invalid_argument("K must be between 2 and ULONG_MAX-1");
    std::vector<Node> stack{{K+1,1,0}};
    U nodes=0,edges=0,leaves=0,maxPending=1;
    while(!stack.empty() && nodes<limit) {
        Node x=std::move(stack.back()); stack.pop_back(); ++nodes;
        if(is_root(x)) { std::cout<<"REACHABLE K="<<K<<" nodes="<<nodes<<"\n"; return 0; }
        auto pp=parents(x,K);
        if(pp.empty()) ++leaves;
        edges=checked_add(edges,pp.size());
        for(auto &p:pp) stack.push_back(std::move(p.node));
        maxPending=std::max<U>(maxPending,stack.size());
    }
    std::cout<<(stack.empty()?"EXCLUDED":"INCOMPLETE")<<" K="<<K<<" nodes="<<nodes<<" edges="<<edges<<" leaves="<<leaves<<" pending="<<stack.size()<<" maxPending="<<maxPending<<"\n";
}
