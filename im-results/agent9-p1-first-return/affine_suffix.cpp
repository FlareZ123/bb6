// Exact half-depth affine support, reusing Agent23/Agent9's existing
// modular period reducer and high-to-low bitmap construction.
#include "../agent9-p1-reverse-block/reduced_jump.hpp"
#include <chrono>
#include <iostream>
#include <map>
#include <utility>
#include <vector>
#include <cstdint>
#include <cstdlib>
using U=uint64_t;
using W=uint32_t;
using Prefix=std::pair<W,W>;
using Row=std::pair<W,std::vector<Prefix>>;
static void visit(unsigned k,unsigned j,W r,W a,W B,std::map<W,std::vector<Prefix>>& groups){
    if(j==k){groups[r].push_back({a,B});return;}
    W H=W(1)<<j,t=a&1;
    visit(k,j+1,r+H*t,(a+t*B)/2,B,groups);
    W C=a+r+j+3,S=B+H,u=C&1;
    visit(k,j+1,r+H*u,(C+u*S)/2,S,groups);
}
static W inverse(W B){
    W x=1;
    for(int i=0;i<5;i++)x*=W(2)-B*x;
    if(B*x!=1)throw std::logic_error("odd inverse");
    return x;
}
static void count(unsigned K,unsigned k){
    if(k<2||k>26||K<k||K-k>k||K-k>26)throw std::invalid_argument("depth");
    unsigned d=K-k;
    std::map<W,std::vector<Prefix>> groups;
    visit(k,2,2,1,1,groups);
    std::vector<Row> rows;
    for(auto &g:groups)rows.push_back({g.first,std::move(g.second)});
    U total=0,visits=0,plan=0,collapsed=0;
    auto start=std::chrono::steady_clock::now();
    bb6_jump::bitmap_plan=true;
    #pragma omp parallel for schedule(dynamic,1) reduction(+:total,visits,plan,collapsed)
    for(int i=0;i<int(rows.size());++i){
        const auto &row=rows[i];
        bb6_jump::Plan p(int(row.first+k+3),int(d));
        W mask=p.modulus-1;
        std::vector<U> bits((U(p.modulus)+63)/64);
        for(auto [a,B]:row.second){
            W I=inverse(B),phase=(W(0)-a)*I;
            for(W s:p.residues){
                W T=(s*I+phase)&mask;
                bits[T>>6]|=U(1)<<(T&63);
            }
        }
        U n=0;for(U b:bits)n+=__builtin_popcountll(b);
        total+=n<<(d-p.exponent);
        visits+=U(p.residues.size())*row.second.size();
        plan+=p.residues.size();collapsed+=d-p.exponent;
    }
    auto ms=std::chrono::duration_cast<std::chrono::milliseconds>(
      std::chrono::steady_clock::now()-start).count();
    std::cout<<"K "<<K<<" k "<<k<<" rows "<<rows.size()<<" count "<<total
      <<" totalEven "<<(U(1)<<(K-1))<<" visits "<<visits
      <<" plan "<<plan<<" collapsed "<<collapsed<<" ms "<<ms<<std::endl;
}
int main(int argc,char**argv){
    for(int i=1;i<argc;i++){unsigned K=std::stoul(argv[i]);count(K,(K+1)/2);}
}
