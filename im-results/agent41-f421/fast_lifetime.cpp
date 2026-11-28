// Fast exact evaluator of the normalized secondary P-run lifetime recurrence.
// Author: Agent 41, 2026-11-28. C++17 + Boost.Multiprecision.
// Invariant (far-to-near):
//   advance: delete all initial 1s as they are encountered from far to near;
//   each survivor l becomes (l-1) * 2^(number of earlier deletions);
//   append 2^(total_deletions+1).
// Global decrement + ordered zero deletion + suffix doubling realizes this
// recurrence in O((time + deletions) log(current_length)) expected treap ops.
// All arithmetic is exact cpp_int. Randomness only determines tree shape.
#include <boost/multiprecision/cpp_int.hpp>
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <random>
#include <string>
#include <vector>
using boost::multiprecision::cpp_int;
using std::uint64_t;

struct Node {
    cpp_int v,mn,mul,add;
    int n;
    uint64_t priority;
    Node *l,*r;
    Node(cpp_int val,uint64_t pr)
      :v(val),mn(val),mul(1),add(0),n(1),priority(pr),l(nullptr),r(nullptr){}
};
int sz(Node*x){return x?x->n:0;}
void update(Node*x){
    if(!x)return;
    x->n=1+sz(x->l)+sz(x->r);
    x->mn=x->v;
    if(x->l && x->l->mn<x->mn)x->mn=x->l->mn;
    if(x->r && x->r->mn<x->mn)x->mn=x->r->mn;
}
void affine(Node*x,const cpp_int& m,const cpp_int& a){
    if(!x)return;
    x->v=m*x->v+a; x->mn=m*x->mn+a;
    x->mul=m*x->mul; x->add=m*x->add+a;
}
void push(Node*x){
    if(!x || (x->mul==1 && x->add==0))return;
    affine(x->l,x->mul,x->add);affine(x->r,x->mul,x->add);
    x->mul=1; x->add=0;
}
Node* merge(Node*a,Node*b){
    if(!a)return b;
    if(!b)return a;
    if(a->priority>b->priority){
        push(a);a->r=merge(a->r,b);update(a);return a;
    } else {
        push(b);b->l=merge(a,b->l);update(b);return b;
    }
}
void split(Node*x,int k,Node*&a,Node*&b){
    if(!x){a=b=nullptr;return;}
    push(x);
    if(sz(x->l)>=k){
        split(x->l,k,a,x->l);b=x;update(b);
    }else{
        split(x->r,k-sz(x->l)-1,x->r,b);a=x;update(a);
    }
}
int firstZero(Node*x){
    if(!x || x->mn!=0)std::abort();
    push(x);
    if(x->l && x->l->mn==0)return firstZero(x->l);
    if(x->v==0)return sz(x->l);
    return sz(x->l)+1+firstZero(x->r);
}
void traverse(Node*x,std::vector<cpp_int>&out){
    if(!x)return;
    push(x);
    traverse(x->l,out);out.push_back(x->v);traverse(x->r,out);
}
struct State {
    Node *root=nullptr;
    uint64_t deaths=0;
    std::mt19937_64 rng{UINT64_C(0xF421BEE6C0FFEE)};
    void birth(const cpp_int&v){root=merge(root,new Node(v,rng()));}
    explicit State(const std::vector<cpp_int>&initial){
        for(const auto&v:initial){if(v<=0)std::abort();birth(v);}
    }
    int advance(){
        affine(root,cpp_int(1),cpp_int(-1));
        int removed=0;
        while(root && root->mn==0){
            int ix=firstZero(root);
            Node *L,*R,*D,*S;
            split(root,ix,L,R);split(R,1,D,S);
            if(!D || sz(D)!=1 || D->v!=0)std::abort();
            delete D;
            affine(S,cpp_int(2),cpp_int(0));
            root=merge(L,S);
            ++removed;
        }
        birth(cpp_int(1)<<(removed+1));
        deaths+=removed;
        return removed;
    }
    std::vector<cpp_int> sequence(){
        std::vector<cpp_int>v;v.reserve(sz(root));
        traverse(root,v);return v;
    }
};
int main(int argc,char**argv){
    int steps=argc>1?std::stoi(argv[1]):32750;
    if(steps<0)std::abort();
    State s({327661,14,30,6,22,14,1,2});
    uint64_t hist[128]={};
    for(int i=0;i<steps;i++){
        int d=s.advance();if(d>=128)std::abort();hist[d]++;
        if(argc>2 && std::string(argv[2])=="--progress" && (i+1)%10000==0)
            std::cerr<<i+1<<" "<<sz(s.root)<<"\n";
    }
    std::cout<<"steps="<<steps<<" length="<<sz(s.root)<<" deaths="<<s.deaths<<"\n";
    std::cout<<"hist:";for(int d=0;d<128;d++)if(hist[d])std::cout<<" "<<d<<":"<<hist[d];std::cout<<"\n";
    auto v=s.sequence();
    std::cout<<"prefix:";for(int i=0;i<std::min(10,(int)v.size());i++)std::cout<<" "<<v[i];std::cout<<"\n";
    std::cout<<"suffix:";for(int i=std::max(0,(int)v.size()-10);i<(int)v.size();i++)std::cout<<" "<<v[i];std::cout<<"\n";
    if(argc>2 && std::string(argv[2])=="--dump")for(auto&x:v)std::cout<<x<<"\n";
    return 0;
}
