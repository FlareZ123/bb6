// Exact event-driven F421 secondary P and Q recurrence from the authentic
// (two protected far rows + positive normalized P-lifetime suffix) seed.
// C++17, Boost.Multiprecision. Numerical evidence, not a Lean certificate.
//
// Each suffix treap row stores P lifetime L and augmented Q credit
// R_i = Q_i + 2^(i+2), i=0 for first suffix row. At every cycle:
//   decrement all L; each L=0 row disappears, transferring R to the next row;
//   double the P lifetimes of all rows to its right;
//   append (2^(number of deletions+1), b+2^oldTotalCells+trailingCredit);
//   b=3071 initially, then 3*2^totalCells-1.
// This implements the source-level Q merger theorem F421AugmentedQ.sNextAug,
// conditional on the exact source guards verified separately.
#include <boost/multiprecision/cpp_int.hpp>
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <random>
#include <string>
#include <vector>
using boost::multiprecision::cpp_int;
struct Node {
    cpp_int life, minLife, mul, add, credit;
    int n=1;
    std::uint64_t pr;
    Node *left=nullptr,*right=nullptr;
    Node(const cpp_int& l,const cpp_int& r,std::uint64_t p)
      :life(l),minLife(l),mul(1),add(0),credit(r),pr(p){}
};
int sz(Node* x){return x?x->n:0;}
void recalc(Node*x){
    if(!x)return;
    x->n=1+sz(x->left)+sz(x->right);
    x->minLife=x->life;
    if(x->left && x->left->minLife<x->minLife)x->minLife=x->left->minLife;
    if(x->right && x->right->minLife<x->minLife)x->minLife=x->right->minLife;
}
void aff(Node*x,const cpp_int&m,const cpp_int&a){
    if(!x)return;
    x->life=m*x->life+a;x->minLife=m*x->minLife+a;
    x->mul=m*x->mul;x->add=m*x->add+a;
}
void push(Node*x){
    if(!x || (x->mul==1 && x->add==0))return;
    aff(x->left,x->mul,x->add);aff(x->right,x->mul,x->add);
    x->mul=1;x->add=0;
}
Node* join(Node*a,Node*b){
    if(!a)return b;
    if(!b)return a;
    if(a->pr>b->pr){push(a);a->right=join(a->right,b);recalc(a);return a;}
    push(b);b->left=join(a,b->left);recalc(b);return b;
}
void split(Node*x,int k,Node*&a,Node*&b){
    if(!x){a=b=nullptr;return;}
    push(x);
    if(sz(x->left)>=k){split(x->left,k,a,x->left);b=x;recalc(b);}
    else {split(x->right,k-sz(x->left)-1,x->right,b);a=x;recalc(a);}
}
int firstZero(Node*x){
    if(!x||x->minLife!=0)std::abort();
    push(x);
    if(x->left&&x->left->minLife==0)return firstZero(x->left);
    if(x->life==0)return sz(x->left);
    return sz(x->left)+1+firstZero(x->right);
}
void addFirstCredit(Node*x,const cpp_int&v){
    if(!x)std::abort();
    push(x);
    if(x->left)addFirstCredit(x->left,v);else x->credit+=v;
}
void flatten(Node*x,std::vector<Node*>&out){
    if(!x)return;
    push(x);flatten(x->left,out);out.push_back(x);flatten(x->right,out);
}
struct Engine {
    std::mt19937_64 rng{UINT64_C(0xF421BEE6C0FFEE)};
    Node* root=nullptr;
    unsigned steps=0;
    std::uint64_t deaths=0;
    void append(const cpp_int&l,const cpp_int&r){
        if(l<=0||r<=0)std::abort();
        root=join(root,new Node(l,r,rng()));
    }
    Engine(){
        const int l[]={327661,14,30,6,22,14,1,2};
        const int q[]={3145735,3148774,3054,3038,4031,3967,767,1535};
        for(int i=0;i<8;i++)
            append(cpp_int(l[i]),cpp_int(q[i])+(cpp_int(1)<<(i+2)));
    }
    int advance(){
        const int oldTotal=sz(root)+2;
        const cpp_int b=steps==0?cpp_int(3071):
           3*(cpp_int(1)<<oldTotal)-1;
        aff(root,cpp_int(1),cpp_int(-1));
        int count=0;
        cpp_int trailing=0;
        while(root&&root->minLife==0){
            Node *L,*R,*D,*S;
            int i=firstZero(root);
            split(root,i,L,R);split(R,1,D,S);
            if(!D||D->life!=0||sz(D)!=1)std::abort();
            cpp_int r=D->credit;
            delete D;
            if(S)addFirstCredit(S,r);else trailing+=r;
            aff(S,cpp_int(2),cpp_int(0));
            root=join(L,S);
            ++count;
        }
        append(cpp_int(1)<<(count+1),
            b+(cpp_int(1)<<oldTotal)+trailing);
        deaths+=count;++steps;
        return count;
    }
    std::vector<Node*> rows() {
        std::vector<Node*> v;v.reserve(sz(root));flatten(root,v);return v;
    }
};
int main(int argc,char**argv){
    const int k=argc>1?std::stoi(argv[1]):32750;
    if(k<0)std::abort();
    Engine s;
    std::uint64_t hist[128]={};
    for(int i=0;i<k;i++){
        int d=s.advance();if(d<0||d>=128)std::abort();hist[d]++;
    }
    auto v=s.rows();
    std::cout<<"steps="<<k<<" headLength="<<v.size()
             <<" primaryCells="<<v.size()+2<<" deaths="<<s.deaths<<"\n";
    std::cout<<"hist:";for(int i=0;i<128;i++)if(hist[i])
        std::cout<<" "<<i<<":"<<hist[i];std::cout<<"\n";
    cpp_int qSum=131073+2883586;
    cpp_int mass=0;
    for(size_t j=0;j<v.size();++j){
        mass+=(v[j]->life<<j);
        cpp_int q=v[j]->credit-(cpp_int(1)<<(j+2));
        if(q<0)std::abort();
        qSum+=q;
        if(argc>2&&std::string(argv[2])=="--dump"){
            cpp_int p=(v[j]->life<<(j+3));
            std::cout<<p<<" "<<q<<"\n";
        }
    }
    const cpp_int M=cpp_int(1)<<(v.size()+2);
    const cpp_int qPred=3506202+16*mass-M;
    if(k==32750 && qSum!=qPred)std::abort();
    std::cout<<"qsumBits="<<(qSum==0?0:boost::multiprecision::msb(qSum)+1)
             <<" weightedMassBits="<<(boost::multiprecision::msb(mass)+1)
             <<" qMassFormula="<<(k==32750?"MATCH":"not checked")<<"\n";
    std::cout<<"firstQs:";
    for(size_t j=0;j<std::min(size_t(8),v.size());j++)
        std::cout<<" "<<v[j]->credit-(cpp_int(1)<<(j+2));
    std::cout<<"\n";
}
