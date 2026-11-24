#include <gmpxx.h>
#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <stdexcept>
#include <vector>
using U=unsigned long;
using W=__uint128_t;
constexpr unsigned PREC=64;
constexpr W SCALE=W(1)<<PREC;
constexpr unsigned MAX_V=32;
struct Bounds { W lo, hi; };
struct Token { unsigned v, delta; U k; };
struct Affine { U a,d; mpz_class r,s,t; };

U kOf(const mpz_class& x) {
    U bits=mpz_sizeinbase(x.get_mpz_t(),2);
    U k=bits>4?bits-4:0;
    while (x+2*k+5 >= (mpz_class(16)<<k)) ++k;
    while (k && x+2*k+3 < (mpz_class(8)<<k)) --k;
    return k;
}
bool fatal(const mpz_class& x,U k) { return x+2*k+3 == (mpz_class(8)<<k); }
U pow3small(unsigned a) { U p=1; while(a--) p*=3; return p; }
Bounds correction(U k,unsigned c) {
    W t=W(2)*k+c;
    if(k<=PREC) { W z=t<<(PREC-k); return {z,z}; }
    U d=k-PREC;
    if(d>=128) return {0,1};
    W lo=t>>d;
    return {lo,lo+((lo<<d)!=t)};
}
Bounds normalized(const mpz_class& x,U k) {
    mpz_class z;
    if(k<=PREC) z=x<<(PREC-k); else z=x>>(k-PREC);
    if(mpz_sizeinbase(z.get_mpz_t(),2)>128) throw std::runtime_error("normalization overflow");
    W lo=0;size_t count=0;
    mpz_export(&lo,&count,-1,sizeof(lo),0,0,z.get_mpz_t());
    if(count>1) throw std::runtime_error("normalization overflow");
    bool exact=k<=PREC || mpz_divisible_2exp_p(x.get_mpz_t(),k-PREC);
    return {lo,lo+!exact};
}
W ceilshift(W x,unsigned s) { W q=x>>s; return q+((q<<s)!=x); }
// Return -1 if the sound interval does not certify a unique next level.
int advanceBounds(Bounds& b,U k,unsigned v) {
    auto c=correction(k,5); W p=pow3small(v-1);
    W l=(b.lo+16*SCALE+c.lo)*p;
    W u=(b.hi+16*SCALE+c.hi)*p;
    for(unsigned d=0;d<=v+2;++d) {
        unsigned s=v+d;
        W lo=l>>s,hi=ceilshift(u,s);
        auto lower=correction(k+d,3),upper=correction(k+d,5);
        if((k+d==0 || lo+lower.lo>=8*SCALE) && hi+upper.hi<16*SCALE) {
            b={lo,hi}; return int(d);
        }
    }
    return -1;
}
Affine compose(const std::vector<Token>& w,size_t l,size_t r) {
    if(r-l==1){const auto& z=w[l];mpz_class p=pow3small(z.v-1);return {z.v,z.delta,p,16*p,(2*z.k+5)*p};}
    size_t m=l+(r-l)/2;
    auto a=compose(w,l,m),b=compose(w,m,r);
    return {a.a+b.a,a.d+b.d,a.r*b.r,b.r*a.s+(b.s<<(a.a+a.d)),b.r*a.t+(b.t<<a.a)};
}
Token exactStep(mpz_class& x,U& k) {
    U k0=k;
    mpz_class z=x+(mpz_class(16)<<k)+2*k+5;
    U v=mpz_scan1(z.get_mpz_t(),0);mpz_class r;
    mpz_ui_pow_ui(r.get_mpz_t(),3,v-1);
    x=(z>>v)*r;k=kOf(x);
    return {unsigned(v),unsigned(k-k0),k0};
}
struct Stats {U steps=0,blocks=0,fallback=0,largest_v=0,interval_stop=0,precision_stop=0; std::ofstream* trace=nullptr;};
void emit(Stats& st,const Token& t) {
    if(!st.trace) return;
    if(t.v>255 || t.delta>255) throw std::runtime_error("trace token overflow");
    const unsigned char bytes[]={static_cast<unsigned char>(t.v-1),static_cast<unsigned char>(t.delta)};
    st.trace->write(reinterpret_cast<const char*>(bytes),2);
}
enum class Stop { Precision, Limit, Hard };
struct Prediction { Affine a; U steps; Stop stop; };
Affine identity() { return {0,0,1,0,0}; }
Affine merge(const Affine& a,const Affine& b) {
    return {a.a+b.a,a.d+b.d,a.r*b.r,b.r*a.s+(b.s<<(a.a+a.d)),b.r*a.t+(b.t<<a.a)};
}
mpz_class lowApply(const Affine& a,const mpz_class& low,U k,U budget) {
    mpz_class z=a.r*low+a.t;
    if(k<budget) {
        mpz_class s;
        mpz_fdiv_r_2exp(s.get_mpz_t(),a.s.get_mpz_t(),budget-k);
        z+=s<<k;
    }
    mpz_fdiv_r_2exp(z.get_mpz_t(),z.get_mpz_t(),budget);
    if(!mpz_divisible_2exp_p(z.get_mpz_t(),a.a)) throw std::runtime_error("low affine division");
    return z>>a.a;
}
Prediction predictLeaf(mpz_class low,U& k,Bounds& b,U limit,U budget,Stats& st) {
    U rem=budget;std::vector<Token> w;w.reserve(budget/2);Stop stop=Stop::Precision;
    while(w.size()<limit && rem>1) {
        if(b.lo+correction(k,3).lo<=8*SCALE) {
            mpz_class check=low+2*k+3;
            if(k+3<rem) check-=(mpz_class(8)<<k);
            if(mpz_divisible_2exp_p(check.get_mpz_t(),rem)) {stop=Stop::Hard;break;}
        }
        low+=2*k+5;
        if(k+4<rem) low+=(mpz_class(16)<<k);
        mpz_fdiv_r_2exp(low.get_mpz_t(),low.get_mpz_t(),rem);
        if(low==0) {++st.precision_stop;break;}
        U v=mpz_scan1(low.get_mpz_t(),0);
        if(v>=rem) {++st.precision_stop;break;}
        if(v==0 || v>MAX_V) {stop=Stop::Hard;break;}
        int d=advanceBounds(b,k,unsigned(v));
        if(d<0) {++st.interval_stop;stop=Stop::Hard;break;}
        w.push_back({unsigned(v),unsigned(d),k});
        emit(st,w.back());
        st.largest_v=std::max(st.largest_v,v);
        k+=d;rem-=v;low>>=v;low*=pow3small(v-1);
        mpz_fdiv_r_2exp(low.get_mpz_t(),low.get_mpz_t(),rem);
    }
    if(w.size()==limit) stop=Stop::Limit;
    return {w.empty()?identity():compose(w,0,w.size()),w.size(),stop};
}
Prediction predict(const mpz_class& low,U& k,Bounds& b,U limit,U budget,Stats& st) {
    if(budget<=1024 || limit<=32) return predictLeaf(low,k,b,limit,budget,st);
    U k0=k,half=budget/2;
    mpz_class l;
    mpz_fdiv_r_2exp(l.get_mpz_t(),low.get_mpz_t(),half);
    auto a=predict(l,k,b,limit,half,st);
    if(a.stop!=Stop::Precision) return a;
    // A precision stop consumes all but at most MAX_V bits, unless the
    // unknown valuation itself is large. Stop rather than recurse without progress.
    if(a.a.a<half/2) { a.stop=Stop::Hard;return a; }
    auto m=lowApply(a.a,low,k0,budget);
    auto c=predict(m,k,b,limit-a.steps,budget-a.a.a,st);
    return {merge(a.a,c.a),a.steps+c.steps,c.stop};
}
bool advance(mpz_class& x,U& k,U limit,U budget,Stats& st) {
    if(fatal(x,k)) return false;
    U k0=k;Bounds b=normalized(x,k);mpz_class low;
    mpz_fdiv_r_2exp(low.get_mpz_t(),x.get_mpz_t(),budget);
    auto p=predict(low,k,b,limit,budget,st);
    if(!p.steps) {
        emit(st,exactStep(x,k));++st.fallback;++st.steps;return true;
    }
    auto& a=p.a;
    mpz_class numerator=a.r*x+(a.s<<k0)+a.t;
    if(!mpz_divisible_2exp_p(numerator.get_mpz_t(),a.a)) throw std::runtime_error("inexact block division");
    x=numerator>>a.a;
    if(k!=k0+a.d || k!=kOf(x)) throw std::runtime_error("level mismatch");
    auto actual=normalized(x,k);
    if(actual.lo<b.lo || actual.hi>b.hi) throw std::runtime_error("interval mismatch");
    st.steps+=p.steps;++st.blocks;return true;
}
int main(int argc,char**argv) {
    U n=argc>1?std::stoul(argv[1]):1000000, budget=argc>2?std::stoul(argv[2]):1048576;
    bool direct=argc>3 && std::string(argv[3])=="direct";
    mpz_class x=9;U k=kOf(x);Stats st;auto start=std::chrono::steady_clock::now();
    std::ofstream trace;
    if(argc>4) {trace.open(argv[4],std::ios::binary);if(!trace) throw std::runtime_error("trace open");st.trace=&trace;}
    if(direct){while(st.steps<n && !fatal(x,k)){emit(st,exactStep(x,k));++st.steps;}}
    else {while(st.steps<n && advance(x,k,n-st.steps,std::min(budget,std::max<U>(1024,2*k)),st)) {}}
    std::cout<<"steps="<<st.steps<<" level="<<k<<" bits="<<mpz_sizeinbase(x.get_mpz_t(),2)<<" fatal="<<fatal(x,k)<<" blocks="<<st.blocks<<" fallback="<<st.fallback<<" interval_stop="<<st.interval_stop<<" precision_stop="<<st.precision_stop<<" max_v="<<st.largest_v<<" fingerprint="<<mpz_fdiv_ui(x.get_mpz_t(),1000000007)<<" time="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"s\n";
    if(trace.is_open()) {trace.close();if(!trace) throw std::runtime_error("trace write");}
    if(st.steps!=n) std::cout<<"HALT at reset "<<st.steps<<" level "<<k<<"\n";
}
