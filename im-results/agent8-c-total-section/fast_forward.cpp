// Experimental finite-orbit simulation of the original Machine C counter map.
// Source equivalence for individual high sweeps: BB6.CSection.sweep.
// This C++ program is not itself a Lean proof of nonhalting.
#include <algorithm>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <optional>
#include <string>
#include <tuple>

using U = std::uint64_t;
using U128 = unsigned __int128;

struct Ret { U a, k, steps; bool halt; };

// Performs the first c=0 return, batching runs of the source's high sweep.
static inline Ret next_section(U a, U k) {
    U c;
    if (a == 0) {
        c = 2*k+2;
        a=1;
        k=0;
    } else if (a == 1) {
        if (k==0) { a=5; c=1; }
        else { c=2*(k-1)+1; a=2; k=2; }
    } else { a-=2; c=2*k+1; k=1; }
    U count=1;
    while (c>=4) {
        if (a!=0) {
            U q=std::min(a,c-3);
            a-=q;
            k+=q;
            c-=q;
            count+=q;
        } else if ((k&1U)==0) {
            a=2*k+2;
            k=2;
            c-=3;
            ++count;
        } else {
            a=2*k+3;
            k=0;
            ++count;
        }
    }
    if (c==1) return {a,k+1,count+1,false};
    if (c==3) return {a,k+3,count+2,false};
    return {a,k,count+1,true};
}

// Independent literal transcription of every single BB6CLine.nextC branch.
static inline std::optional<std::tuple<U,U,U>> source_step(U a,U k,U c) {
    if(c==1) return std::make_tuple(a,k+1,U(0));
    if(c==2) return std::nullopt;
    if(c==3) return std::make_tuple(a,k+2,U(1));
    if(c==0) {
        if(a==0) return std::make_tuple(U(1),U(0),2*k+2);
        if(a==1 && k==0) return std::make_tuple(U(5),U(0),U(1));
        if(a==1) return std::make_tuple(U(2),U(2),2*(k-1)+1);
        return std::make_tuple(a-2,U(1),2*k+1);
    }
    if(a==0) {
        if(k%2==0) return std::make_tuple(2*k+2,U(2),c-3);
        return std::make_tuple(2*k+3,U(0),c);
    }
    return std::make_tuple(a-1,k+1,c-1);
}

static inline Ret slow_section(U a,U k) {
    U c=0;
    for(U t=1; ; ++t) {
        auto s=source_step(a,k,c);
        if(!s) return {0,0,t,true};
        a=std::get<0>(*s); k=std::get<1>(*s); c=std::get<2>(*s);
        if(c==0) return {a,k,t,false};
    }
}

static void self_test() {
    U seed=0x85ebca6b95ab3c21ULL;
    for(int i=0;i<10000;i++) {
        seed^=seed<<13; seed^=seed>>7;seed^=seed<<17;
        U a=seed%1000;
        seed^=seed<<13; seed^=seed>>7;seed^=seed<<17;
        U k=seed%1000;
        Ret x=next_section(a,k),y=slow_section(a,k);
        if(x.halt!=y.halt || x.steps!=y.steps || (!x.halt && (x.a!=y.a || x.k!=y.k))) {
           std::fprintf(stderr,"FAIL case %d: (a,k)=(%" PRIu64 ",%" PRIu64 ")\n",i,a,k);
           std::exit(1);
        }
    }
    std::puts("PASS 10000 reproducible independent macro-step section comparisons");
}

static void print_u128(U128 value) {
    char buf[42]; int n=0;
    do { buf[n++]=char('0'+value%10); value/=10; } while(value);
    while(n) std::putchar(buf[--n]);
}

int main(int argc, char** argv) {
    if(argc>1 && std::string(argv[1])=="--self-test") {self_test();return 0;}
    U count = argc>1 ? std::strtoull(argv[1],nullptr,10) : 1000000;
    U a=5,k=1;
    U128 macro=1;
    U hash=0x243f6a8885a308d3ULL;
    for(U i=0;i<count;i++) {
        Ret r=next_section(a,k);
        macro+=r.steps;
        if(r.halt) {
            std::printf("HALT at section=%" PRIu64 ", a=%" PRIu64 ",k=%" PRIu64 ", accelerator_calls=",i,a,k);
            print_u128(macro); std::puts(""); return 0;
        }
        a=r.a; k=r.k;
        hash ^= a+0x9e3779b97f4a7c15ULL+(hash<<6)+(hash>>2);
        hash ^= k+0x517cc1b727220a95ULL+(hash<<6)+(hash>>2);
        if((i+1)%100000000ULL==0 || (i+1)==count) {
            std::printf("section=%" PRIu64 " a=%" PRIu64 " k=%" PRIu64 " rank=%" PRIu64 " hash=%016" PRIx64 " macro=",i+1,a,k,a+2*k,hash);
            print_u128(macro); std::puts(""); std::fflush(stdout);
        }
    }
    return 0;
}
