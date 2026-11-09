// Exact-integer P1 exceptional right-five inverse-cone traversal.
// Source inverse equations: im-results/agent1-p1-quarter/InverseIff.lean.
// Nonterminal child uniqueness follows from original deterministic T^2.
// Requires Boost.Multiprecision, C++17. No fixed-width arithmetic for counters.
#include <boost/multiprecision/cpp_int.hpp>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using boost::multiprecision::cpp_int;
struct State { cpp_int b, d; };
struct Outcome {
    unsigned n;
    uint64_t active, children, inactive, maxQueue;
    bool found, capped;
    double seconds;
};
Outcome run(unsigned n, uint64_t cap) {
    cpp_int P = cpp_int(1) << n;
    std::vector<State> stack;
    stack.push_back({14*P-2*n-16,3});
    uint64_t active=0,children=0,inactive=0,maxQueue=1;
    auto start=std::chrono::steady_clock::now();
    while(!stack.empty()) {
        State s=std::move(stack.back());stack.pop_back();
        ++active;
        if(active>cap) return {n,active,children,inactive,maxQueue,false,true,0};
        cpp_int a=s.d+(s.b>>1)+3;
        unsigned v=boost::multiprecision::lsb(a);
        cpp_int q=a;
        for(unsigned t=0;t<v;++t,q>>=1) {
            if(q<4) continue; // c=q-3 must be a positive odd integer
            cpp_int newb=s.b+s.d-q-2*t-3;
            if(newb<0) continue; // k>=2, because child b=2*k-4
            cpp_int newd=q+1;
            ++children;
            if(newd==5) {
                double seconds=std::chrono::duration<double>(
                    std::chrono::steady_clock::now()-start).count();
                std::cerr<<"WITNESS n="<<n<<" parent_b="<<s.b
                    <<" parent_d="<<s.d<<" t="<<t
                    <<" child_b="<<newb<<"\n";
                return {n,active,children,inactive,maxQueue,true,false,seconds};
            }
            if(newb<8 || (newb&3)!=0) {
                ++inactive;
                continue;
            }
            stack.push_back({std::move(newb),std::move(newd)});
        }
        if(maxQueue<stack.size()) maxQueue=stack.size();
    }
    double seconds=std::chrono::duration<double>(
        std::chrono::steady_clock::now()-start).count();
    return {n,active,children,inactive,maxQueue,false,false,seconds};
}
int main(int argc,char**argv) {
    if(argc<2) return 2;
    unsigned low=std::strtoul(argv[1],nullptr,10);
    unsigned high=argc>2?std::strtoul(argv[2],nullptr,10):low;
    uint64_t cap=argc>3?std::strtoull(argv[3],nullptr,10):10000000;
    bool qmode=argc>4 && argv[4][0]=='q';
    uint64_t total=0,complete=0,capped=0;
    for(unsigned i=low;i<=high;++i) {
        unsigned n=qmode?(16*i+2):i;
        Outcome r=run(n,cap);
        std::cout<<"n="<<r.n<<" active="<<r.active
            <<" edges="<<r.children<<" inactive="<<r.inactive
            <<" peak="<<r.maxQueue
            <<" status="<<(r.found?"HIT":(r.capped?"CAPPED":"COMPLETE"))
            <<" seconds="<<r.seconds<<"\n";
        total+=r.active;
        complete+=!r.found&&!r.capped;
        capped+=r.capped;
        if(r.found) return 1;
    }
    std::cerr<<"SUMMARY cases="<<high-low+1<<" complete="<<complete
        <<" capped="<<capped<<" activeTotal="<<total<<"\n";
}
