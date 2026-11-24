#include <algorithm>
#include <cstdint>
#include <iostream>
#include <utility>
#include <vector>
using P = std::pair<uint64_t,uint64_t>;
int main() {
    std::vector<P> cur,next;
    for(uint64_t k=2;k<=10000;k+=2) {
        cur={{k,k}};
        uint64_t d=0;
        while(!cur.empty() && d<20000) {
            next.clear();
            for(auto [u,v]:cur) {
                if(!(u&1)) next.emplace_back(u/2,v+u/2+1);
                if(!(v&1)) next.emplace_back(u+v/2,v/2);
            }
            std::sort(next.begin(),next.end());
            next.erase(std::unique(next.begin(),next.end()),next.end());
            cur.swap(next); ++d;
        }
        const uint64_t D=d-1;
        bool excluded=false;
        if(cur.empty() && D<2*k) {
            const uint64_t e=2*k-D;
            excluded=e>=63 || 4*k+2*D+7<(uint64_t(1)<<e);
        }
        if(!excluded) std::cout << k-1 << " depth=" << d
            << " empty=" << cur.empty() << "\n";
    }
}
