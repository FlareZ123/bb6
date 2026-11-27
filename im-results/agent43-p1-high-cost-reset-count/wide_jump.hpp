#pragma once
#include <algorithm>
#include <cstdint>
#include <stdexcept>
#include <vector>
#include <immintrin.h>

// Exact support of the modular carry jump. One plan is reusable for every
// target word at the same starting clock q and suffix length r.
// For the signed int clock limits of the prefix drivers, r <= 30.
namespace bb6_jump {
using U = std::uint64_t;
using W = std::uint32_t;
inline bool bitmap_plan=false;
static inline U spread32(W x){
#if defined(__BMI2__)
 return _pdep_u64(x,0x5555555555555555ULL);
#else
 U a=x;a=(a|(a<<16))&0x0000ffff0000ffffULL;
 a=(a|(a<<8))&0x00ff00ff00ff00ffULL;
 a=(a|(a<<4))&0x0f0f0f0f0f0f0f0fULL;
 a=(a|(a<<2))&0x3333333333333333ULL;
 return (a|(a<<1))&0x5555555555555555ULL;
#endif
}
struct Plan {
    W q; int r, exponent;
    W modulus;
    std::vector<W> residues; // sorted support for target Y=0
    Plan(W start, int length) : q(start), r(length), exponent(length) {
        if (r < 0 || r > 30) throw std::invalid_argument("jump range");
        // Preserve the exact weights; half-modulus removal commutes with all
        // remaining subset choices. Descending order matches ResiduePeriod.
        std::vector<U> weights;
        std::vector<int> indices;
        std::vector<bool> removed(r,false);
        for (int j = r; j-- > 0;) {weights.push_back((U(q)+j) << j);indices.push_back(j);}
        while (exponent > 0) {
            U m = U(1) << exponent, h = m >> 1;
            auto it = std::find_if(weights.begin(), weights.end(),
                [=](U w) { return (w & (m-1)) == h; });
            if (it == weights.end()) break;
            auto pos=it-weights.begin();removed[indices[pos]]=true;
            weights.erase(it);indices.erase(indices.begin()+pos);
            --exponent;
        }
        modulus = W(1) << exponent;
        W mask = modulus-1;
        if(bitmap_plan){build_bitmap(removed);return;}
        // Sparse support construction; the bitmap avoids multiplicity and
        // uses one bit per residue. A zero shift adds no new support.
        std::vector<U> seen((U(modulus)+63)/64);
        auto insert = [&](W x) {
            U bit = U(1) << (x&63); U& word = seen[x>>6];
            if (word & bit) return false;
            word |= bit; return true;
        };
        residues.push_back(0); insert(0);
        // Low weights first gives the existing driver order; order is
        // immaterial to exact support. Stop as soon as support is full.
        for (auto it=weights.rbegin(); it!=weights.rend() && residues.size()<modulus; ++it) {
            W shift = W(*it) & mask;
            if (!shift) continue;
            std::size_t old = residues.size();
            for (std::size_t i=0; i<old; ++i) {
                W x=(residues[i]-shift)&mask;
                if (insert(x)) residues.push_back(x);
            }
        }
        std::sort(residues.begin(),residues.end());
    }
    // High-to-low scaled subset support. At digit j, dilation maps the
    // preceding support to even residues; the second branch is its cyclic
    // translation by -(q+j). Total bitmap words processed is geometric.
    void build_bitmap(const std::vector<bool>& removed){
        std::vector<U> prev(1,1);
        for(int j=exponent;j-->0;){
            U M=U(1)<<(exponent-j), nw=(M+63)/64;
            std::vector<U> even(nw);
            if(M<=64)even[0]=spread32(W(prev[0]));
            else for(std::size_t i=0;i<prev.size();i++){
                even[2*i]=spread32(W(prev[i]));
                even[2*i+1]=spread32(W(prev[i]>>32));
            }
            if(removed[j]){prev.swap(even);continue;}
            U shift=(U(q)+j)&(M-1);
            if(!shift){prev.swap(even);continue;}
            if(M<=64){
                U m=M==64?~U(0):(U(1)<<M)-1;
                even[0]|=((even[0]>>shift)|(even[0]<<(M-shift)))&m;
                prev.swap(even);continue;
            }
            std::vector<U> next(nw);
            U w=shift/64,b=shift%64;
            for(U i=0;i<nw;i++){
                U p=(i+w)&(nw-1),v=even[p]>>b;
                if(b)v|=even[(p+1)&(nw-1)]<<(64-b);
                next[i]=even[i]|v;
            }
            prev.swap(next);
        }
        std::size_t count=0;
        for(U v:prev)count+=__builtin_popcountll(v);
        residues.reserve(count);
        for(U i=0;i<prev.size();i++){
            U v=prev[i];
            while(v){unsigned b=__builtin_ctzll(v);residues.push_back(W(64*i+b));v&=v-1;}
        }
    }
    // Translation modulo M is a cyclic rotation of the sorted support.
    // Enumerate [0,q) in sorted order with no per-target allocation or sort.
    template<class Emit> void lift(U Y, Emit emit) const {
        W y=W(Y)&(modulus-1);
        auto split=std::lower_bound(residues.begin(),residues.end(),modulus-y);
        for (U base=0;base<U(q);base+=modulus) {
            for (auto it=split;it!=residues.end();++it) {
                U c=base+*it+y-modulus;
                if (c>=U(q)) break;
                emit(W(c));
            }
            for (auto it=residues.begin();it!=split;++it) {
                U c=base+*it+y;
                if (c>=U(q)) break;
                emit(W(c));
            }
        }
    }
};
} // namespace bb6_jump
