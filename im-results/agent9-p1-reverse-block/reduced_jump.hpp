#pragma once
#include <algorithm>
#include <cstdint>
#include <stdexcept>
#include <vector>

// Exact support of the modular carry jump. One plan is reusable for every
// target word at the same starting clock q and suffix length r.
// For the signed int clock limits of the prefix drivers, r <= 30.
namespace bb6_jump {
using U = std::uint64_t;
using W = std::uint32_t;
struct Plan {
    int q, r, exponent;
    W modulus;
    std::vector<W> residues; // sorted support for target Y=0
    Plan(int start, int length) : q(start), r(length), exponent(length) {
        if (q < 0 || r < 0 || r > 30) throw std::invalid_argument("jump range");
        // Preserve the exact weights; half-modulus removal commutes with all
        // remaining subset choices. Descending order matches ResiduePeriod.
        std::vector<U> weights;
        for (int j = r; j-- > 0;) weights.push_back((U(q)+j) << j);
        while (exponent > 0) {
            U m = U(1) << exponent, h = m >> 1;
            auto it = std::find_if(weights.begin(), weights.end(),
                [=](U w) { return (w & (m-1)) == h; });
            if (it == weights.end()) break;
            weights.erase(it);
            --exponent;
        }
        modulus = W(1) << exponent;
        W mask = modulus-1;
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
    // Translation modulo M is a cyclic rotation of the sorted support.
    // Enumerate [0,q) in sorted order with no per-target allocation or sort.
    template<class Emit> void lift(U Y, Emit emit) const {
        W y=W(Y)&(modulus-1);
        auto split=std::lower_bound(residues.begin(),residues.end(),modulus-y);
        for (U base=0;base<U(q);base+=modulus) {
            for (auto it=split;it!=residues.end();++it) {
                U c=base+*it+y-modulus;
                if (c>=U(q)) break;
                emit(int(c));
            }
            for (auto it=residues.begin();it!=split;++it) {
                U c=base+*it+y;
                if (c>=U(q)) break;
                emit(int(c));
            }
        }
    }
};
} // namespace bb6_jump
