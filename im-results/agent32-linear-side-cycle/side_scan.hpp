#pragma once
#include <array>
#include <vector>
#include <algorithm>
#include <cstdint>
#include <limits>

namespace side_scan {
// Each ID is a canonical semi-infinite binary word. Node 0 denotes all-zero.
// For each suffix and bit, its unique cons ID is cached at the suffix node.
// No probabilistic hashes or fixed tape window are used.
struct Node {
    int tail=0, bit=0;
    std::array<int,2> child{-1,-1};
    std::array<int,6> lastR{-1,-1,-1,-1,-1,-1};
    std::array<int,6> lastL{-1,-1,-1,-1,-1,-1};
};
struct Record {int word,q,h,n,prev;};
struct Result {int typ,n,s,e,k,dir,b;}; // hole=1, cycle=2, unknown=0
class Scanner {
    std::vector<Node> nodes;
    std::vector<Record> right,left;
    int cons(int b,int tail) {
        int child=nodes[tail].child[b];
        if(child>=0)return child;
        child=static_cast<int>(nodes.size());
        nodes[tail].child[b]=child;
        Node v; v.bit=b; v.tail=tail; nodes.push_back(v);
        return child;
    }
    template<bool R> void expire(int h) {
        auto& stack=R?right:left;
        while(!stack.empty() && (R?stack.back().h>h:stack.back().h<h)) {
            auto r=stack.back();
            (R?nodes[r.word].lastR:nodes[r.word].lastL)[r.q]=r.prev;
            stack.pop_back();
        }
    }
    template<bool R> int find(int word,int q) const {
        return (R?nodes[word].lastR:nodes[word].lastL)[q];
    }
    template<bool R> void add(int word,int q,int h,int n) {
        auto& stack=R?right:left;
        auto& last=(R?nodes[word].lastR:nodes[word].lastL)[q];
        int prev=last;last=static_cast<int>(stack.size());
        stack.push_back({word,q,h,n,prev});
    }
public:
    Result run(const std::array<int,12>& p,int limit) {
        nodes.clear();nodes.emplace_back();nodes[0].child[0]=0;
        left.clear();right.clear();
        int l=0,r=0,a=0,q=0,h=0;
        for(int n=0;n<=limit;n++) {
            int slot=2*q+a,act=p[slot];
            if(act<0)return {1,n,slot,0,0,0,0};
            int wr=cons(a,r),wl=cons(a,l);
            expire<true>(h);expire<false>(h);
            int ir=find<true>(wr,q),il=find<false>(wl,q);
            if(ir>=0) {auto e=right[ir];return {2,0,0,e.n,n-e.n,1,e.h};}
            if(il>=0) {auto e=left[il];return {2,0,0,e.n,n-e.n,0,e.h};}
            if(n==limit)break;
            add<true>(wr,q,h,n);add<false>(wl,q,h,n);
            int w=act/12;
            if(act%12>=6) {
                l=cons(w,l);a=nodes[r].bit;r=nodes[r].tail;h++;
            } else {
                r=cons(w,r);a=nodes[l].bit;l=nodes[l].tail;h--;
            }
            q=act%6;
        }
        return {0,0,0,0,0,0,0};
    }
};
} // namespace side_scan
