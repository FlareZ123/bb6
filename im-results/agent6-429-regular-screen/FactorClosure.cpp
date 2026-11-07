// Exact finite k-factor abstraction of the #429 six-state physical machine.
// Research diagnostic only: abstract bad factors are not blank-run witnesses.
// U=0, visited zero=1, visited one=2, head(state,bit)=10+2*state+bit.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <deque>
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <vector>

struct Context {
    std::vector<int> required;
    std::vector<int> produced;
    int unmet;
};
static constexpr int state_next[6][2] = {
    {1,5},{2,0},{3,1},{4,6},{0,4},{3,0}};
static constexpr int write_bit[6][2] = {
    {1,0},{1,1},{0,0},{0,1},{0,1},{1,1}};
static constexpr int move_dir[6][2] = {
    {1,-1},{1,1},{1,1},{-1,0},{-1,-1},{1,-1}};

static std::vector<std::vector<int>> sides(int k) {
    std::vector<std::vector<int>> out;
    for (int n=0;n<=k;++n)
        for (int mask=0;mask<(1<<n);++mask) {
            std::vector<int> word(k);
            for (int j=0;j<n;++j) word[j]=1+((mask>>j)&1);
            out.push_back(std::move(word));
        }
    return out;
}
static void make_unique(std::vector<int>& a) {
    std::sort(a.begin(),a.end());
    a.erase(std::unique(a.begin(),a.end()),a.end());
}
int main(int argc,char**argv) {
    const int k=argc==2?std::atoi(argv[1]):4;
    if (k<2 || k>9) throw std::invalid_argument("Use 2 <= k <= 9");
    const auto started=std::chrono::steady_clock::now();
    const auto options=sides(k);
    std::unordered_map<std::uint64_t,int> id_of;
    std::vector<std::uint64_t> keys;
    auto id=[&](std::uint64_t key) {
        auto it=id_of.find(key);
        if (it!=id_of.end()) return it->second;
        int next=static_cast<int>(keys.size());
        id_of.emplace(key,next);
        keys.push_back(key);
        return next;
    };
    auto key_at=[&](const std::vector<int>& w,int first) {
        std::uint64_t key=0;
        for(int i=first;i<first+k;++i)
            key=key*24+static_cast<unsigned>(w[i]);
        return key;
    };
    std::vector<Context> contexts;
    for(int state=0;state<6;++state)
        for(int bit=0;bit<2;++bit) {
            if(state_next[state][bit]==6) continue; // halt, no successor
            for(const auto& left:options)
                for(const auto& right:options) {
                    std::vector<int> before(2*k+1);
                    for(int i=0;i<k;++i) {
                        before[k-i-1]=left[i];
                        before[k+i+1]=right[i];
                    }
                    before[k]=10+2*state+bit;
                    auto after=before;
                    after[k]=1+write_bit[state][bit];
                    int destination=k+move_dir[state][bit];
                    int new_bit=after[destination]==0?0:after[destination]-1;
                    after[destination]=10+2*state_next[state][bit]+new_bit;
                    Context c;
                    for(int i=0;i<=k+1;++i) {
                        c.required.push_back(id(key_at(before,i)));
                        c.produced.push_back(id(key_at(after,i)));
                    }
                    make_unique(c.required);
                    make_unique(c.produced);
                    c.unmet=static_cast<int>(c.required.size());
                    contexts.push_back(std::move(c));
                }
        }
    std::vector<std::vector<int>> dependents(keys.size());
    for(int i=0;i<static_cast<int>(contexts.size());++i)
        for(int gram:contexts[i].required)
            dependents[gram].push_back(i);
    std::vector<char> admitted(keys.size());
    std::vector<int> depth(keys.size(),-1);
    std::deque<int> pending;
    auto add=[&](int gram,int level) {
        if(!admitted[gram]) {
            admitted[gram]=true;
            depth[gram]=level;
            pending.push_back(gram);
        }
    };
    // Blank tape with exactly one visited A/0 head.
    std::vector<int> blank(k);
    const int blank_id=id(key_at(blank,0));
    if(blank_id>=static_cast<int>(admitted.size()))
        throw std::logic_error("Missing all-blank factor");
    add(blank_id,0);
    for(int j=0;j<k;++j) {
        std::vector<int> word(k);
        word[j]=10;
        int g=id(key_at(word,0));
        if(g>=static_cast<int>(admitted.size()))
            throw std::logic_error("Missing initial-head factor");
        add(g,0);
    }
    int activated=0;
    int earliest_bad=-1;
    int final_depth=0;
    std::uint64_t bad_key=0;
    while(!pending.empty()) {
        const int gram=pending.front();
        pending.pop_front();
        final_depth=std::max(final_depth,depth[gram]);
        std::uint64_t encoded=keys[gram];
        std::vector<int> w(k);
        for(int j=k-1;j>=0;--j) {
            w[j]=static_cast<int>(encoded%24);
            encoded/=24;
        }
        for(int j=0;j+1<k;++j)
            if(w[j]==14 && (w[j+1]==1 || w[j+1]==2) &&
               earliest_bad<0) {
                earliest_bad=depth[gram];
                bad_key=keys[gram];
            }
        for(int ci:dependents[gram]) {
            Context& c=contexts[ci];
            if(--c.unmet==0) {
                ++activated;
                for(int g:c.produced) add(g,depth[gram]+1);
            }
        }
    }
    int admitted_count=0;
    for(char a:admitted) admitted_count+=a;
    const double elapsed=std::chrono::duration<double>(
        std::chrono::steady_clock::now()-started).count();
    std::cout<<"k="<<k<<" contexts="<<contexts.size()
             <<" factors="<<admitted_count
             <<" activated="<<activated
             <<" max_round="<<final_depth
             <<" first_bad_round="<<earliest_bad
             <<" elapsed_seconds="<<elapsed<<"\n";
    if(earliest_bad>=0) {
        std::vector<int> w(k);
        for(int j=k-1;j>=0;--j) {
            w[j]=static_cast<int>(bad_key%24);
            bad_key/=24;
        }
        std::cout<<"Example abstract bad k-gram:";
        for(int token:w) std::cout<<" "<<token;
        std::cout<<"\n";
    }
}
