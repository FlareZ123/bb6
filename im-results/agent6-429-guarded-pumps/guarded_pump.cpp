#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <unordered_map>
#include <vector>

// Source-exact transcription of BB429.next in BB429Rank.lean.
// All arithmetic fits signed 64-bit for N <= 2e17 by run_rank_bounds:
// 2*u+w <= 31*N. Candidate affine products use signed 128-bit temporaries.
using u64 = std::uint64_t;
using i64 = std::int64_t;
using i128 = __int128_t;

struct State {
    u64 u, w;
    bool operator==(const State& x) const { return u == x.u && w == x.w; }
};

enum Branch { H, R2, R1, R0, E1, EE, EO, HALT, O2, O0, OE, OO };
struct Transition { Branch branch; State next; };

Transition step(State x) {
    auto [u, w] = x;
    if (w >= 2*u+3) return {H, {2*u+3, w-2*u-3}};
    if (w == 2*u+2) return {R2, {0, 4*u+18}};
    if (w == 2*u+1) return {R1, {11, 4*u+2}};
    if (w == 2*u) return {R0, {0, 4*u+12}};
    u64 d = u - w/2;
    if (w%2 == 0) {
        if (d == 1) return {E1, {0, 2*w+12}};
        if (d%2 == 0) return {EE, {11, 2*u+w-2}};
        return {EO, {0, 2*u+w+10}};
    }
    if (d == 1) return {HALT, x};
    if (d == 2) return {O2, {0, 2*w+8}};
    if (d%2 == 0) {
        if (w == 1) return {O0, {11, 2*u+10}};
        return {OE, {d+7, 2*w-4}};
    }
    return {OO, {d+3, 2*w}};
}

struct Entry { u64 t, w; };
struct Key {
    u64 u, residue;
    bool operator==(const Key& x) const { return u == x.u && residue == x.residue; }
};
struct KeyHash {
    std::size_t operator()(const Key& x) const {
        return std::hash<u64>{}((x.u * 0x9e3779b97f4a7c15ULL) ^ x.residue);
    }
};

struct Candidate {
    u64 period, drift;
    std::vector<State> old_states, new_states;
    std::vector<Branch> branches;
};

// Two consecutive copies of the same affine itinerary, with return
// (u,w) -> (u,w+drift), establish all stagewise affine differences.
std::optional<Candidate> detect(u64 period, u64 drift, State old, State now) {
    Candidate c{period, drift, {old}, {now}, {}};
    c.old_states.reserve(period+1);
    c.new_states.reserve(period+1);
    c.branches.reserve(period);
    for (u64 j=0; j<period; ++j) {
        auto a=step(c.old_states.back());
        auto b=step(c.new_states.back());
        if (a.branch == HALT || a.branch != b.branch) return std::nullopt;
        c.branches.push_back(a.branch);
        c.old_states.push_back(a.next);
        c.new_states.push_back(b.next);
    }
    if (!(c.old_states.back() == now) ||
        !(c.new_states.back() == State{now.u, now.w+drift})) return std::nullopt;

    // Every parity-dependent branch must remain in its congruence coset.
    // This rules out endpoint agreement hiding alternating parity.
    for (u64 j=0; j<period; ++j) {
        i64 du=(i64)c.new_states[j].u-(i64)c.old_states[j].u;
        i64 dw=(i64)c.new_states[j].w-(i64)c.old_states[j].w;
        auto b=c.branches[j];
        if (b != H && dw%2 != 0) return std::nullopt;
        if (b >= E1 && b != HALT &&
            (dw%2 != 0 || (du-dw/2)%2 != 0)) return std::nullopt;
    }
    return c;
}

// Verify the *furthest* repetition's itinerary and affine stage outputs.
// All intermediate repetitions have the same itinerary: each guard is an
// integer affine equality/inequality within a preserved parity coset,
// hence convex on the line segment between the checked endpoints.
bool valid_endpoint(const Candidate& c, u64 k) {
    State x{c.new_states[0].u, c.new_states[0].w+k*c.drift};
    for (u64 j=0; j<c.period; ++j) {
        auto a=step(x);
        if (a.branch != c.branches[j]) return false;
        i64 du=(i64)c.new_states[j+1].u-(i64)c.old_states[j+1].u;
        i64 dw=(i64)c.new_states[j+1].w-(i64)c.old_states[j+1].w;
        i128 eu=(i128)c.new_states[j+1].u+(i128)k*du;
        i128 ew=(i128)c.new_states[j+1].w+(i128)k*dw;
        if (eu<0 || ew<0 || eu>(i128)UINT64_MAX || ew>(i128)UINT64_MAX ||
            a.next.u!=(u64)eu || a.next.w!=(u64)ew) return false;
        x=a.next;
    }
    return x == State{c.new_states[0].u, c.new_states[0].w+(k+1)*c.drift};
}

struct EscapeEvent { u64 time; State state; };

// Do not silently skip a previously proved infinite-survival entry:
// (u,u+8), u>=17 and u=1 mod 4. Each stage's (u,w) is affine in k.
std::optional<EscapeEvent> escape_in_pump(const Candidate& c, u64 cycles, u64 t) {
    std::optional<EscapeEvent> earliest;
    for (u64 j=0; j<c.period; ++j) {
        i64 du=(i64)c.new_states[j].u-(i64)c.old_states[j].u;
        i64 dw=(i64)c.new_states[j].w-(i64)c.old_states[j].w;
        i64 b=(i64)c.new_states[j].w-(i64)c.new_states[j].u-8;
        i64 slope=dw-du;
        std::vector<u64> possible;
        if (slope==0) {
            if (b!=0) continue;
            for (u64 k=0; k<std::min<u64>(cycles,100); ++k) possible.push_back(k);
            if (du>0 && (i64)c.new_states[j].u<17) {
                u64 k=(u64)((17-(i64)c.new_states[j].u+du-1)/du);
                for (u64 n=k; n<std::min<u64>(cycles,k+100); ++n) possible.push_back(n);
            }
        } else {
            if (-b%slope!=0) continue;
            i64 k=-b/slope;
            if (k>=0 && (u64)k<cycles) possible.push_back((u64)k);
        }
        for (u64 k:possible) {
            i128 u=(i128)c.new_states[j].u+(i128)k*du;
            i128 w=(i128)c.new_states[j].w+(i128)k*dw;
            if (u>=17 && w==u+8 && u%4==1) {
                EscapeEvent event{t+k*c.period+j,{(u64)u,(u64)w}};
                if (!earliest || event.time<earliest->time) earliest=event;
            }
        }
    }
    return earliest;
}

int main(int argc, char** argv) {
    if (argc<2) {
        std::cerr << "usage: guarded_pump MACRO_STEPS\n";
        return 2;
    }
    u64 N=std::strtoull(argv[1],nullptr,10);
    if (N>200000000000000000ULL) {
        std::cerr << "Require N <= 2e17 for 64-bit rank bounds\n";
        return 2;
    }
    State x{0,0};
    u64 t=0, skipped=0, cycles=0, attempts=0, matches=0;
    std::unordered_map<Key,Entry,KeyHash> seen;
    auto start=std::chrono::steady_clock::now();
    while (t<N) {
        auto s=step(x);
        if (x.u>=17 && x.u%4==1 && x.w==x.u+8) {
            std::cout << "ESCAPE macro=" << t << " u=" << x.u << " w=" << x.w << "\n";
            break;
        }
        if (s.branch==HALT) {
            std::cout << "HALT macro=" << t << " u=" << x.u << " w=" << x.w << "\n";
            break;
        }
        if (s.branch!=H) {
            Key key{x.u,x.w%8};
            auto it=seen.find(key);
            if (it!=seen.end() && x.w>it->second.w) {
                u64 period=t-it->second.t, drift=x.w-it->second.w;
                if (period>=1 && period<=2048) {
                    ++attempts;
                    auto c=detect(period,drift,State{x.u,it->second.w},x);
                    if (c) {
                        ++matches;
                        u64 cap=(N-t)/period;
                        if (cap>=2) {
                            u64 maxK=cap-1, low=0, high=1;
                            while (high<maxK && valid_endpoint(*c,high)) {
                                low=high;
                                high=std::min(maxK,high*2);
                            }
                            u64 best=0;
                            if (valid_endpoint(*c,high)) best=high;
                            else {
                                while (high-low>1) {
                                    u64 mid=(high+low)/2;
                                    if (valid_endpoint(*c,mid)) low=mid;
                                    else high=mid;
                                }
                                best=low;
                            }
                            u64 count=best+1;
                            if (count>=2) {
                                auto escape=escape_in_pump(*c,count,t);
                                if (escape) {
                                    std::cout << "ESCAPE_IN_PUMP macro=" << escape->time
                                              << " u=" << escape->state.u
                                              << " w=" << escape->state.w
                                              << " period=" << period
                                              << " drift=" << drift << "\n";
                                    return 0;
                                }
                                x.w+=count*drift;
                                t+=count*period;
                                skipped+=count*period;
                                cycles+=count;
                                seen.clear();
                                continue;
                            }
                        }
                    }
                }
            }
            seen.insert_or_assign(key,Entry{t,x.w});
        }
        x=s.next;
        ++t;
    }
    auto ms=std::chrono::duration_cast<std::chrono::milliseconds>(
        std::chrono::steady_clock::now()-start).count();
    std::cout << "N=" << N << " t=" << t << " end=(" << x.u << "," << x.w
              << ") skipped=" << skipped << " cycles=" << cycles
              << " attempts=" << attempts << " matches=" << matches
              << " runtime_ms=" << ms << "\n";
}
