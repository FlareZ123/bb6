#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

namespace {
constexpr int M = 224;
constexpr int N = 112;
constexpr int C = N + 4;
constexpr std::uint32_t V = M * M * C;
struct T { int a, k, c; };

std::uint32_t index(T s) {
    int c = s.c < 4 ? s.c : 4 + (s.c - 4) % N;
    return (s.a % M * M + s.k % M) * C + c;
}
T decode(std::uint32_t i) {
    return {static_cast<int>(i / (M * C)),
            static_cast<int>((i / C) % M),
            static_cast<int>(i % C)};
}
bool nextC(T s, T& t) {
    const auto [a,k,c] = s;
    if (c == 1) { t = {a,k+1,0}; return true; }
    if (c == 2) return false;
    if (c == 3) { t = {a,k+2,1}; return true; }
    if (c == 0) {
        if (a == 0) t = {1,0,2*k+2};
        else if (a == 1) t = k == 0 ? T{5,0,1} : T{2,2,2*k-1};
        else t = {a-2,1,2*k+1};
        return true;
    }
    if (a == 0) {
        if (k % 2 == 0) t = {2*k+2,2,c-3};
        else t = {2*k+3,0,c};
    } else t = {a-1,k+1,c-1};
    return true;
}

template<class F> void successors(std::uint32_t source, F consume) {
    auto [a,k,c] = decode(source);
    for (int da : {0,M}) for (int dk : {0,M}) {
        for (int dc : {0,N}) {
            if (c < 4 && dc != 0) continue;
            T out;
            if (nextC({a+da,k+dk,c+dc}, out)) consume(index(out));
        }
    }
}

bool bad(T s) {
    const auto [a,k,c] = s;
    if (c == 0) return (a%224==13 && k%224==191)
                         || (a%112==18 && k%56==15)
                         || (a%112==74 && k%56==43)
                         || (a%112==100 && k%56==32);
    if (c == 1) return (a%224==13 && k%224==190)
                         || (a%112==18 && k%56==14)
                         || (a%112==74 && k%56==42)
                         || (a%112==100 && k%56==31);
    if (c == 3) return (a%224==13 && k%224==188)
                         || (a%112==18 && k%56==12)
                         || (a%112==74 && k%56==40)
                         || (a%112==100 && k%56==29);
    if (c < 4) return false;
    return (a%112==(c+10)%112 && (a+k)%224==201)
        || (a%112==(c+15)%112 && (a+k)%56==30)
        || (a%112==(c+24)%112 && (a+k)%56==35)
        || (a%112==(c+33)%112 && (a+k)%112==99)
        || (a%112==(c+71)%112 && (a+k)%56==2)
        || (a%112==(c+80)%112 && (a+k)%56==7)
        || (a%112==(c+97)%112 && (a+k)%56==17);
}
} // namespace

int main() {
    std::vector<std::uint32_t> indegree(V, 0);
    std::uint64_t edges = 0;
    for (std::uint32_t s = 0; s < V; ++s)
        successors(s, [&](std::uint32_t t) { ++indegree[t]; ++edges; });
    if (edges != 45559808ULL) throw std::runtime_error("edge count mismatch");
    std::vector<std::uint32_t> offsets(V+1, 0);
    for (std::uint32_t i = 0; i < V; ++i) offsets[i+1] = offsets[i] + indegree[i];
    std::vector<std::uint32_t> pred(edges);
    std::vector<std::uint32_t> cursors(offsets.begin(), offsets.end()-1);
    for (std::uint32_t s = 0; s < V; ++s)
        successors(s, [&](std::uint32_t t) { pred[cursors[t]++] = s; });

    std::vector<std::uint8_t> reverse(V, 0);
    std::vector<std::uint32_t> queue;
    queue.reserve(6000);
    const auto root = index({5,0,1});
    const auto target = index({13,191,0});
    reverse[target] = 1;
    queue.push_back(target);
    for (std::size_t i = 0; i < queue.size(); ++i) {
        auto t = queue[i];
        for (auto z=offsets[t]; z<offsets[t+1]; ++z) {
            auto s = pred[z];
            if (!reverse[s]) { reverse[s] = 1; queue.push_back(s); }
        }
    }
    std::array<std::uint32_t,5> phases{};
    std::uint32_t mismatches = 0;
    for (std::uint32_t i=0; i<V; ++i) {
        auto x=decode(i);
        if ((reverse[i] != 0) != bad(x)) ++mismatches;
        if (reverse[i]) ++phases[x.c<4 ? x.c : 4];
    }
    std::cout << "vertices=" << V << " edges=" << edges << '\n';
    std::cout << "reverse=" << queue.size() << " root_in_reverse=" << int(reverse[root])
              << " c0=" << phases[0] << " c1=" << phases[1]
              << " c2=" << phases[2] << " c3=" << phases[3]
              << " c_ge4=" << phases[4] << " formula_mismatches=" << mismatches << '\n';
    if (queue.size()!=5227 || reverse[root] || mismatches
        || phases != std::array<std::uint32_t,5>{25,25,0,25,5152})
        throw std::runtime_error("reverse certificate mismatch");

    std::vector<std::uint8_t> reached(V, 0);
    queue.clear();
    queue.reserve(V/2);
    reached[root] = 1;
    queue.push_back(root);
    for (std::size_t i = 0; i < queue.size(); ++i)
        successors(queue[i], [&](std::uint32_t t) {
            if (!reached[t]) { reached[t] = 1; queue.push_back(t); }
        });
    std::cout << "forward_reached=" << queue.size()
              << " target_reached=" << int(reached[target]) << '\n';
    if (queue.size() != 3222498 || reached[target])
        throw std::runtime_error("forward certificate mismatch");
}
