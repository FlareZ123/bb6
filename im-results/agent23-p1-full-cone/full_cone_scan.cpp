#include <boost/multiprecision/cpp_int.hpp>
#include <algorithm>
#include <cassert>
#include <iostream>
#include <vector>
using boost::multiprecision::cpp_int;
int main(){
  for (auto [n,K] : std::vector<std::pair<unsigned,unsigned>>{{30,82},{286,1442},{350,586},{1614,5824},{2990,6154},{3342,13730}}){
    const cpp_int P=cpp_int(1)<<n, Q=7*P-n-3;
    std::vector<cpp_int> cs{1}, next;
    size_t peak=1; unsigned j=0;
    for(;j<K && !cs.empty();++j){
      const cpp_int R=Q-j, limit=7*P-2*j-2*n-3;
      next.clear(); next.reserve(2*cs.size());
      for(const auto& v:cs){
        assert(v!=2 && v<limit);
        if(!bit_test(v,0))next.push_back(v>>1);
        if(bit_test(v,0)==bit_test(R,0))next.push_back((v+R)>>1);
      }
      cs.swap(next);peak=std::max(peak,cs.size());
    }
    assert(j==K && cs.empty());
    std::cout << n << ' ' << K << ' ' << peak << " OK\n" << std::flush;
  }
}
