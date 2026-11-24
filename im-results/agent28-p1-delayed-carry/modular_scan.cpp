#include <algorithm>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
int main(int argc,char**argv){int lo=stoi(argv[1]),hi=stoi(argv[2]);vector<unsigned> cs,ns;uint64_t total=0;int exceptions=0;for(int n=lo;n<=hi;n+=2){cs.assign(1,(n+2)/2); unsigned j=1;size_t maxw=1;for(;j<(unsigned)n&&!cs.empty();++j){ns.clear();unsigned C=n+3+j;for(unsigned p:cs){if((p&1)==0)ns.push_back(p/2);if(((p+C)&1)==0)ns.push_back((p+C)/2);}cs.swap(ns);maxw=max(maxw,cs.size());total+=cs.size();}if(!cs.empty()||j+20>(unsigned)n){cout<<n<<" "<<j<<" "<<cs.size()<<" "<<maxw<<"\n";cout.flush();exceptions++;}if(n%10000==2){cerr<<n<<" total states "<<total<<" exceptions "<<exceptions<<"\n";}}}
