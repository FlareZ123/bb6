#include <boost/multiprecision/cpp_int.hpp>
#include <vector>
#include <fstream>
#include <iostream>
using I=boost::multiprecision::cpp_int;using namespace std;
struct C{I p,q;};
// Closed recurrence from PrimaryGuard.md, far-to-near.
int main(){vector<C> cs={{2883545,131073},{7077811,2883586},{2621288,3145735},{224,3148774},{960,3054},{384,3038},{2816,4031},{3584,3967},{512,767},{2048,1535}}; I K=0;for(int n=0;n<32750;n++){I B=1,Cscale=1,merge=0;size_t j=0;for(size_t i=0;i<cs.size();i++){auto &c=cs[i]; c.p-=B<<1;c.q+=B;if(c.p==0)merge+=c.q;else {if(c.p<3){cerr<<"guard fail";return 2;}c.q+=merge-Cscale;merge=0;if(i!=j)cs[j]=std::move(c);j++;Cscale<<=1;}B<<=1;}cs.resize(j);cs.push_back({B<<2,(B<<2)-1+merge-Cscale});K+=B+(Cscale<<2);if(n%5000==4999)cerr<<n+1<<" "<<cs.size()<<endl;}
I M=I(1)<<cs.size();ofstream f("prefix-state.txt");f<<32750<<'\n'<<K<<'\n'<<2*M-1<<' '<<3*M-1<<' '<<cs.size()<<'\n';for(size_t i=cs.size();i-->0;)f<<cs[i].p<<' '<<cs[i].q<<'\n';}
