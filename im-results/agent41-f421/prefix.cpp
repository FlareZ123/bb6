#include <boost/multiprecision/cpp_int.hpp>
#include <vector>
#include <iostream>
#include <fstream>
#include <chrono>
using namespace std;using I=boost::multiprecision::cpp_int;
struct Cell{I p,q;};struct Prefix{I a,b;vector<Cell> cs;};
// All marked cells. Merged Q masses are retained exactly.
bool drain(Prefix &u,I &K){I H=0,merge=0;vector<Cell> rev;rev.reserve(u.cs.size());for(size_t i=u.cs.size();i-->0;){auto &c=u.cs[i];I cap=(H<<1)+1,n,t; if(c.p<=cap){if(!boost::multiprecision::bit_test(c.p,0))return false;n=c.p;t=(n+1)>>1;merge+=c.q+t;}else{n=std::move(cap);t=H+1;rev.push_back({c.p-n,c.q+t+merge});merge=0;}H+=t;}reverse(rev.begin(),rev.end());u.a+=H<<1;u.b+=H+merge;u.cs.swap(rev);K+=H;return true;}
bool cycle(Prefix&u,I&K,int &why){for(auto&c:u.cs){if(c.p<2){why=1;return false;}--c.p;}u.a+=2;++u.b;++K;if(!drain(u,K)){why=2;return false;}Prefix v{1,u.a+1,{}};I prev=u.b;v.cs.reserve(u.cs.size()+1);for(auto&c:u.cs){if(c.p<3){why=3;return false;}v.cs.push_back({prev,c.p-1});prev=c.q;}v.cs.push_back({prev,2});++K;if(!drain(v,K)){why=4;return false;}Prefix w{1,v.a+1,{}};prev=v.b;w.cs.reserve(v.cs.size());for(auto&c:v.cs){if(c.p<3){why=5;return false;}w.cs.push_back({prev,c.p-1});prev=c.q;}++K;if(!drain(w,K)){why=6;return false;}u=std::move(w);return true;}
void save(const Prefix&u,const I&K,int n,const string&file){ofstream f(file);f<<n<<"\n"<<K<<"\n"<<u.a<<" "<<u.b<<" "<<u.cs.size()<<"\n";for(auto&c:u.cs)f<<c.p<<" "<<c.q<<"\n";}
int main(int argc,char**argv){int n=argc>1?stoi(argv[1]):1000;Prefix u{2047,3071,{{2048,1535},{512,767},{3584,3967},{2816,4031},{384,3038},{960,3054},{224,3148774},{2621288,3145735},{7077811,2883586},{2883545,131073}}};I K=0;int i=0;if(argc>2){ifstream f(argv[2]);size_t len;f>>i>>K>>u.a>>u.b>>len;u.cs.resize(len);for(auto&c:u.cs)f>>c.p>>c.q;}
auto start=chrono::steady_clock::now();for(;i<n;++i){int why=0;if(!cycle(u,K,why)){cout<<"failed cycle "<<i<<" guard "<<why<<"\n";return 2;}if((i+1)%1000==0)cout<<"cycle "<<i+1<<" cells "<<u.cs.size()<<" a bits "<<boost::multiprecision::msb(u.a)+1<<" K bits "<<boost::multiprecision::msb(K)+1<<" time "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;}
save(u,K,i,"prefix-state.txt");cout<<"final cycle "<<i<<" cells "<<u.cs.size()<<" a bits "<<boost::multiprecision::msb(u.a)+1<<" K bits "<<boost::multiprecision::msb(K)+1<<"\n";for(size_t j=u.cs.size()>10?u.cs.size()-10:0;j<u.cs.size();++j)cout<<u.cs[j].p<<" "<<u.cs[j].q<<"\n";}
