// Candidate search; the Lean certificate checker is the authority.
#define main large_far_original_main
#include "../agent7-far/large_far.cpp"
#undef main
#include <algorithm>
void canonicalDFAs(int d,D& a,int mx,std::vector<D>& out){
 if(int(a.size())==2*d){if(mx==d-1)out.push_back(a);return;}
 if(int(a.size()/2)>mx)return;
 for(int j=0;j<=std::min(d-1,mx+1);j++){a.push_back(j);canonicalDFAs(d,a,std::max(j,mx),out);a.pop_back();}
}
D parseD(const std::string&s){D a;for(size_t i=1;i<s.size();i++)a.push_back(s[i]>='a'?s[i]-'a'+10:s[i]-'0');return a;}
std::string code(const D&a,int rev){std::string s(1,'0'+rev);for(int x:a)s+=x<10?'0'+x:'a'+x-10;return s;}
int main(int argc,char**argv){
 if(argc!=6){std::cerr<<"usage: seeded_far roster start end maxd seeds\n";return 1;}
 std::ifstream input(argv[1]),sf(argv[5]);std::string s;std::vector<std::string> rows;
 while(input>>s)rows.push_back(s);
 std::vector<std::pair<D,int>> seeds;
 while(sf>>s){D a=parseD(s);if(a.empty()||a.size()%2||a[0]!=0||*std::max_element(a.begin(),a.end())>=int(a.size()/2))continue;seeds.emplace_back(a,s[0]-'0');}
 int maxd=atoi(argv[4]),start=atoi(argv[2]),end=atoi(argv[3]);std::vector<D> dfas;
 for(int d=1;d<=maxd;d++){D a{0};canonicalDFAs(d,a,0,dfas);}
 int hits=0;for(int i=start;i<end&&i<(int)rows.size();i++){M m=parse(rows[i]);bool got=false;
 for(auto [a,rev]:seeds)if(far(m,a,rev).safe){std::cout<<i<<":"<<code(a,rev)<<"\n";got=true;break;}
 if(!got)for(int rev=0;rev<2&&!got;rev++)for(const auto&a:dfas)if(far(m,a,rev).safe){std::cout<<i<<":"<<code(a,rev)<<"\n";seeds.insert(seeds.begin(),{a,rev});got=true;break;}hits+=got;}
 std::cerr<<"start="<<start<<" end="<<end<<" hits="<<hits<<std::endl;
}
