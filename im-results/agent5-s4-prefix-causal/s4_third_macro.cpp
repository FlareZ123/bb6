// Third-level S4 suffix section. Pipe output of s4_nested_macro --print-offsets
// into this executable. Reuses the original exact G/H source model.
#define BB6_S4_SUFFIX_MACRO_LIBRARY
#include "s4_suffix_macro.cpp"
#include <sstream>
#include <string>
using ThirdPrefix = std::array<uint64_t,7>;
constexpr uint64_t THIRD_PERIOD = 800;

void thirdGp(ThirdPrefix& x,uint64_t c){
    uint64_t a=x[0]+c;
    for(size_t i=0;i<x.size();++i){
        if(i+1==x.size()){x[i]=a/2+((a&1)?0:2);return;}
        if(!(a&1)){x[i]=a/2+2; x[i+1]+=a/2;return;}
        x[i]=a/2;a=x[i+1]+a/2+1;
    }
}
Boundary thirdBoundary(const ThirdPrefix& x,uint64_t c){
    uint64_t a=x[0]+c;
    for(size_t i=0;i<x.size();++i){
        if(!(a&1))return i+1==x.size()?Boundary{1,a/2}:Boundary{0,0};
        if(i+1==x.size())return {2,a/2+1};
        a=x[i+1]+a/2+1;
    }
    return {0,0};
}
void scanLine(const std::string& line,const std::string& label,Tail& dest){
    if(line.rfind(label,0)!=0)return;
    std::istringstream in(line.substr(label.size()));uint64_t a;
    while(in>>a)dest.push_back(a);
}
int main(int argc,char**argv){
    Tail offsets,full;
    std::string line;
    while(std::getline(std::cin,line)){
        scanLine(line,"Offsets:",offsets);
        scanLine(line,"RootTail:",full);
    }
    if(offsets.size()!=4603 || full.size()!=8)return 2;
    Tail out;
    for(auto c:offsets){if(!G(c,full,out))return 3;full.swap(out);}
    if(full.size()<7)return 4;
    ThirdPrefix p{},start{};
    std::copy_n(full.begin(),7,p.begin());start=p;
    Tail suffix(full.begin()+7,full.end());
    Tail normalized;
    uint64_t nAdd=0,nG=0,pending=0;
    for(uint64_t t=0;t<THIRD_PERIOD;++t){
        for(auto c:offsets){
            auto e=thirdBoundary(p,c);
            if(e.kind==1){nAdd++;pending+=e.d;}
            if(e.kind==2){nG++;normalized.push_back(e.d+pending);pending=0;}
            thirdGp(p,c);
        }
    }
    assert(p==start);
    assert(nAdd==28830 && nG==28802 && pending==0);
    uint64_t sum=std::accumulate(normalized.begin(),normalized.end(),uint64_t{0});
    assert(sum==219902325555142396ULL);
    assert(sum+2*nG==1024ULL*T*12800*THIRD_PERIOD);
    Tail accelerated=suffix;
    for(auto c:normalized){if(!G(c,accelerated,out))return 5;accelerated.swap(out);}
    for(uint64_t t=0;t<THIRD_PERIOD;++t){
        for(auto c:offsets){
            if(!G(c,full,out))return 6;
            full.swap(out);
        }
    }
    assert(full.size()>=7);
    assert(std::equal(full.begin(),full.begin()+7,start.begin()));
    assert(std::equal(full.begin()+7,full.end(),accelerated.begin(),accelerated.end()));
    std::cout<<"Third section prefix:";for(auto x:start)std::cout<<' '<<x;
    std::cout<<"\nHead additions="<<nAdd<<", effective G gates="<<nG<<", pending="<<pending;
    std::cout<<"\nTotal offsets="<<sum<<", source-return mass gain="<<1024ULL*T*12800*THIRD_PERIOD;
    std::cout<<"\nPASS full R^800 equals third-level suffix word for modeled root\n";
    if(argc>1 && std::string(argv[1])=="--print-offsets"){
        std::cout<<"Offsets:";for(auto c:normalized)std::cout<<' '<<c;
        std::cout<<"\nRootTail:";for(auto c:suffix)std::cout<<' '<<c;
        std::cout<<'\n';
    }
}
