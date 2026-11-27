// Reuse the already validated graph solver; seed novel leaves with the
// parameter choices seen in accepted Raw47 proof artifacts.
#include <bits/stdc++.h>
#define main raw47_original_main
#include "../agent12-raw47-rungraph/run_search.cpp"
#undef main

int main(int argc,char**argv) {
  if(argc < 2 || std::string(argv[1])!="portfolio")
    return raw47_original_main(argc,argv);
  if(argc!=4) return 2;
  std::ifstream bank(argv[2]);
  if(!bank) return 2;
  int cap=std::stoi(argv[3]);
  std::vector<std::pair<Params,Params>> params;
  std::string line;
  while(std::getline(bank,line)){
    std::istringstream in(line); std::vector<int> v; int x;
    while(in>>x)v.push_back(x);
    if(v.empty())continue;
    if(v.size()!=5 && v.size()!=10)return 2;
    Params a{v[0],v[1],v[2],v[3],bool(v[4])}, b=a;
    if(v.size()==10)b={v[5],v[6],v[7],v[8],bool(v[9])};
    params.push_back({a,b});
  }
  if(params.empty())return 2;
  int id;std::string table;
  while(std::cin>>id>>table){
    bool solved=false;
    for(auto [a,b]:params){
      Solver s(table,a,b,cap);
      if(!s.run())continue;
      std::cout<<id<<' '<<table<<' '<<a.lag<<' '<<a.k<<' '<<a.t<<' '<<a.m<<' '<<a.pair;
      if(std::tie(a.lag,a.k,a.t,a.m,a.pair)!=std::tie(b.lag,b.k,b.t,b.m,b.pair))
        std::cout<<' '<<b.lag<<' '<<b.k<<' '<<b.t<<' '<<b.m<<' '<<b.pair;
      std::cout<<' '<<s.states.size()<<' '<<s.d[0].ws.size()<<' '<<s.d[1].ws.size()<<'\n';
      solved=true;break;
    }
    if(!solved)std::cerr<<id<<' '<<table<<'\n';
  }
  return 0;
}
