// Reuse the exact 127-step discovery trace implementation.
#define main original_scan_main
#include "scan.cpp"
#undef main
int main(int argc,char**argv){
 int target=atoi(argv[1]);vector<int> ds[12];int fx[6]={8,14,11,7,17,4};
 for(int i=0;i<12;i++){if(i<6)ds[i]={fx[i]};else if(i==target)ds[i]={0};else for(int v=1;v<=24;v++)if(i!=6||v!=9)ds[i].push_back(v);}
 T root;uint64_t total=1;uint32_t full[12]={};for(int i=0;i<12;i++){root[i]=ds[i].size()==1?ds[i][0]:-1;total*=ds[i].size();for(int v:ds[i])full[i]|=1u<<v;}
 vector<array<uint32_t,12>> boxes;ifstream in("greedyboxes.txt");array<uint32_t,12>b;while(in>>b[0]){for(int i=1;i<12;i++)in>>b[i];boxes.push_back(b);}
 int words=(boxes.size()+63)/64;vector<uint64_t> idx[12][26];for(int j=6;j<12;j++)for(int v=0;v<26;v++){idx[j][v].resize(words);uint32_t m=v==25?full[j]:1u<<v;for(size_t i=0;i<boxes.size();i++)if((m&~boxes[i][j])==0)idx[j][v][i/64]|=1ull<<(i%64);}
 auto find=[&](const T&t){for(int w=0;w<words;w++){uint64_t x=~0ull;for(int j=6;j<12;j++){x&=idx[j][t[j]<0?25:t[j]][w];if(!x)break;}if(x)return 64*w+__builtin_ctzll(x);}return -1;};
 vector<T> stk{root};uint64_t count[6]={},mass[6]={};int mx=0;T best{};ofstream out("tree"+to_string(target)+".txt");
 auto start=chrono::steady_clock::now();
 while(!stk.empty()){
  auto t=stk.back();stk.pop_back();int id=find(t);Res z=id>=0?Res{5,id,0,0,false,0}:trace(t);count[z.kind]++;
  if(z.kind==HOLE){for(auto it=ds[z.s].rbegin();it!=ds[z.s].rend();++it){auto c=t;c[z.s]=*it;stk.push_back(c);}out<<"b "<<z.s<<'\n';continue;}
  uint64_t m=1;for(int i=0;i<12;i++)if(t[i]<0)m*=ds[i].size();mass[z.kind]+=m;
  if(z.kind==HALT&&z.n+1>mx){mx=z.n+1;best=t;}
  if(z.kind==OPEN){out<<"o";for(int v:t)out<<' '<<v;out<<'\n';}
  else if(z.kind==5)out<<"a "<<id<<'\n';
  else if(z.kind==HALT)out<<"h "<<z.n<<'\n';
  else out<<"c "<<z.n<<' '<<z.period<<' '<<z.right<<' '<<z.edge<<'\n';
 }
 uint64_t sum=0;for(int i=0;i<6;i++){sum+=mass[i];cerr<<i<<":"<<count[i]<<"/"<<mass[i]<<" ";}cerr<<"total "<<total<<" max "<<mx<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<'\n';assert(sum==total);
}
