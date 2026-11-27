// Search only unresolved leaves, using the existing exact sparse closure discovery.
#define main ngram_dump_main
#include "../agent32-raw59/ngram_asym.cpp"
#undef main
int main() {
 int id; string s;
 while(cin>>id>>s){
  bool solved=false;
  for(int total=2;total<=24&&!solved;total++)for(int l=1;l<total&&!solved;l++){
   int r=total-l;if(l>18||r>18)continue;
   NGram a(s,l,r,100000);
   if(a.check()){cout<<id<<' '<<s<<' '<<l<<' '<<r<<'\n'<<flush;solved=true;}
  }
 }
}
