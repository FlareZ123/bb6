// Escalate exact prefix/side-cycle search only on unresolved leaves.
#define main enumerate_original_main
#include "../agent32-linear-side-cycle/enumerate_tnf.cpp"
#undef main
int main(int argc,char**argv) {
 int id; string s;int cap=argc>1?atoi(argv[1]):100000;
 while(cin>>id>>s){auto p=parse(s);auto a=scanner.run(p,cap);
  if(a.typ==2) cout<<id<<" cycle "<<a.e<<' '<<a.k<<' '<<a.dir<<' '<<a.b<<'\n';
  else if(a.typ==1 && count(p.begin(),p.end(),-1)==1) cout<<id<<" last "<<a.n<<' '<<a.s<<'\n';
  else if(a.typ==1) cerr<<id<<" query "<<a.n<<' '<<a.s<<'\n';
  else cerr<<id<<" open\n";
 }
}
