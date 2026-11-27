// Exact table-keyed grafts and partial coverage. Candidate generation only.
#define AGENT46_FRONTIER_LIBRARY
#include "frontier_complete.cpp"
set<string> grafts;
map<string,pair<int,int>> lateQueries;
int graftSolve(Table p,int cut,int holes){
 if(nodes.size()>=300000)throw runtime_error("node cap");
 int i=nodes.size();nodes.push_back({});string raw=show(p);
 if(grafts.count(raw)){nodes[i].raw=raw;nodes[i].a.typ=8;return i;}
 if(autoTables.count(raw)){nodes[i].raw=raw;nodes[i].a.typ=6;return i;}
 if(auto it=lateQueries.find(raw);it!=lateQueries.end()){
   if(holes!=1)throw runtime_error("late query must be last hole");
   nodes[i].raw=raw;nodes[i].a={9,it->second.first,it->second.second,0,0,0,0};return i;
 }
 if(auto ov=overrides.find(raw);ov!=overrides.end()){
   const auto&[rev,d]=ov->second;nodes[i].raw=raw;nodes[i].a.typ=5;nodes[i].df=showD(d);nodes[i].rev=rev;return i;
 }
 int m=mask(p);if(m){nodes[i].a={3,m,0,0,0,0,0};return i;}
 auto a=classify<120,256,120>(p);if(!a.typ)a=classify<1000,2048,256>(p);
 if(!a.typ){
   nodes[i].raw=raw;
   for(const auto&d:bank)for(int rev=0;rev<2;rev++)if(far(p,d,rev)){nodes[i].a.typ=5;nodes[i].df=showD(d);nodes[i].rev=rev;return i;}
   auto late=classify<1000,2048,1000>(p);if(late.typ==2){nodes[i].a=late;return i;}
   nodes[i].a.typ=7;return i;
 }
 nodes[i].a=a;if(a.typ==2||holes==1)return i;
 nodes[i].a.typ=4;
 for(int q=min(cut,5);q>=0;q--)for(int w=0;w<2;w++)for(int r=0;r<2;r++){
  int x=12*w+6*r+q;p[a.s]=x;int j=graftSolve(p,max(cut,q+1),holes-1);nodes[i].child[x]=j+1;
 }
 return i;
}
void graftEmit(int i){
 const auto&n=nodes[i];auto a=n.a;
 if(a.typ==7||a.typ==8){cout<<"[\""<<(a.typ==7?"open":"graft")<<"\",\""<<n.raw<<"\"]";return;}
 if(a.typ==9){cout<<"[\"late\",\""<<n.raw<<"\","<<a.n<<','<<a.s<<']';return;}
 if(a.typ!=4){emit(i);return;}
 cout<<"[\"split\","<<a.n<<','<<a.s<<",[";
 for(int j=0;j<24;j++){if(j)cout<<',';if(n.child[j])graftEmit(n.child[j]-1);else cout<<"null";}cout<<"]]";
}
int main(int argc,char**argv){
 if(argc!=6)return 2;
 ifstream f(argv[1]),g(argv[2]),h(argv[3]),j(argv[4]),k(argv[5]);if(!f||!g||!h||!j||!k)return 2;
 string s,d;int rev,n,slot;
 while(f>>d)bank.push_back(parseD(d));
 while(g>>s>>rev>>d)overrides[s]={bool(rev),parseD(d)};
 while(h>>s)autoTables.insert(s);
 while(j>>s)grafts.insert(s);
 while(k>>s>>n>>slot)lateQueries[s]={n,slot};
 int cut,holes;while(cin>>s>>cut>>holes){nodes.clear();graftEmit(graftSolve(parse(s),cut,holes));cout<<'\n';}
}
