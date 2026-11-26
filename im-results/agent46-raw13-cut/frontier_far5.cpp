// Untrusted candidate search: exhaustive accessible, canonical DFAs through five states.
#define main strict_frontier_main
#include "frontier_complete.cpp"
#undef main
void enumerateD(int d,DFA& a,int mx,vector<DFA>& out){
 if(int(a.size())==2*d){if(mx==d-1)out.push_back(a);return;}
 if(int(a.size()/2)>mx)return;
 for(int j=0;j<=min(d-1,mx+1);j++){a.push_back(j);enumerateD(d,a,max(j,mx),out);a.pop_back();}
}
int main(){vector<DFA> ds;for(int d=1;d<=5;d++){DFA a{0};enumerateD(d,a,0,ds);}
 string s;while(cin>>s){bool ok=false;for(int rev=0;rev<2&&!ok;rev++)for(auto&d:ds)
 if(far(parse(s),d,rev)){cout<<s<<' '<<rev<<' '<<showD(d)<<'\n';ok=true;break;}
 if(!ok)cerr<<s<<'\n';}
}
