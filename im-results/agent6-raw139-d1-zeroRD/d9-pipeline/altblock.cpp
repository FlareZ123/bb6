// Untrusted alternative witness search; kernel independently checks emitted witness.
#define main original_main
#include "strong.cpp"
#undef main
int main(int argc,char**argv){ifstream f(argv[1]);int id;string s;while(f>>id>>s){Table p;size_t at=0;for(int i=0;i<12;i++){auto en=s.find(',',at);p[i]=stoi(s.substr(at,en-at));at=en+1;}long best=1000000000;string recipe;for(int w:{2,3,4})for(int r:{2,3,4})for(int m:{2,3,4,5,7})for(int flip:{0,1})for(int phase:{0,1}){Graph g(p,w,1,m,r,flip,phase,15000);if(!g.check())continue;long cost=g.events.size()+g.left.size()*(1<<w)*12;if(cost<best){best=cost;recipe=to_string(w)+" 1 "+to_string(m)+" "+to_string(r)+" "+to_string(flip)+" "+to_string(phase)+" "+to_string(g.left.size())+" "+to_string(g.nodes.size())+" "+to_string(g.events.size());}if(best<400)goto done;}done: if(recipe.size())cout<<id<<" block "<<recipe<<' '<<s<<endl;else cout<<id<<" none "<<s<<endl;}}
