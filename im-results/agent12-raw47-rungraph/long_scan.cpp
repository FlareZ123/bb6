#include <bits/stdc++.h>
#include "side_scan.hpp"
using namespace std;
int main(int argc,char**argv){side_scan::Scanner scan;int id;string t;int cap=argc>1?atoi(argv[1]):1000000;while(cin>>id>>t){array<int,12> p;for(int i=0;i<12;i++)p[i]=t[3*i]=='-'?-1:(t[3*i]-'0')*12+(t[3*i+1]=='R')*6+t[3*i+2]-'A';auto a=scan.run(p,cap);cout<<id<<' '<<t<<' '<<a.typ<<' '<<a.n<<' '<<a.s<<' '<<a.e<<' '<<a.k<<' '<<a.dir<<' '<<a.b<<endl;}}
