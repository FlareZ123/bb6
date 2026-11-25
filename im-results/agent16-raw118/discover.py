#!/usr/bin/env python3
"""Reproduce raw118 candidate searches. Only Lean source checks certify a leaf."""
from pathlib import Path
import argparse, hashlib, json, subprocess

ROOT=Path(__file__).resolve().parent
IM=ROOT.parent
PARENT="1RB---_1RC---_0RD---_1LD1RE_---0LE_------"
SHA="00b82e8ded916fb719ebfd627d29da4bbf86659039b3b7889ff60a3f9ae396f9"
FAR_BANKS=["agent47-raw112-cut/far-bank.txt","agent47-raw115-cut/far-bank.txt","agent47-raw114-cut/all-far-bank.txt"]
EXTRA_BANKS=["agent19-tnf-raw71/dfa-bank.txt","agent19-tnf-raw77/dfa-bank.txt","agent19-tnf-raw81/dfa-bank.txt","agent19-tnf-raw98/dfa.txt","agent31-three-hole-tnf/four_hole_dfas.txt","agent7-far/f1-siblings/dfa-overrides.txt","agent7-far/wide132/dfa-overrides.txt","agent7-far/wide133/dfa-overrides.txt","agent7-far/depth-eight-smt-deeper-hits-45526798647.md","agent7-far/depth-eight-smt-roster-hits-45525504552.md"]
LATE=r"""
#include <array>
#include <vector>
#include <string>
#include <iostream>
#include <fstream>
using namespace std;
int main(int argc,char**argv){int lim=stoi(argv[2]);ifstream f(argv[1]);string s;int i=0;vector<unsigned char>t(2*lim+3);while(f>>s){fill(t.begin(),t.end(),0);array<int,12> p;string a;for(char c:s)if(c!='_')a+=c;for(int j=0;j<12;j++)p[j]=a[3*j]=='-'?-1:4*(a[3*j+2]-'A')+2*(a[3*j]-'0')+(a[3*j+1]=='R');int q=0,h=lim+1;for(int n=0;n<=lim;n++){int slot=2*q+t[h],x=p[slot];if(x<0){cout<<i<<":"<<n<<":"<<slot<<"\n";break;}t[h]=(x>>1)&1;h+=(x&1)?1:-1;q=x/4;}i++;}}
"""
NGRAM_MAIN=r"""
int main(int argc,char**argv){int maxk=stoi(argv[1]);int id;string s;while(cin>>id>>s){s.erase(remove(s.begin(),s.end(),'_'),s.end());for(int k=1;k<=maxk;k++){NGram a(s,k);if(a.check()){cout<<id<<':'<<k<<':'<<a.todo.size()<<'\n';break;}if(a.limit)break;}}}
"""
def compile(src,dst):
    subprocess.run(["g++","-O3","-std=c++17",str(src),"-o",str(dst)],check=True)
def out(args,**kwargs):
    return subprocess.check_output([str(x) for x in args],text=True,**kwargs)
def lines(path,values):
    path.write_text("".join(str(x)+"\n" for x in values))
def extra_bank():
    bank=set()
    def add(s):
        if len(s)<3 or len(s)%2!=1 or len(s)>41 or s[:2] not in ("00","10"):return
        if not all(c in "0123456789abcdefghij" for c in s[1:]):return
        if all(int(c,36)<(len(s)-1)//2 for c in s[1:]):bank.add(s)
    for p in EXTRA_BANKS:
        for line in (IM/p).read_text().splitlines():
            if "-bank" in p:
                for x in line.split(","):add(x)
            elif p.endswith("/dfa.txt"):
                a=line.split(":");add(a[1] if len(a)>1 else "")
            elif "four_hole_dfas" in p:
                a=line.split()
                if len(a)==6:add(a[4]+a[5])
            elif "overrides" in p:
                a=line.split()
                if len(a)==3:add(a[0]+a[1])
            elif line.startswith("HIT "):
                a=line.split();i=a.index("DFA");j=a.index("MASK")
                add(a[i-1]+"".join("0123456789abcdefghijklmnopqrstuvwxyz"[int(x)] for x in a[i+1:j]))
    assert len(bank)==421,len(bank)
    return bank

def discover(work):
    work=work.resolve();work.mkdir(parents=True,exist_ok=True)
    compile(IM/"agent2-tnf-raw99/enumerate.cpp",work/"enumerate")
    compile(IM/"agent47-raw114-cut/seeded_far.cpp",work/"far")
    (work/"late.cpp").write_text(LATE);compile(work/"late.cpp",work/"late")
    ns=(IM/"agent47-raw111-cut/ngram_sparse.cpp").read_text()
    (work/"ngram.cpp").write_text(ns.split("int main(")[0].replace("todo.size()>2000000","todo.size()>200000")+NGRAM_MAIN)
    compile(work/"ngram.cpp",work/"ngram")
    print(out([work/"enumerate",PARENT],cwd=work))
    raw=(work/"open.txt").read_bytes()
    assert hashlib.sha256(raw).hexdigest()==SHA
    rows=raw.decode().splitlines()
    assert len(rows)==6085
    banks=set().union(*((IM/p).read_text().split() for p in FAR_BANKS))
    assert len(banks)==150
    lines(work/"bank.txt",sorted(banks))
    def far_search(ids,bank,maxd):
        lines(work/"far_input.txt",(rows[i] for i in ids));lines(work/"far_bank.txt",sorted(bank))
        s=out([work/"far",work/"far_input.txt",0,len(ids),maxd,work/"far_bank.txt"])
        return {ids[int(i)]:code for i,code in (line.split(":") for line in s.splitlines())}
    far=far_search(list(range(len(rows))),banks,4)
    assert len(far)==4974,len(far)
    missing=[i for i in range(len(rows)) if i not in far]
    lines(work/"late_input.txt",(rows[i] for i in missing))
    late={}
    for line in out([work/"late",work/"late_input.txt",1000000]).splitlines():
        j,n,s=map(int,line.split(":"));i=missing[j]
        assert rows[i].count("---")==1
        late[i]=(n,s)
    assert len(late)==67 and late[439]==(756495,3)
    pending=[i for i in missing if i not in late]
    ng={int(i):(int(k),int(n)) for i,k,n in (line.split(":") for line in out([work/"ngram",16],input="".join(f"{i} {rows[i]}\n" for i in pending)).splitlines())}
    assert len(ng)==679 and sum(n for k,n in ng.values())==635684,(len(ng),sum(n for k,n in ng.values()))
    hard=[i for i in pending if i not in ng];assert len(hard)==365
    lines(work/"hard.txt",(f"{i} {rows[i]}" for i in hard))
    more=extra_bank()
    additional=far_search(hard,more,0);assert len(additional)==73,len(additional)
    hard=[i for i in hard if i not in additional]
    far.update(additional)
    additional=far_search(hard,banks|more,5);assert len(additional)==18,len(additional)
    far.update(additional)
    hard=[i for i in hard if i not in additional]
    lines(work/"hard2.txt",(f"{i} {rows[i]}" for i in hard))
    result=dict(far=far,late=late,ngram=ng,hard=hard)
    (work/"candidates.json").write_text(json.dumps(result,sort_keys=True)+"\n")
    print("FAR",len(far),"late",len(late),"ngram",len(ng),"hard",len(hard))
    return rows,result

if __name__=="__main__":
    ap=argparse.ArgumentParser();ap.add_argument("work",type=Path);args=ap.parse_args()
    discover(args.work)
