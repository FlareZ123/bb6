#!/usr/bin/env python3
"""Reuse exact Box4 one-halt scans on the new Box28 D0=14,D1=17/18 cut.
Discovery is untrusted. Retain all unresolved rows and exact mass accounting.
Do not repeat completed targets or claim a source bound from this script.
"""
from pathlib import Path
from collections import Counter
from math import prod
import argparse, json, os, shutil, subprocess, sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'agent13-raw10-box4'
BRANCH = HERE.parent / 'agent13-raw10-box3-branches'
TARGETS = (1,3,8,9,10,11)

def call(*args):
    subprocess.run([str(x) for x in args], check=True)

def prepare(work, fixed):
    for n in ('scan.cpp', 'treegen.cpp'):
        s = (BASE/n).read_text()
        f = 'int fx[6]={8,14,11,7,17,4};'
        d = 'for(int i=0;i<12;i++){if(i<6)ds[i]={fx[i]};else if(i==target)ds[i]={0};else for(int v=1;v<=24;v++)if(i!=6||v!=9)ds[i].push_back(v);}'
        assert s.count(f)==s.count(d)==1
        s=s.replace(f,'int fx[12]={'+','.join(map(str,fixed))+'};')
        s=s.replace(d,'for(int i=0;i<12;i++){if(fx[i]>=0)ds[i]={fx[i]};else if(i==target)ds[i]={0};else for(int v=1;v<=24;v++)ds[i].push_back(v);}')
        s=s.replace('for(int j=6;j<12;j++)','for(int j=0;j<12;j++)')
        (work/n).write_text(s)
    (work/'classify.cpp').write_text((BASE/'classify.cpp').read_text().replace('if(i!=6||v!=9)',''))
    shutil.copyfile(BRANCH/'rle_scan.cpp',work/'rle_scan.cpp')
    for n in ('scan','classify','treegen','rle_scan'):
        call('g++','-O3','-std=c++17',work/(n+'.cpp'),'-o',work/n)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--d1',type=int,choices=(17,18),required=True)
    p.add_argument('--work',type=Path,required=True)
    p.add_argument('--targets',type=int,nargs='+',default=TARGETS)
    args=p.parse_args()
    fixed=[8,-1,11,-1,11,13,14,args.d1,-1,-1,-1,-1]
    work=args.work.resolve();work.mkdir(parents=True,exist_ok=True);os.chdir(work)
    prepare(work,fixed)
    sys.path.insert(0,str(BASE))
    import finish
    allstats={};max_halt=(0,None)
    for target in args.targets:
        assert target in TARGETS
        ds=tuple((v,) if v>=0 else (0,) if i==target else tuple(range(1,25)) for i,v in enumerate(fixed))
        def mass(t):return prod(len(ds[i]) for i,v in enumerate(t) if v<0)
        call(work/'scan',target)
        call(work/'classify',target)
        pending=[tuple(map(int,l.split())) for l in open(f'hard{target}.txt') if l.strip()]
        initial_mass=sum(map(mass,pending));terminal_mass=0
        long=[];rlestart=[];counts=Counter()
        while pending:
            t=pending.pop();z=finish.trace_long(t,limit=16384,cycle_limit=2048)
            kind=z[0]
            if kind=='hole':
                s=z[2];long.append([t,('hole',s)])
                pending.extend(t[:s]+(v,)+t[s+1:] for v in ds[s]);continue
            terminal_mass+=mass(t);counts[kind]+=1
            if kind in ('halt','cycle','side'):
                long.append([t,z])
                if kind=='halt' and z[1]+1>max_halt[0]:max_halt=(z[1]+1,t)
            else:rlestart.append(t)
        assert initial_mass==terminal_mass
        with open(f'late{target}.json','w') as f:json.dump(long,f)
        with open(f'rlestart{target}.txt','w') as f:
            for t in rlestart:f.write(' '.join(map(str,t))+'\n')
        call(work/'rle_scan',target)
        rr=[tuple(map(int,l.split())) for l in open(f'rlehard{target}.txt') if l.strip()]
        ss=[tuple(map(int,l.split())) for l in open(f'rle{target}.txt') if l.strip()]
        assert sum(map(mass,rr))+sum(mass(t[:12]) for t in ss)==sum(map(mass,rlestart))
        st={'target':target,'late_counts':dict(counts),'late_mass':initial_mass,
            'rle_certified_leaves':len(ss),'open_count':len(rr),
            'open_mass':sum(map(mass,rr)),'open_rows':rr,'late_max_halt':max_halt}
        allstats[target]=st
        print(json.dumps(st),flush=True)
        with open('summary.json','w') as f:json.dump(allstats,f,indent=2)
    print('Final residual leaves',sum(s['open_count'] for s in allstats.values()),flush=True)

if __name__=='__main__':main()
