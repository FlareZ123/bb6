#!/usr/bin/env python3
"""Find finite block-FAR certificates only for saved residual rows.
Each attempt has a finite time/memory cap; do not re-enumerate the rectangle.
All results are untrusted until their exact table and invariant pass Lean.
"""
import argparse, json, os, resource, subprocess, sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
FAR=HERE.parent/'agent13-block-far'
from cuts import stem, second_index

def code_table(row):
    def code(v):
        if v<=0:return '---'
        v-=1
        return f'{v//2%2}{"R" if v%2 else "L"}{chr(65+v//4)}'
    return '_'.join(code(row[i])+code(row[i+1]) for i in range(0,12,2))

def one(row, param, out, name):
    sys.path.insert(0,str(FAR))
    from generate_multi import generate
    width,cap,mod,runs,flip,mode=param
    resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
    d=generate(code_table(row),out,width,cap,mod,runs,flip,name,minimize_left=True,left_mode=mode)
    print('CERTIFIED_CANDIDATE',d['left_states'],d['right_nodes'],flush=True)

def main():
    p=argparse.ArgumentParser();p.add_argument('--work',type=Path);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--one');p.add_argument('--param');p.add_argument('--name',default='Box28Far')
    a=p.parse_args()
    if a.one:
        one(json.loads(a.one),json.loads(a.param),a.out,a.name);return
    a.out.mkdir(parents=True,exist_ok=True)
    rows=sorted({tuple(t) for v in json.load(open(a.work/'summary.json')).values() for t in v['open_rows']})
    # Start with small regular languages; widen only when necessary.
    schedule=[]
    for width in (2,3,4,5):
        for mode,cap,mod,runs in [('runs',2,4,3),('suffix',1,1,4),('runs',1,3,4),('suffix',1,1,6),('runs',2,6,5)]:
            for flip in (False,True):schedule.append([width,cap,mod,runs,flip,mode])
    solved=[];open_rows=[]
    (a.out/'far_manifest.json').write_text(json.dumps({'solved':solved,'open_rows':open_rows},indent=2))
    for i,row in enumerate(rows):
        name=f'{stem(row[6],row[second_index(row[6])])}Far{i:02d}'
        for param in schedule:
            try:
                r=subprocess.run([sys.executable,str(Path(__file__).resolve()),'--one',json.dumps(row),'--param',json.dumps(param),'--out',str(a.out),'--name',name],capture_output=True,text=True,timeout=8)
            except subprocess.TimeoutExpired:continue
            if r.returncode==0 and 'CERTIFIED_CANDIDATE' in r.stdout:
                solved.append([row,param]);print('SOLVED',json.dumps([row,param]),r.stdout.splitlines()[-1],flush=True);break
        else:
            open_rows.append(row);print('OPEN',json.dumps(row),flush=True)
        (a.out/'far_manifest.json').write_text(json.dumps({'solved':solved,'open_rows':open_rows},indent=2))
    print('FINAL',len(solved),len(open_rows),flush=True)
if __name__=='__main__':main()
