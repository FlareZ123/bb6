#!/usr/bin/env python3
"""Produce exact original-Z0 source proofs of the first undefined-slot exposure.
No native_decide, sorry or axiomatic oracle; each finite run segment reduces by rfl.
"""
import argparse,hashlib,json,sys
from collections import deque
from pathlib import Path
from detect_pump import parse,next_step

def bits(s):return '['+','.join('true' if c=='1' else 'false' for c in s)+']'
def expr(z):q,l,r=z;return f'⟨{q},{bits(l)},{bits(r)}⟩'
def generate(table,n,out,chunk=170):
    moves=parse(table);q=0;L=deque();R=deque()
    checkpoints=[(0,(0,'',''))]
    for t in range(1,n+1):
        q=next_step(q,L,R,moves)
        assert q is not None,(table,t,'undefined early')
        if t%chunk==0 or t==n:
            checkpoints.append((t,(q,''.join(L),''.join(R))))
    scanned=L[0] if L else '0'
    assert moves[2*q+int(scanned)]=='---',(q,scanned,moves[2*q+int(scanned)])
    ns='BB6.Agent7D100Exposure'+hashlib.sha256(table.replace('_','').encode()).hexdigest()[:12]
    lines=['import SweepPumping','set_option maxRecDepth 100000','set_option maxHeartbeats 0',
        f'namespace {ns}','open BB6Coverage BB6Coverage.Agent31Pump',
        'def table : PartialMachine := fun s => match s.1.val,s.2 with']
    for i,m in enumerate(moves):
        if m=='---':continue
        lines.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(m[0]=="1").lower()},{str(m[1]=="R").lower()},{ord(m[2])-65}⟩)')
    lines.append('  | _,_ => none')
    for i,((t0,z0),(t1,z1)) in enumerate(zip(checkpoints,checkpoints[1:])):
        lines.append(f'theorem part{i:03d} : run0 table {t1-t0} {expr(z0)} = some {expr(z1)} := by rfl')
    final=expr(checkpoints[-1][1]);lines.append(f'theorem reached : run0 table {n} ⟨0,[],[]⟩ = some {final} := by')
    for i in range(len(checkpoints)-1):
        if i==0:lines.append('  have h0 := part000')
        else:lines.append(f'  have h{i} := join0 h{i-1} part{i:03d}')
    lines.append(f'  simpa using h{len(checkpoints)-2}')
    lines += [f'theorem hole : table ({q}, {str(scanned=="1").lower()}) = none := by decide',
       '#print axioms reached','#print axioms hole',f'end {ns}']
    out=Path(out);out.parent.mkdir(parents=True,exist_ok=True)
    src='\n'.join(lines)+'\n';out.write_text(src)
    info=dict(table=table,undefined_after=n,slot=f'{chr(q+65)}{scanned}',namespace=ns,
        source_sha256=hashlib.sha256(src.encode()).hexdigest(),chunks=len(checkpoints)-1)
    out.with_suffix('.json').write_text(json.dumps(info,indent=2)+'\n')
    return info
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('table');ap.add_argument('n',type=int);ap.add_argument('out');ap.add_argument('--chunk',type=int,default=170)
    x=ap.parse_args();print(json.dumps(generate(x.table,x.n,x.out,x.chunk)))
