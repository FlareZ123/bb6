"""Generate support-complete sparse block-FAR proofs for expensive bank entries.

Uses Agent13's ActiveSparseFAR soundness theorem (specialized to widths 2/4).
No externally supplied coverage claim is trusted: missing sparse keys have no
transition by definition, and every nonempty row is checked by Lean's kernel.
"""
from collections import Counter
from pathlib import Path
import json
import re
import sys
from emit_lean import ls, boolean
from minimize import minimize

RANGE = 'BB6.Agent6D1RangeCheck'

def tree(items, default, key='i'):
    """Balanced exact finite-map lookup with a literal default."""
    if not items:
        return default
    if len(items) == 1:
        k, value = items[0]
        return f'if {key} = {k} then {value} else {default}'
    mid = len(items)//2
    return f'if {key} < {items[mid][0]} then ({tree(items[:mid],default,key)}) else ({tree(items[mid:],default,key)})'

def scalar(name, xs):
    default = Counter(xs).most_common(1)[0][0]
    bits = max(1,max(xs).bit_length()); stride = 16
    def pack(ys): return sum(v << (bits*j) for j,v in enumerate(ys))
    fallback = pack([default]*stride)
    groups=[]
    for i in range(0,len(xs),stride):
        ys=xs[i:i+stride]; val=pack(ys+[default]*(stride-len(ys)))
        if val != fallback: groups.append((i//stride,hex(val)))
    return f'def {name}Chunks (i : Nat) : Nat := {tree(groups,hex(fallback))}\ndef {name} (i : Nat) : Nat := ({name}Chunks (i/{stride}) >>> ({bits}*(i%{stride}))) % (2^{bits})'

def list_map(name, ty, rows):
    items=[(i,value) for i,value in enumerate(rows) if value != '[]']
    return f'def {name} (i : Nat) : List {ty} := {tree(items,"[]")}'

def checks(name,size,fn,chunk=8):
    lines=[]
    def rec(lo,n):
        label=f'{name}_{lo}_{n}'
        t=f'private theorem {label} : {RANGE}.check {size-1} ({fn}) {lo} {n} = true := '
        if n<=chunk:
            lines.append(t+'by decide +kernel')
        else:
            m=n//2;x=rec(lo,m);y=rec(lo+m,n-m)
            lines.append(t+f'{RANGE}.join {size-1} ({fn}) {lo} {m} {n-m} {x} {y}')
        return label
    label=rec(0,size)
    lines.append(f'private theorem {name}_full : (List.finRange {size}).all ({fn}) = true := {RANGE}.full {size-1} ({fn}) {label}')
    return lines

def emit(c, chunk=8):
    c=minimize(c);i,p,w,D,N,flip=c['id'],c['p'],c['w'],c['D'],c['N'],c['flip']
    A=1<<w; suffix='' if w==3 else str(w); ns='BB6BlockFAR'+suffix; sem='BB6BlockFAR4' if w==4 else 'BB6BlockFAR'
    moves=['none' if x==24 else f'some ⟨{boolean((x//2)%2)},{boolean((x%2)^flip)},{x//4}⟩' for x in p]
    s=[f'namespace H{i}',f'def ctr : PartialMachine := FAR.fromCodes {ls(p)}',f'def machine : {sem}.Table := fun q b => ({ls(moves)} : List (Option {sem}.Move))[2*q.val+b.toNat]?.getD none']
    s.append(list_map('pushRows','(Nat × Nat)',[ls(f'({a},{x})' for a,x in enumerate(c['push'][l*A:(l+1)*A]) if x) for l in range(D)]))
    s.append(scalar('controlCodes',c['ctrl']))
    s.append(scalar('auxiliaryCodes',c['aux']))
    s.append(list_map('predecessorCodes','Nat',[ls(xs) for xs in c['pred']]))
    s.append(list_map('edgeRows','(Nat × List Nat)',[ls(f'({a},{ls(ts)})' for a,ts in enumerate(c['edges'][v*A:(v+1)*A]) if ts) for v in range(N)]))
    s.append(scalar('zeroNextCodes',c['znext']))
    s.append(f'def cert : {ns}.ActiveData {D-1} {N-1} := ⟨0,pushRows,controlCodes,auxiliaryCodes,predecessorCodes,edgeRows,{hex(sum(v<<j for j,v in enumerate(c["zero"])))},zeroNextCodes⟩')
    s.append('private theorem base_ok : cert.sparse.baseCheck = true := by decide +kernel')
    s+=checks('pred',D,'cert.fastPredAt',chunk)
    s+=checks('rows',D,'cert.fastRowsAt machine',chunk)
    s.append('theorem valid : cert.sparse.Valid machine := cert.valid_of_checks machine base_ok pred_full rows_full')
    s.append(f'theorem forever : ∀ k, ∃ c, {sem}.run machine k {sem}.primBlank = some c := cert.sparse.sound machine valid')
    if flip:
        s += [f'theorem same : FAR.reflectPartial ctr = {sem}.partialTable machine := tableOK_sound _ _ (by decide)',f'theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m := FAR.reflectNever m ({sem}.transfer_never machine (reflectTable m) (by simpa only [← same] using FAR.reflectCompatible ctr m hm) forever)']
    else:
        s += [f'theorem same : ctr = {sem}.partialTable machine := tableOK_sound _ _ (by decide)',f'theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m := {sem}.transfer_never machine m (by simpa only [← same] using hm) forever']
    s += ['#print axioms never',f'end H{i}']
    return '\n'.join(s)+'\n'

def replace(source,cert,chunk=8):
    i=cert['id']; suffix='' if cert['w']==3 else str(cert['w'])
    source,n=re.subn(rf'^namespace H{i}\n.*?^end H{i}\n',lambda m:emit(cert,chunk),source,flags=re.M|re.S)
    assert n==1,(i,n)
    for module in ['D1RangeCheck','ActiveSparseFAR'+suffix]:
        if f'import {module}\n' not in source:source=f'import {module}\n'+source
    return source

if __name__=='__main__':
    root=Path(sys.argv[1]); ns=sys.argv[2]; batch=int(sys.argv[3]); ids=set(map(int,sys.argv[4:])); found=set()
    certs={c['id']:c for c in map(json.loads,(root/'certs.jsonl').read_text().splitlines()) if c['id'] in ids}
    if (root/'alt.jsonl').exists():
        certs.update({c['id']:c for c in map(json.loads,(root/'alt.jsonl').read_text().splitlines()) if c['id'] in ids})
    assert set(certs)==ids, set(certs)^ids
    for i,c in certs.items():
        assert c['type']=='block',c['type']
        path=root/'src'/f'{ns}Bank{(i-1)//batch:03d}.lean'
        path.write_text(replace(path.read_text(),c))
        print(ns,i,'sparse',c['w'],c['D'],c['N'])
