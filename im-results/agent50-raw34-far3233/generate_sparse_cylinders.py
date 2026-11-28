#!/usr/bin/env python3
"""Certify sparse residual rows by their halt completions.
Untrusted candidate selection; actual sparse tables are checked in Lean.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path

PUMP_ROW = (21,19,22,12,11,1,16,7,18,20,5,14)
NS = 'BB6.Agent50Raw34Cylinder'

def lean(xs):
    return '[' + ','.join(map(str,xs)) + ']'

def emit_shard(out, index, cases):
    mod = f'Raw34CylinderShard{index:03d}'
    ns = f'{NS}.{mod}'
    body = ['import Raw34CylinderCore', 'set_option maxRecDepth 100000',
            'set_option maxHeartbeats 0', f'namespace {ns}',
            f'open BB6Coverage BB6Coverage.FAR {NS}',
            'def rows : List (List Nat) := [', ',\n'.join('  '+lean(row) for _,row,_ in cases), ']', '']
    for ident,row,x in cases:
        p = f'p{ident}'
        body.append(f'def {p} : PartialMachine := table {lean(row)}')
        if x is None:
            full = f'q{ident}'
            body += [f'def {full} : PartialMachine := table {lean(PUMP_ROW)}',
                     f'theorem eq{ident} : {full} = BB6.Agent50Raw34M2071.p := sameTable_sound _ _ (by decide)',
                     f'theorem never{ident} (m : Machine) (hm : compatible {p} m) : NeverHalts m := by',
                     f'  apply fillCheck_sound {p} {full} (by decide) _ m hm',
                     f'  intro m hm; rw [eq{ident}] at hm; exact BB6.Agent50Raw34M2071.never m hm','']
            continue
        c,ok = f'c{ident}', f'ok{ident}'
        d = x['d']
        pp = f'(reflectPartial {p})' if x['reflect'] else p
        proof = f'({c}).sound {pp} (({c}).fastValid_sound {pp} {ok})'
        proof = f'reflectNever m ({proof} (reflectTable m) (reflectCompatible {p} m hm))' if x['reflect'] else f'{proof} m hm'
        body += [f'def {c} : Data {d} := ⟨0,{lean(x["dfa"])},{lean(x["m0"])},{lean(x["m1"])},{x["z"]}⟩',
                 f'theorem {ok} : ({c}).fastValid {pp} = true := by decide +kernel',
                 f'theorem never{ident} (m : Machine) (hm : compatible {p} m) : NeverHalts m := {proof}', '']
    body += ['theorem never_mem (row : List Nat) (h : row ∈ rows) (m : Machine)',
             '    (hm : compatible (table row) m) : NeverHalts m := by',
             '  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h',
             '  rcases h with ' + ' | '.join('rfl' for _ in cases)]
    body += [f'  · exact never{i} m hm' for i,_,_ in cases]
    body += ['#print axioms never_mem',f'end {ns}','']
    (out/f'{mod}.lean').write_text('\n'.join(body))
    return mod,ns

def main():
    ap = argparse.ArgumentParser()
    for name in ('hard','far4','far5','far6','output'):
        ap.add_argument('--'+name,type=Path,required=True)
    ap.add_argument('--sparse',type=Path,help='Optional independent sparse census; checked exactly')
    ap.add_argument('--shard-size',type=int,default=16)
    a = ap.parse_args()
    assert a.shard_size > 0
    rows = {}
    for line in a.hard.read_text().splitlines():
        ident,*row = map(int,line.split())
        row=tuple(row)
        assert len(row)==12 and all(1<=x<=25 for x in row) and row not in rows
        rows[row]=ident
    assert len(rows)==3233 and set(rows.values())==set(range(3233))
    certs={}
    for f in (a.far4,a.far5,a.far6):
        for line in f.read_text().splitlines():
            x=json.loads(line)
            if not x.get('d'): continue
            ident=x['id'];d=x['d']
            assert ident not in certs and 1<=d<=6 and len(x['dfa'])==2*d
            assert all(len(x[k])==6*d+1 for k in ('m0','m1'))
            certs[ident]=x
    assert set(certs)|{rows[PUMP_ROW]}==set(range(3233)) and rows[PUMP_ROW] not in certs
    # census_f0ld.cpp emits 40 groups of 49 full rows from two-hole cylinders,
    # then 1,273 one-hole HALT completions. Select each all-HALT completion.
    ordered=sorted(rows,key=rows.get)
    assert all(r.count(1)==1 for r in ordered[1960:])
    assert all(r.count(1) in (1,2) for r in ordered[:1960])
    assert all(sum(r.count(1)==2 for r in ordered[i:i+49])==1 for i in range(0,1960,49))
    sparse=[tuple(0 if x==1 else x for x in r) for i,r in enumerate(ordered)
            if (i<1960 and r.count(1)==2) or i>=1960]
    if a.sparse:
        independently=[]
        for line in a.sparse.read_text().splitlines():
            cols=line.split()
            assert cols[0]=='sparse'
            independently.append(tuple(map(int,cols[1:])))
        assert independently==sparse
    assert len(set(sparse))==len(sparse)==1313
    assert collections.Counter(r.count(0) for r in sparse)=={1:1273,2:40}
    cases=[]
    for row in sparse:
        full=tuple(x or 1 for x in row)
        ident=rows[full]
        cases.append((ident,row,certs.get(ident)))
    assert len(set(i for i,_,_ in cases))==len(cases)
    a.output.mkdir(parents=True,exist_ok=True)
    mods=[emit_shard(a.output,j//a.shard_size,cases[j:j+a.shard_size])
          for j in range(0,len(cases),a.shard_size)]
    body=[*[f'import {mod}' for mod,_ in mods],
          'set_option maxRecDepth 100000','set_option maxHeartbeats 0',
          f'namespace {NS}', 'open BB6Coverage',
          'def shards : List (List (List Nat)) := [',
          ',\n'.join('  '+ns+'.rows' for _,ns in mods),']',
          'def allRows : List (List Nat) := shards.flatten',
          'theorem never_mem (row : List Nat) (h : row ∈ allRows) (m : Machine)',
          '    (hm : compatible (table row) m) : NeverHalts m := by',
          '  obtain ⟨s,hs,hr⟩ := List.mem_flatten.mp h',
          '  simp only [shards,List.mem_cons,List.not_mem_nil,or_false] at hs',
          '  rcases hs with '+' | '.join('rfl' for _ in mods)]
    body += [f'  · exact {ns}.never_mem row hr m hm' for _,ns in mods]
    body += ['theorem cover_mem (row : List Nat) (h : row ∈ allRows) : Cover (DecidedBelow 128) (table row) :=',
             '  .leaf _ (fun m hm => Or.inl (never_mem row h m hm))',
             '#print axioms never_mem','#print axioms cover_mem',f'end {NS}','']
    (a.output/'Raw34CylinderBank.lean').write_text('\n'.join(body))
    digest=hashlib.sha256((json.dumps(sparse,separators=(',',':'))+'\n').encode()).hexdigest()
    manifest={'rows':len(sparse),'cylinderCompletions':sum(25**r.count(0) for r in sparse),
              'orderedSha256':digest,'certificateDimensions':dict(collections.Counter(str(x['d']) if x else 'pump' for _,_,x in cases)),
              'modules':[mod for mod,_ in mods]}
    (a.output/'sparseRows.json').write_text(json.dumps(sparse,separators=(',',':'))+'\n')
    (a.output/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(manifest,indent=2))

if __name__=='__main__':
    main()
