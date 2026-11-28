#!/usr/bin/env python3
"""Close the Raw34 FAR168 residual with d=5/6 FAR and one growth proof.

The original source checker, not the external FAR search, proves every hit.
All 168 rows are bound in order to Raw34FAR168.Data.missRows in Lean.
"""
import argparse
import hashlib
import json
from pathlib import Path

PUMP = 2071
PUMP_ROW = [21,19,22,12,11,1,16,7,18,20,5,14]
PARENT = 'BB6.Agent40Raw34PairD1LF_F0LDDepth6Data.parent'
NS = 'BB6.Agent50Raw34FAR168Closed'

def read_jsonl(path):
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]

def read_stage(path, expected_ids, d):
    records = read_jsonl(path)
    if [x['id'] for x in records] != expected_ids:
        raise ValueError(f'{path}: unexpected ordered IDs')
    hits, misses = {}, []
    for x in records:
        ident = x['id']
        if 'd' not in x:
            misses.append(ident)
            continue
        if x['d'] != d or len(x['dfa']) != 2*d:
            raise ValueError(f'{path}: malformed size-{d} hit {ident}')
        n = 6*d + 1
        if any(len(x[k]) != n for k in ('m0','m1')):
            raise ValueError(f'{path}: malformed mask vectors {ident}')
        hits[ident] = x
    return hits, misses

def lean(xs):
    return '[' + ','.join(map(str,xs)) + ']'

def emit_shard(out, index, ids, rows, hits):
    module = f'Raw34FAR168ClosedShard{index:03d}'
    ns = f'{NS}.{module}'
    body = ['import Raw34Plan','import FastFAR','import Raw34M2071Growth',
            'set_option maxRecDepth 100000','set_option maxHeartbeats 0',
            f'namespace {ns}', 'open BB6Coverage BB6Coverage.FAR BB6.Agent50Raw34Plan',
            'def rows : List (List Nat) := [', ',\n'.join('  '+lean(rows[i]) for i in ids), ']', '']
    for ident in ids:
        p, c, ok, never = (f'{name}{ident}' for name in ('p','c','ok','never'))
        body.append(f'def {p} : PartialMachine := table {lean(rows[ident])}')
        if ident == PUMP:
            body += [f'theorem eq{ident} : {p} = BB6.Agent50Raw34M2071.p :=',
                     '  sameTable_sound _ _ (by decide)',
                     f'theorem {never} (m : Machine) (hm : compatible {p} m) : NeverHalts m := by',
                     f'  rw [eq{ident}] at hm', '  exact BB6.Agent50Raw34M2071.never m hm','']
            continue
        x = hits[ident]
        d = x['d']
        pp = f'(reflectPartial {p})' if x['reflect'] else p
        sound = f'({c}).sound {pp} (({c}).fastValid_sound {pp} {ok})'
        proof = f'reflectNever m ({sound} (reflectTable m) (reflectCompatible {p} m hm))' if x['reflect'] else f'{sound} m hm'
        body += [f'def {c} : Data {d} := ⟨0,{lean(x["dfa"])},{lean(x["m0"])},{lean(x["m1"])},{x["z"]}⟩',
                 f'theorem {ok} : ({c}).fastValid {pp} = true := by decide +kernel',
                 f'theorem {never} (m : Machine) (hm : compatible {p} m) : NeverHalts m := {proof}', '']
    body += ['theorem never_mem (row : List Nat) (h : row ∈ rows) (m : Machine)',
             '    (hm : compatible (table row) m) : NeverHalts m := by',
             '  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h',
             '  rcases h with ' + ' | '.join('rfl' for _ in ids)]
    body += [f'  · exact never{i} m hm' for i in ids]
    body += ['#print axioms never_mem',f'end {ns}','']
    (out/f'{module}.lean').write_text('\n'.join(body))
    return module, ns

def main():
    ap = argparse.ArgumentParser()
    for name in ('hard','far4','far5','far6','output'):
        ap.add_argument('--'+name, type=Path, required=True)
    ap.add_argument('--shard-size', type=int, default=12)
    args = ap.parse_args()
    if args.shard_size < 1:
        raise ValueError('shard size must be positive')
    rows = {}
    for line in args.hard.read_text().splitlines():
        ident,*row = map(int,line.split())
        if ident != len(rows) or len(row) != 12 or not all(1 <= x <= 25 for x in row):
            raise ValueError('malformed hard census')
        rows[ident] = row
    if len(rows) != 3233 or len({tuple(r) for r in rows.values()}) != 3233:
        raise ValueError('wrong hard census')
    old = read_jsonl(args.far4)
    if [x['id'] for x in old] != list(rows):
        raise ValueError('wrong four-state census order')
    ids = [x['id'] for x in old if 'd' not in x]
    hits5, misses5 = read_stage(args.far5, ids, 5)
    hits6, misses6 = read_stage(args.far6, misses5, 6)
    if (len(ids),len(hits5),len(hits6),misses6) != (168,159,8,[PUMP]) or rows[PUMP] != PUMP_ROW:
        raise ValueError('unexpected endgame roster')
    hits = hits5 | hits6
    out = args.output
    out.mkdir(parents=True, exist_ok=True)
    shards = [emit_shard(out,k//args.shard_size,ids[k:k+args.shard_size],rows,hits)
              for k in range(0,len(ids),args.shard_size)]
    body = ['import Raw34FAR168Cover', *[f'import {mod}' for mod,_ in shards],
            'set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {NS}',
            'open BB6Coverage BB6.Agent50Raw34Plan',
            'def allRows : List (List Nat) := ' + ' ++\n  '.join(f'{ns}.rows' for _,ns in shards),
            'theorem rows_eq : allRows = BB6.Agent50Raw34FAR168.Data.missRows := by decide +kernel',
            'theorem never_mem (row : List Nat) (h : row ∈ allRows) (m : Machine)',
            '    (hm : compatible (table row) m) : NeverHalts m := by',
            '  simp only [allRows, List.mem_append] at h']
    depth = 0
    for _,ns in shards[:-1]:
        pad = '  '*(depth+1)
        body += [pad+'rcases h with h | h',pad+f'· exact {ns}.never_mem row h m hm',pad+'·']
        depth += 1
    body += ['  '*(depth+1)+f'exact {shards[-1][1]}.never_mem row h m hm',
             f'theorem cover : Cover (DecidedBelow 128) {PARENT} := by',
             '  apply Cover.leaf', '  intro m hm',
             '  rcases BB6.Agent50Raw34FAR168.cover.sound m hm with hd | hr',
             '  · exact hd', '  · rcases hr with ⟨j, row, hj, hrow⟩',
             '    have hmem : row ∈ BB6.Agent50Raw34FAR168.Data.missRows := by',
             '      rcases List.getElem?_eq_some_iff.mp hj with ⟨hidx, hget⟩',
             '      exact List.mem_of_getElem hget',
             '    rw [← rows_eq] at hmem', '    exact Or.inl (never_mem row hmem m hrow)',
             '#print axioms rows_eq','#print axioms cover',f'end {NS}','']
    (out/'Raw34FAR168Closed.lean').write_text('\n'.join(body))
    digest = hashlib.sha256((json.dumps([rows[i] for i in ids],separators=(',',':'))+'\n').encode()).hexdigest()
    manifest = {'residualRows':168,'far5Hits':159,'far6Hits':8,'growthId':PUMP,
                'orderedMissSha256':digest,'modules':[m for m,_ in shards],
                'theorem':NS+'.cover','status':'generated; original-source Lean acceptance required'}
    (out/'far168-closed-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(manifest,indent=2))

if __name__ == '__main__':
    main()
