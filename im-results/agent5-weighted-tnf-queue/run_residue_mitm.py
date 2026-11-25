#!/usr/bin/env python3
"""Untrusted capped run-residue BiDFA synthesis, with optional aligned blocks.
The original source's decide_nonhalt checks all generated candidates."""
from collections import defaultdict, deque
from functools import lru_cache
from pathlib import Path
import argparse
import json
import re
from block_phase_dfa import phase_dfa, discovered_closure, coq_list

BANK = [(c,m,r) for r in range(1,7) for c,m in
        [(1,1),(2,1),(3,1),(4,1),(5,1),(1,2),(2,2),(1,3),
         (2,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,12),(1,16)]]
TABLE_RE = re.compile(r"^(?:(?:[01][LR][A-F]|---){2}_){5}(?:[01][LR][A-F]|---){2}$")

def block_search(table,width,specl,specr,limit=10000):
    code=table.replace("_","")
    assert TABLE_RE.fullmatch(table)
    moves=[None if x=="---" else (int(x[0]),x[1]=="R",ord(x[2])-65)
           for x in (code[i:i+3] for i in range(0,36,3))]
    @lru_cache(None)
    def macro(q,d,a):
        h=0 if d else width-1
        visited=set()
        while 0<=h<width:
            st=q,h,a
            if st in visited:
                return "loop"
            visited.add(st)
            mv=moves[2*q+(a>>h&1)]
            if mv is None:
                return None
            w,d,q=mv
            a=(a&~(1<<h))|(w<<h)
            h+=1 if d else -1
        return q,d,a

    states=[[()],[()]]
    ids=[{():0},{():0}]
    delta=[{},{}]
    edges=[defaultdict(set),defaultdict(set)]
    waiting=[defaultdict(list),defaultdict(list)]
    seen={(0,True,0,0,0)}
    pending=deque(seen)

    def push(side,x,b):
        key=x,b
        if key in delta[side]:
            return delta[side][key]
        cap,mod,runs=(specl,specr)[side]
        st=states[side][x]
        if not st and b==0:
            ns=()
        elif st and st[0][0]==b:
            sym,n,m=st[0]
            ns=((b,min(n+1,cap),(m+1)%mod),)+st[1:]
        else:
            ns=((b,1,1%mod),)+st[:runs-1]
        j=ids[side].get(ns)
        if j is None:
            j=len(states[side])
            states[side].append(ns)
            ids[side][ns]=j
        delta[side][key]=j
        return j

    for side in range(2):
        assert push(side,0,0)==0
        edges[side][0].add((0,0))

    def add(q,d,a,l,r):
        st=q,d,a,l,r
        if st not in seen:
            if len(seen)>=limit:
                raise RuntimeError("block closure limit")
            seen.add(st)
            pending.append(st)

    def pop(st,b,src):
        q,d,a,l,r=st
        n,d,w=macro(q,d,a)
        if d:
            add(n,d,b,push(0,l,w),src)
        else:
            add(n,d,b,src,push(1,r,w))

    try:
        while pending:
            st=pending.popleft()
            q,d,a,l,r=st
            mv=macro(q,d,a)
            if mv is None:
                return None
            if mv=="loop":
                continue
            n,d,w=mv
            side=int(d)
            old=l if d else r
            dst=push(1-side,old,w)
            edge=w,old
            if edge not in edges[1-side][dst]:
                edges[1-side][dst].add(edge)
                for x in waiting[1-side][dst]:
                    pop(x,*edge)
            target=r if d else l
            waiting[side][target].append(st)
            for b,x in edges[side][target]:
                pop(st,b,x)
    except RuntimeError:
        return None
    ds=[[[d.get((i,b),0) for b in range(1<<width)]
         for i in range(len(s))] for d,s in zip(delta,states)]
    return ds,len(seen)

def search(table,limit=10000):
    for width in (1,2,3,4):
        for spec in BANK:
            hit=block_search(table,width,spec,spec,limit)
            if hit is None:
                continue
            ds,block_count=hit
            try:
                l=phase_dfa(width,0,lambda q,a:ds[0][q][a])
                r=phase_dfa(width,0,lambda q,a:ds[1][q][a],reverse=True)
                count,_=discovered_closure(table,
                    lambda side,q,b:(l,r)[side][q][b],limit=300000)
            except RuntimeError:
                continue
            return dict(table=table,L=l,R=r,reachable=count,
                        width=width,spec=spec,block_reachable=block_count)
    return None

def packed_nodes(log,marker="fast_packed"):
    txt=Path(log).read_text()
    parts=re.split(r"\]\s*,\s*\[",txt.rsplit(marker+" =",1)[1].split("\n     :",1)[0])
    if len(parts)!=2:
        raise ValueError("packed queue format")
    nodes=[[(s,int(h),int(f)) for s,h,f in
            re.findall(r'\("([01LRABCDEF_-]+)",\s*(\d+),\s*(\d+)\)',p)]
           for p in parts]
    for s,h,f in nodes[0]+nodes[1]:
        if not TABLE_RE.fullmatch(s) or s.count("---")!=h:
            raise ValueError("invalid packed table")
    return nodes

def emit(rows,out):
    # Filter by the original verifier, then prove the entire accepted roster safe.
    lines=["From BusyCoq Require Import CTL62 Individual62 Enumerate62",
           "  Agent5Enumerate62DeciderSound SourceResidualRoster.",
           "From Coq Require Import List Bool NArith.",
           "Import ListNotations.",
           "Open Scope N_scope.",
           "Open Scope string_scope.",
           "Definition run_symbol_id (s : Sym) := match s with S0 => int0 | S1 => int1 end."]
    entries=[]
    for i,row in enumerate(rows):
        n=row["reachable"]
        lines += [f"Definition run_left_{i} : list N := {coq_list(row['L'])}.",
                  f"Definition run_right_{i} : list N := {coq_list(row['R'])}.",
                  f"Definition run_arg_{i} := MITMDFA {max(100,2*n)} {max(1000,4*n)} run_left_{i} run_right_{i} run_symbol_id (N_to_int 2)."]
        entries.append(f'(TM_from_str "{row["table"]}", run_arg_{i})')
    lines += ["Definition run_candidates : list (TM * DeciderParameter) := [\n  "+";\n  ".join(entries)+"\n].",
              "Definition run_certified := map fst (filter (fun x => decide_nonhalt (fst x) (snd x)) run_candidates).",
              "Theorem run_certified_safe bound : Forall (source_table_safe bound) run_certified.",
              "Proof.",
              "  apply Forall_forall. intros t Ht. unfold run_certified in Ht.",
              "  apply in_map_iff in Ht. destruct Ht as [[p arg] [E H]]. simpl in E. subst t.",
              "  apply filter_In in H. destruct H as [_ H].",
              "  apply source_nonhalt_cylinder. eapply agent5_decide_nonhalt_sound. exact H.",
              "Qed.",
              "Print Assumptions run_certified_safe.",
              "Eval vm_compute in (List.length run_candidates, List.length run_certified)."]
    Path(out).write_text("\n\n".join(lines)+"\n")

def main():
    p=argparse.ArgumentParser()
    p.add_argument("checkpoint_log",type=Path)
    p.add_argument("output",type=Path)
    p.add_argument("--marker",default="fast_packed")
    p.add_argument("--all-nodes",action="store_true")
    p.add_argument("--exclude",action="append",default=[])
    a=p.parse_args()
    active,held=packed_nodes(a.checkpoint_log,a.marker)
    selected=active+held if a.all_nodes else held
    rows=[];failed=[];done=set(a.exclude)
    for table,h,f in selected:
        if table in done:
            continue
        done.add(table)
        hit=search(table)
        if hit is None:
            failed.append(table)
        else:
            rows.append(hit)
    a.output.mkdir(parents=True,exist_ok=True)
    (a.output/"run-candidates.json").write_text(json.dumps(rows,separators=(",",":"))+"\n")
    (a.output/"run-failed.txt").write_text("\n".join(failed)+"\n")
    emit(rows,a.output/"Agent5RunMITM.v")
    print(f"candidates {len(rows)}, unresolved {len(failed)}, active {len(active)}, held {len(held)}")

if __name__=="__main__":
    main()
