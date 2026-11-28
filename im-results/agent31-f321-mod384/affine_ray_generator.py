#!/usr/bin/env python3
"""Proof-producing exact symbolic inverse search for F321 terminal rays.

Usage: python3 affine_ray_generator.py 6144 3787 > /tmp/Auto3787.lean
       python3 affine_ray_generator.py 12288 7933 > /tmp/Auto7933.lean

The script is a SEARCH/TRANSLATION aid, not a proof oracle: the emitted
Lean file explicitly proves the predecessor closure for every n and k
using the source CounterMove inductive relation. Unknown symbolic
branches fail closed rather than being silently discarded.
"""
from __future__ import annotations
import argparse
import dataclasses
import json
import sys

@dataclasses.dataclass(frozen=True)
class Ray:
    p: int
    a: int
    q: int
    b: int

    def low(self):
        return (self.a, self.b)

def maybe_seed(ray: Ray) -> bool:
    if ray.a > 1 or ray.b > 1:
        return False
    if (ray.p == 0 and ray.a != 1) or (ray.q == 0 and ray.b != 1):
        return False
    candidates = []
    for p, base in ((ray.p, ray.a), (ray.q, ray.b)):
        if p:
            if (1-base) % p:
                return False
            candidates.append((1-base)//p)
    return (len(set(candidates)) <= 1 and (not candidates or candidates[0]>=0))

def build(modulus: int, residue: int):
    if modulus < 4 or modulus%4 or not (0 <= residue < modulus):
        raise ValueError("Need M divisible by 4 and 0 <= residue < M")
    stack=[Ray(modulus, residue+1, modulus, residue)]
    nodes=[]
    seen=set()
    children={}
    while stack:
        s=stack.pop()
        if s in seen:
            continue
        seen.add(s)
        p,a,q,b=s.p,s.a,s.q,s.b
        if min(p,a,q,b)<0 or p+q!=2*modulus or a+b>2*modulus:
            raise ValueError(f"Invalid affine inverse rank: {s}")
        if maybe_seed(s):
            raise ValueError(f"Root may lie in symbolic cone: {s}")
        if q%2 or (b%2 and b<3) or (q>0 and b<=1) or p%4:
            raise ValueError(f"Unknown high/far inverse parity/threshold: {s}")
        if q==0 and b<=2:
            raise ValueError(f"Possible equality/middle inverse: {s}")
        if q>0 and b<=2 and a%4==2:
            raise ValueError(f"Possible unbounded middle inverse: {s}")
        nexts={}
        if b%2:
            nexts["high"]=Ray(p+q//2,a+(b-3)//2+2,q//2,(b-3)//2)
        if a%4==2:
            if a<6 or b<1:
                raise ValueError(f"Unknown far inverse threshold: {s}")
            ap=(a-6)//4
            nexts["far"]=Ray(p//4,ap,q+3*(p//4),b+3*ap)
        nodes.append(s)
        children[s]=nexts
        for child in nexts.values():
            stack.append(child)
        if len(nodes)>20000:
            raise ValueError("Symbolic inverse search exceeded 20k ray nodes")
    return nodes,children

def form(node:Ray,k="k"):
    return f"({node.p}*{k}+{node.a}) ({node.q}*{k}+{node.b})"

def emit(modulus:int,residue:int,nodes,children):
    ix={ray:i for i,ray in enumerate(nodes)}
    out=[]
    add=out.append
    add("import F321BackwardBarrier")
    add("import Lean.Elab.Tactic.Omega")
    add("")
    add("/-! Automatically generated, kernel-checked F321 affine inverse cone.")
    add("    All successors and branch contradictions are re-proved in Lean.")
    add("    This file proves an unbounded theorem from CounterMove, not simulation. -/")
    add("set_option maxRecDepth 8192")
    add("set_option maxHeartbeats 0")
    add(f"namespace BB6.Agent31F321Ray{residue}")
    add("open BB6.Agent31F321Density")
    add("")
    clauses=[f"(∃ k : Nat, A = {s.p}*k+{s.a} ∧ D = {s.q}*k+{s.b})" for s in nodes]
    add("private def AffineDead (A D : Nat) : Prop :=")
    add("  " + " ∨ (\n      ".join(clauses)+")"*(len(nodes)-1))
    add("")
    for i,s in enumerate(nodes):
        constructor="Or.inr ("*i+("⟨k,rfl,rfl⟩" if i==len(nodes)-1 else "Or.inl ⟨k,rfl,rfl⟩")+")"*i
        add(f"private theorem intro_{i} (k:Nat) : AffineDead {form(s)} := by")
        add("  unfold AffineDead")
        add(f"  exact {constructor}")
        add("")
    for i,s in enumerate(nodes):
        add(f"private theorem pred_{i} (k a d:Nat)")
        add(f"  (hm:CounterMove a d {form(s)}) : AffineDead a d := by")
        add(f"  have hD : 3 ≤ {s.q}*k+{s.b} := by omega")
        add("  rcases large_second_only_high_far hm hD with ⟨ha,hd⟩ | ⟨ha,hd⟩")
        for name in ("high","far"):
            add("  ·")
            nxt=children[s].get(name)
            if nxt is None:
                add("      omega")
            else:
                assert nxt in ix
                add(f"      have hA : a = {nxt.p}*k+{nxt.a} := by omega")
                add(f"      have hD : d = {nxt.q}*k+{nxt.b} := by omega")
                add("      rw [hA,hD]")
                add(f"      exact intro_{ix[nxt]} k")
        add("")
    add("private theorem no_seed : ¬ AffineDead 1 1 := by")
    add("  intro h")
    add("  unfold AffineDead at h")
    add("  rcases h with "+" | ".join(f"⟨k{i},ha{i},hd{i}⟩" for i in range(len(nodes))))
    for _ in nodes:
        add("  · omega")
    add("")
    add("private theorem backward_closed {a d A D : Nat}")
    add("  (hm : CounterMove a d A D) (hbad : AffineDead A D) :")
    add("  AffineDead a d := by")
    add("  unfold AffineDead at hbad")
    add("  rcases hbad with "+" | ".join(f"⟨k{i},ha{i},hd{i}⟩" for i in range(len(nodes))))
    for i,_ in enumerate(nodes):
        add(f"  · exact pred_{i} k{i} a d (by simpa [ha{i},hd{i}] using hm)")
    add("")
    add("private theorem no_reach {n a d:Nat}")
    add("  (hr:CounterReach 1 1 n a d) : ¬AffineDead a d := by")
    add("  induction hr with")
    add("  | nil => exact no_seed")
    add("  | step hr hm ih =>")
    add("      intro hbad")
    add("      exact ih (backward_closed hm hbad)")
    add("")
    add(f"theorem gate{residue}_mod{modulus}_never (k n : Nat) :")
    add(f"  ¬ CounterReach 1 1 n ({modulus}*k+{residue+1}) ({modulus}*k+{residue}) := by")
    add("  intro hr")
    add("  exact no_reach hr (intro_0 k)")
    add("")
    add(f"#print axioms gate{residue}_mod{modulus}_never")
    add(f"end BB6.Agent31F321Ray{residue}")
    return "\n".join(out)+"\n"

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modulus",type=int)
    parser.add_argument("residue",type=int)
    parser.add_argument("--summary",action="store_true",help="print JSON stats rather than Lean proof")
    args=parser.parse_args()
    nodes,children=build(args.modulus,args.residue)
    if args.summary:
        print(json.dumps({"modulus":args.modulus,"residue":args.residue,
            "nodes":len(nodes),"inverse_edges":sum(map(len,children.values()))},
            sort_keys=True))
    else:
        sys.stdout.write(emit(args.modulus,args.residue,nodes,children))

if __name__=="__main__":
    main()
