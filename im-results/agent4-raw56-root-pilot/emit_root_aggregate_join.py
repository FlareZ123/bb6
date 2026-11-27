#!/usr/bin/env python3
"""Emit the checked first-query cut and exact all-E0 consumer for a pilot E1 child."""
import argparse,json
from pathlib import Path
BOUND=12000
HEAD='''set_option maxRecDepth 100000
set_option maxHeartbeats 0
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier
open BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster
'''
def mv(i):return f'⟨{str(bool(i//12)).lower()},{str(i%12>=6).lower()},{i%6}⟩'
def emit(tag,root,out):
    t=json.loads((root/'rootbranches'/f'{tag}.json').read_text());assert t[:3]==['split',8 if tag=='E10RD' else 9,8]
    rootmv=9 if tag=='E10RD' else 14
    children=[i for i,k in enumerate(t[3]) if k[0]=='split'];assert all(k[0] in ('cycle','split') for k in t[3]);assert len(children)==(14 if tag=='E10RD' else 15)
    ns=f'BB6.Agent4Raw56Pilot{tag}';mod=f'Raw56Pilot{tag}'
    a=['import Raw56RootConsumer',HEAD,f'namespace {ns}',f'abbrev p : PartialMachine := refine BB6.Agent1Raw56Root.parent (4,true) (some {mv(rootmv)})',
       'theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide',
       '''theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide''',
       'theorem supported : TNFSupport p 5 := supportOK_sound _ _ (by decide)']
    entries=[f'.closed (.cycle {k[1]} {k[2]} {str(bool(k[3])).lower()} ({k[4]}))' if k[0]=='cycle' else '.unresolved' for k in t[3]]
    a += [f'def tree : PartialAudit := .split {t[1]} (4,false) (byPartialMove [\n  '+',\n  '.join(entries)+'])',
          f'theorem checked : canonicalCheck {BOUND} p 5 tree = true := by decide',
          'def remaining := canonicalResiduals p 5 tree',f'theorem count : remaining.length = {len(children)} := by decide',
          f'''theorem sound : ∀ m, TNFQuotientCompatible p m → WeightedBound {BOUND} m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m :=
  canonicalSound {BOUND} p 5 tree (by decide) supported root nohalt checked''']
    a += [f'abbrev child{i:02} := refine p (4,false) (some {mv(i)})' for i in children]
    a += ['def childTables : List PartialMachine := ['+','.join(f'child{i:02}' for i in children)+']',
          'theorem exactRoster : remaining.all (fun e => childTables.any (fun q => sameTable e.2 q)) = true := by decide',
          f'''theorem cover (h : ∀ q ∈ childTables, ∀ m, TNFQuotientCompatible q m → WeightedBound {BOUND} m) :
    ∀ m, TNFQuotientCompatible p m → WeightedBound {BOUND} m := by
  intro m hm
  rcases sound m hm with hb | ⟨e,he,hq⟩
  · exact hb
  · have ha := List.all_eq_true.mp exactRoster e he
    obtain ⟨q,hmem,hmatch⟩ := List.any_eq_true.mp ha
    have hEq : e.2 = q := sameTable_sound hmatch
    exact h q hmem m (hEq ▸ hq)''',
          '#print axioms checked','#print axioms count','#print axioms cover',f'end {ns}']
    (out/(mod+'Cut.lean')).write_text('\n'.join(a)+'\n')
    b=[f'import {mod}Cut',*(f'import Raw56{tag}C{i:02}All' for i in children),HEAD,f'namespace {ns}']
    b += [f'theorem eq{i:02} : BB6.Agent4Raw56.{tag}C{i:02}.p = child{i:02} := sameTable_sound (by decide)' for i in children]
    b += [f'''theorem all_quotient : ∀ m, TNFQuotientCompatible p m → WeightedBound {BOUND} m := by
  apply cover
  intro q hq m hm
  simp only [childTables,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with {'|'.join(['rfl']*len(children))}''',*(f'  · exact BB6.Agent4Raw56.{tag}C{i:02}.all_quotient m (eq{i:02}.symm ▸ hm)' for i in children),f'''theorem all : ∀ m, compatible p m → WeightedBound {BOUND} m := by
  intro m hm; exact all_quotient m (compatible_quotient hm)''','#print axioms all_quotient','#print axioms all',f'end {ns}']
    (out/(mod+'All.lean')).write_text('\n'.join(b)+'\n')
    print(tag,'children',children)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('tag',choices=['E10RD','E11LC']);p.add_argument('--root',type=Path,default=Path.cwd());p.add_argument('--out',type=Path,required=True);a=p.parse_args();a.out.mkdir(parents=True,exist_ok=True);emit(a.tag,a.root,a.out)
