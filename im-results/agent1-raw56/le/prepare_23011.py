#!/usr/bin/env python3
"""Reproduce locally Lean-checked Raw56 E1=0LE leaf 23011 certificates.

The original FastBiDFA and canonicalCheck kernels validate the finite graph
and whole two-hole parent split. Discovery/replay is not trusted.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
STACK = ROOT / 'im-results/agent32-raw59'
RAW56 = ROOT / 'im-results/agent1-raw56'
LE = RAW56 / 'le'
PARENT = '1RB---_1RC1RF_0RD1RB_1LD1LE_1RC0LE_---0RC'
CHILD = '1RB---_1RC1RF_0RD1RB_1LD1LE_1RC0LE_1RA0RC'
PARAM = {'k':20,'groups':[['01',1,1]]}
SPEC = [{'id':23011,'table':CHILD,'params':[PARAM,PARAM],
         'states':5909,'edges':897}]

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def parse(s):
    s = s.replace('_','')
    assert len(s) == 36
    return [s[i:i+3] for i in range(0,36,3)]

def move(i):
    return f'{i//12}{"R" if i%12>=6 else "L"}{chr(65+i%6)}'

def branch(i):
    p = parse(PARENT)
    assert p[10] == '---'
    p[10] = move(i)
    return p

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('output',type=Path)
    args=ap.parse_args()
    out=args.output.resolve()
    out.mkdir(parents=True,exist_ok=True)
    sys.path.insert(0,str(STACK))
    from emit_rungram import emit
    sys.path.insert(0,str(LE))
    sys.path.insert(0,str(RAW56))
    from motif_quotient import minimize
    from emit_rc_rd import far
    z=json.loads(subprocess.check_output(
        ['node',str(LE/'motif_replay.cjs')],
        input=json.dumps(SPEC).encode()))
    assert len(z)==1 and z[0]['table']==CHILD
    d,graphs,states=minimize(CHILD,z[0]['dfa'])
    assert len(d[0])//2==186 and len(d[1])//2==285
    assert (len(states),sum(map(len,graphs))+2)==(3159,528)
    content='\n'.join([
        'import FastBiDFA',
        'set_option maxRecDepth 100000',
        'set_option maxHeartbeats 0',
        'namespace BB6.Agent1Raw56.LE23011',
        'open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA',
        emit(23011,CHILD,*d,[3159,528]),
        'end BB6.Agent1Raw56.LE23011',''])
    leaf=out/'Raw56LE23011F0RA.lean'
    leaf.write_text(content)

    root=[]
    for i,v in enumerate(parse(PARENT)):
        if v!='---':
            root.append(
                f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(v[0]=="1").lower()},{str(v[1]=="R").lower()},{ord(v[2])-65}⟩)')
    parts=[]
    for i in range(24):
        if i in [0,12]:
            parts.append('    .last 1203 (0,true)')
        elif i==6:
            parts.append('    .last 2698 (0,true)')
        elif i==1:
            parts.append('    .cycle 1201 2 true (7)')
        elif i==18:
            parts.append('    .proven BB6.Agent1Raw56.LE23011.M23011.table BB6.Agent1Raw56.LE23011.M23011.never')
        else:
            parts.append('    '+far('000',branch(i)))
    text='''import Raw40Nores
import Raw56LE23011F0RA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw56.LE23011Cover
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier

def p : PartialMachine := fun s => match s.1.val,s.2 with
'''+ '\n'.join(root)+'''
  | _,_ => none

theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
theorem support : TNFSupport p 6 := supportOK_sound _ _ (by decide)

def tree : PartialAudit := .closed (.split 1202 (5,false) (byMove [
'''+',\n'.join(parts)+'''
  ]))
theorem checked : canonicalCheck 7014 p 6 tree = true := by decide +kernel
theorem empty : canonicalResiduals p 6 tree = [] := by decide +kernel

theorem all_quotient : ∀ m, TNFQuotientCompatible p m → WeightedBound 7014 m := by
  intro m hm
  rcases canonicalSound 7014 p 6 tree (by decide) support root nohalt checked m hm with hb | ⟨e,he,_⟩
  · exact hb
  · rw [empty] at he; contradiction

theorem all : ∀ m, compatible p m → WeightedBound 7014 m := by
  intro m hm
  exact all_quotient m (compatible_quotient hm)
#print axioms all_quotient
#print axioms all
end BB6.Agent1Raw56.LE23011Cover
'''
    cover=out/'Raw56LE23011Cover.lean'
    cover.write_text(text)
    assert sha(leaf)=='5fc73be96ce85d426a9762e4aa5ba236f1272b6c0f879be79b835076dcd2dbdf',sha(leaf)
    assert sha(cover)=='64eb5f3486f18c21ca45bae4530d46d01e827b629c7060f1d716ea9e836829eb',sha(cover)
    print('Raw56 LE23011 SHA256',sha(leaf),sha(cover))
    print('Lean 4.36.0-rc2: compile FastBiDFA, Raw56LE23011F0RA, Raw56LE23011Cover')

if __name__=='__main__':
    main()
