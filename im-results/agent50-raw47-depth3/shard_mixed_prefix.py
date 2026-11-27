"""Recursively certify oversized mixed audit trees in bounded source shards."""
def write_sharded(out,i,tree,source,kind,emit,emit_partial,limit=35000):
    root=f'Raw47D3{kind}{i}'
    ns='BB6.Agent50.'+root
    partial=kind=='U'
    typ='PartialAudit' if partial else 'Audit'
    checker='partialPrefixCheck' if partial else 'prefixCheck'
    quick='quickPartialCheck_eq' if partial else 'quickCheck_eq'
    split='BB6.Agent50SplitMixedPrefix.partialSplit_checked' if partial else 'split_checked'
    selector='byPartialMove' if partial else 'byMove'
    emitter=emit_partial if partial else emit
    base=root+'Base'
    end=f'end {ns}\n'
    (out/(base+'.lean')).write_text(source.split(f'def tree : {typ} := ',1)[0]+end)
    head=f'''import {base}
import SplitPrefix
import SplitMixedPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent50TNFPilot BB6.Agent47CanonicalFrontier
open BB6.Agent47PartialAudit BB6.Agent50PartialPrefix BB6.Agent50SplitPrefix
'''
    def b(x):return str(bool(x)).lower()
    def slot(s):return f'({s//2},{b(s%2)})'
    def mv(j):return f'⟨{b(j//12)},{b(j%12>=6)},{j%6}⟩'
    modules=0
    def build(t,address,pexpr):
        nonlocal modules
        name=root+'K'+address
        term='node'+address
        check='chk'+address
        txt=emitter(t,i)
        if t[0]!='split' or len(txt)<=limit:
            body=head+f'def {term} : {typ} := {txt}\n'
            body+=f'theorem {check} : {checker} 10006 ({pexpr}) {term} = true := (BB6.Agent50QuickPrefix.{quick} 10006 ({pexpr}) {term}).symm.trans (by decide +kernel)\n'
        else:
            _,n,s,kids=t
            assert len(kids)==24
            subs=[build(k,address+'_'+str(j),f'refine ({pexpr}) {slot(s)} (some {mv(j)})') for j,k in enumerate(kids)]
            body=''.join(f'import {mod}\n' for mod,_,_ in subs)+head
            body+=f'def {term} : {typ} := .split {n} {slot(s)} ({selector} ['+','.join(v for _,v,_ in subs)+'])\n'
            body+=f'''theorem {check} : {checker} 10006 ({pexpr}) {term} = true := by
  unfold {term}
  apply {split}
  · decide +kernel
  · intro mv
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
'''
            for q in range(6):
                for j in (q,6+q,12+q,18+q):body+=f'    · exact {subs[j][2]}\n'
        (out/(name+'.lean')).write_text(body+end)
        modules+=1
        return name,term,check
    name,term,check=build(tree,'R','p')
    text=f'import {name}\n'+head
    text+=f'def tree : {typ} := {term}\ntheorem checked : {checker} 10006 p tree = true := {check}\n'
    tail='def remaining := ' if partial else 'theorem bound (m : Machine)'
    text+=source[source.index(tail):]
    (out/(root+'.lean')).write_text(text)
    print(f'Sharded {root}: {modules} checked subtrees, source limit {limit}',flush=True)
