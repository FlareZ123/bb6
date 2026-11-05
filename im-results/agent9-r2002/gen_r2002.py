"""Emit a fully parametric, kernel-checkable P1 GAncestor/Blocked proof for n=65536*q+2002."""
from pathlib import Path
import affine_r2002 as mod

Aff=mod.Aff
ROOT=(Aff(131072,127052),Aff(0,3))

def expression(x):
    if x.a == 0:
        return str(x.c)
    return f'({x.a}*t+{x.c})'

def pair_cases(pairs):
    return ' ∨\n      '.join(f'(k = {expression(k)} ∧ v = {expression(v)})' for k,v in pairs)

def rcases_cases(pairs):
    return ' | '.join('⟨hk,hv⟩' for _ in pairs)

def eq_cases(pairs):
    return ' | '.join('⟨rfl,rfl⟩' for _ in pairs)

nodes=[];seen=set();children={}
def visit(node):
    if node in seen:
        return
    seen.add(node)
    b,d=node
    pairs=mod.inv(b,d)
    assert pairs is not None, ('inverse',node)
    children[node]=pairs
    for k,v in pairs:
        assert v.a!=0 or v.c!=1, ('exceptional one',node)
        x,y=k*2-4,v+4
        if y.mod(2)==0:
            assert mod.gap(x+12)==15
        elif x.mod(4)==2:
            pass
        else:
            assert x.mod(4)==0 and x.ge(8) and y.ge(1)
            visit((x,y))
    nodes.append(node)
visit(ROOT)
ids={x:i for i,x in enumerate(nodes)}
print('interior nodes',len(nodes),'branches',sum(map(len,children.values())))

blocks=[]
for node in nodes:
    i=ids[node]; b,d=node; pairs=children[node]
    B=expression(b);D=expression(d)
    out=[f'private theorem inv_{i} (t k v : Nat) (ht : 223≤t)\n    (h : BB6.P1Reduction.GAncestor {B} {D} k v) :\n      {pair_cases(pairs)} := by',
    '  have aux : ∀ b d k v, BB6.P1Reduction.GAncestor b d k v →\n      b = '+B+' → d = '+D+' →\n      '+pair_cases(pairs)+' := by',
    '    intro b d k v h',
    '    induction h with',
    '    | upper k d =>',
    '        intro hb hd',
    '        omega',
    '    | nest b d k c h ih =>',
    '        intro hb hd',
    '        have hh := ih hb hd',
    f'        rcases hh with {rcases_cases(pairs)}',
    '        all_goals omega',
    f'  exact aux {B} {D} k v h rfl rfl',
    f'\nprivate theorem block_{i} (q t : Nat) (ht : 223≤t)\n    (htid : t = paramT q) : BB6.Agent4Cone.Blocked {B} {D} := by',
    f'  refine BB6.Agent4Cone.Blocked.feeder {B} {D} (by omega) (by omega) (by omega) ?_ ?_',
    '  · intro k h',
    f'    rcases inv_{i} t k 1 ht h with {rcases_cases(pairs)}',
    '    all_goals omega',
    '  · intro k v h hv',
    f'    rcases inv_{i} t k v ht h with {eq_cases(pairs)}',
    ]
    for k,v in pairs:
        x,y=k*2-4,v+4
        K,V,X,Y=map(expression,(k,v,x,y))
        if y.mod(2)==0:
            typ='power'
        elif x.mod(4)==2:
            typ='mod'
        else:
            typ='next'
        out.extend([
            f'    · have hx : 2*{K}-4={X} := by omega',
            f'      have hy : {V}+4={Y} := by omega',
            '      rw [hx,hy]',
        ])
        if typ=='mod':
            out.append(f'      exact BB6.Agent4Cone.Blocked.modLeaf {X} {Y} (by omega) (by omega) (by omega) (by omega)')
        elif typ=='power':
            s=x+12;A,C=s.a,s.c
            assert mod.gap(s)==15
            out.extend([
                f'      have hgap0 : ∀ j : Nat, {A}*t+{C} ≠ 14*2^j := by',
                f'        simpa only [htid] using (param_gap q {A} {C} (by decide) (by decide) (by decide) (by decide))',
                f'      have hgap : ∀ j : Nat, {X}+12 ≠ 14*2^j := by',
                '        intro j heq',
                f'        have he : {X}+12={A}*t+{C} := by omega',
                '        exact hgap0 j (he ▸ heq)',
                f'      exact BB6.Agent4Cone.Blocked.powerLeaf {X} {Y} (by omega) (by omega) (by omega) hgap',
            ])
        else:
            out.append(f'      exact block_{ids[(x,y)]} q t ht htid')
    blocks.append('\n'.join(out))

header='''import ConeKernel
import R2002Param
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent9R2002
'''
footer=f'''\n
theorem root_blocked (q:Nat) :
    BB6.Agent4Cone.Blocked {expression(ROOT[0]).replace('t','(paramT q)')} {expression(ROOT[1])} := by
  have ht : 223≤paramT q := by
    have hX : 64*(q+1) ≤ expX q := X_ge_64_succ q
    have he := param_eq q
    omega
  exact block_{ids[ROOT]} q (paramT q) ht rfl

#print axioms root_blocked
end BB6.Agent9R2002
'''
code=header+'\n\n'.join(blocks)+footer
Path(__file__).with_name('R2002Root.lean').write_text(code)
print('bytes',len(code),'leaf power',sum(y.mod(2)==0 for pairs in children.values() for k,y in pairs))
