"""Generate a kernel-verifiable, all-time P1 n=18 critical-index inverse-cone proof.
Every generated inference is checked against the unmodified original source by Lean CI.
"""
from pathlib import Path

INDEX = 18
ROOT = (14*(1 << INDEX)-2*INDEX-16, 3)

def g_inputs(b,d):
    assert b>=8 and b%4==0 and d>=1
    k=b//4-1; v=d+b//2
    pairs=[]
    while True:
        pairs.append((k,v))
        if v<3 or v%2==0: break
        nxt=(v-3)//2
        k=k+nxt//2+1
        v=nxt
    return pairs

def is_power_leaf(x,y):
    s=x+12
    return x%2==0 and y>0 and y%2==0 and not (s%14==0 and (s//14)>0 and ((s//14)&((s//14)-1))==0)

def is_mod_leaf(x,y):
    return x%2==0 and y>0 and x>2 and x%4==2

nodes=[]; visited=set()
def visit(node):
    if node in visited: return
    visited.add(node)
    b,d=node
    for k,v in g_inputs(b,d):
        assert v!=1, ('exceptional input',node,k,v)
        if v<2: continue
        x,y=2*k-4,v+4
        if not is_mod_leaf(x,y) and not is_power_leaf(x,y):
            assert x>=8 and x%4==0 and y>0,('unclassified',node,x,y)
            visit((x,y))
    nodes.append(node)
visit(ROOT)
ids={x:i for i,x in enumerate(nodes)}

def pair_cases(pairs):
    return ' ∨\n      '.join(f'(k = {k} ∧ v = {v})' for k,v in pairs)

def rcases_cases(pairs):
    return ' | '.join('⟨hk,hv⟩' for _ in pairs)

def eq_cases(pairs):
    return ' | '.join('⟨rfl,rfl⟩' for _ in pairs)

blocks=[]
for node in nodes:
    i=ids[node]; b,d=node; pairs=g_inputs(b,d)
    out=[f'private theorem inv_{i} (k v : Nat)\n    (h : BB6.P1Reduction.GAncestor {b} {d} k v) :\n      {pair_cases(pairs)} := by',
    '  have aux : ∀ b d k v, BB6.P1Reduction.GAncestor b d k v →\n      b = '+str(b)+' → d = '+str(d)+' →\n      '+pair_cases(pairs)+' := by',
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
    f'  exact aux {b} {d} k v h rfl rfl',
    f'\nprivate theorem block_{i} : BB6.Agent4Cone.Blocked {b} {d} := by',
    f'  refine BB6.Agent4Cone.Blocked.feeder {b} {d} (by decide) (by decide) (by decide) ?_ ?_',
    '  · intro k h',
    f'    rcases inv_{i} k 1 h with {rcases_cases(pairs)}',
    '    all_goals omega',
    '  · intro k v h hv',
    f'    rcases inv_{i} k v h with {eq_cases(pairs)}',
    ]
    for k,v in pairs:
        if v<2:
            out.append('    · omega')
            continue
        x,y=2*k-4,v+4
        if is_mod_leaf(x,y):
            out.append(f'    · exact BB6.Agent4Cone.Blocked.modLeaf {x} {y} (by decide) (by decide) (by decide) (by decide)')
        elif is_power_leaf(x,y):
            s=x+12
            e=(s//14).bit_length()-1
            assert 14*(1<<e)<s<14*(1<<(e+1)),(node,x,y,s,e)
            out.extend([
               '    · have hgap : ∀ j : Nat, '+str(s)+' ≠ 14*2^j := by',
               '        intro j heq',
               f'        have hlo : 14*2^{e} < {s} := by decide',
               f'        have hhi : {s} < 14*2^({e}+1) := by decide',
               f'        by_cases hj : j ≤ {e}',
               '        · have hp := Nat.pow_le_pow_right (show 0 < 2 by decide) hj',
               f'          have hmul : 14*2^j ≤ 14*2^{e} := Nat.mul_le_mul_left 14 hp',
               '          omega',
               '        · have hp := Nat.pow_le_pow_right (show 0 < 2 by decide) (show '+str(e)+'+1 ≤ j by omega)',
               f'          have hmul : 14*2^({e}+1) ≤ 14*2^j := Nat.mul_le_mul_left 14 hp',
               '          omega',
               f'      exact BB6.Agent4Cone.Blocked.powerLeaf {x} {y} (by decide) (by decide) (by decide) hgap'])
        else:
            out.append(f'    · exact block_{ids[(x,y)]}')
    blocks.append('\n'.join(out))
header='''import ConeKernel
import P1Gate
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace BB6.Agent7N18
'''
footer=f'''\ntheorem root_blocked : BB6.Agent4Cone.Blocked {ROOT[0]} 3 := block_{ids[ROOT]}

theorem no_blank_critical_18 :
    ¬BB6.Agent1.Reach 2 (14*2^18 - 2*18 - 10) := by
  intro hr
  have h3 := BB6.Agent50P1.critical_target_implies_three
    (14*2^18 - 2*18 - 10) (by decide) (by decide) hr
  have hroot : ¬ BB6.Agent1.Reach {ROOT[0]} 3 :=
    BB6.Agent4Cone.blocked_no_reach {ROOT[0]} 3 root_blocked
  exact hroot (by simpa using h3)

#print axioms root_blocked
#print axioms no_blank_critical_18
end BB6.Agent7N18
'''
code=header+'\n\n'.join(blocks)+footer
Path(__file__).with_name('N18.lean').write_text(code)
print('nodes',len(nodes),'bytes',len(code),'inverse branches',sum(len(g_inputs(*u)) for u in nodes),'leaf modulo',sum(is_mod_leaf(2*k-4,v+4) for u in nodes for k,v in g_inputs(*u) if v>=2),'leaf powers',sum(is_power_leaf(2*k-4,v+4) and not is_mod_leaf(2*k-4,v+4) for u in nodes for k,v in g_inputs(*u) if v>=2))
