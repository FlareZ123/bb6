"""Bounded-memory first-level prefixCheck composition (checked on Raw47 D3 parent 21)."""
def node_count(t):
    return 1+sum(map(node_count,t[3])) if t[0]=='split' else 1

def write_sharded(out,i,tree,source,emit):
    root='Raw47D3FAR'+str(i)
    ns='BB6.Agent50.'+root
    base=root+'Base'
    end=f'end {ns}\n'
    (out/(base+'.lean')).write_text(source.split('def tree : Audit := ',1)[0]+end)
    head=f'''import {base}
import SplitPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent50TNFPilot BB6.Agent47CanonicalFrontier BB6.Agent50SplitPrefix
'''
    def b(x):return str(bool(x)).lower()
    def slot(s):return f'({s//2},{b(s%2)})'
    _,n,s,kids=tree
    assert len(kids)==24
    for group in range(6):
        text=head
        for j in range(4*group,4*group+4):
            text+=f'def child{j} : Audit := {emit(kids[j],i)}\n'
            text+=f'theorem chk{j} : prefixCheck 10006 (refine p {slot(s)} (some ⟨{b(j//12)},{b(j%12>=6)},{j%6}⟩)) child{j} = true := by decide +kernel\n'
        (out/(root+'K'+str(group)+'.lean')).write_text(text+end)
    text='\n'.join('import '+root+'K'+str(j) for j in range(6))+'\n'+head
    text+=f'\ndef tree : Audit := .split {n} {slot(s)} (byMove ['+','.join('child'+str(j) for j in range(24))+'])\n'
    text+='''theorem checked : prefixCheck 10006 p tree = true := by
  unfold tree
  apply split_checked
  · decide +kernel
  · intro mv
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases w <;> cases r
'''
    for q in range(6):
        for j in [q,6+q,12+q,18+q]:text+=f'    · exact chk{j}\n'
    text+=source[source.index('theorem bound (m : Machine)'):]
    (out/(root+'.lean')).write_text(text)
