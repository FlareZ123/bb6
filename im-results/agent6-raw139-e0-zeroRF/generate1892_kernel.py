"""Emit the exact packed kernel certificate; all replay data are untrusted.
The Lean checker validates every segment, including the guarded left-tail test.
"""
from pathlib import Path
from verify1892 import TABLE, P, B, T, run

def bl(v):
    return 'true' if v else 'false'

def packed(w):
    return int('1' + w[::-1], 2)

def state(c):
    return f'⟨{c[0]},{packed(c[1])},{packed(c[2])}⟩'

def generate():
    header = '''import PackedGuardedReplay
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent6E0ZeroRF1892
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6GuardedTail BB6.Agent6PackedReplay

def p : PartialMachine := fun s => match s.1.val,s.2 with
'''
    for i,v in enumerate(TABLE):
        if v!=24:
            header+=f'  | {i//2},{bl(i&1)} => some (some ⟨{bl(v&2)},{bl(v&1)},{v//4}⟩)\n'
    header+='''  | _,_ => none

def bits (s : String) : List Bool := s.toList.map (· == '1')
'''
    for name,w in [('P',P),('B',B),('T',T)]:
        header+=f'def {name} := bits "{w}"\n'
    header+='''def C (u : List Bool) : Z0 := ⟨0,P++u,[]⟩
def family (k : Nat) := C (rep B k ++ T)

'''
    out=[header]
    for label,n,start,end,guard,src,dst in [
        ('seed',39854,(0,'',''),(0,P+T,''),False,'⟨0,[],[]⟩','family 0'),
        ('guardedPeriod',16148,(0,P,''),(0,P+B,''),True,'C []','C B')]:
        op='guardedRun' if guard else 'run0'
        g=bl(guard)
        prev=f'pack ({src})';curr=start;proofs=[]
        for i,k in enumerate(range(0,n,512)):
            steps=min(512,n-k);curr=run(*curr,steps,guard)
            name=f'{label}C{i}';proof=f'{label}H{i}'
            nxt=f'pack ({dst})' if k+steps==n else name
            if nxt==name:
                out.append(f'private def {name} : PZ := {state(curr)}\n')
            out.append(f'private theorem {proof} : prun p {g} {steps} ({prev}) = some ({nxt}) := by decide +kernel\n')
            proofs.append(proof);prev=nxt
        assert curr==end
        while len(proofs)>1:
            proofs=[f'(prun_join {proofs[i]} {proofs[i+1]})' if i+1<len(proofs) else proofs[i] for i in range(0,len(proofs),2)]
        out.append(f'theorem {label} : {op} p {n} ({src}) = some ({dst}) := replay_sound p {g} {n} ({src}) ({dst}) {proofs[0]}\n')
    out.append('''theorem pump (tail : List Bool) : run0 p 16148 (C tail) = some (C (B++tail)) := by
  have h := guardedRun_append p 16148 tail guardedPeriod
  simpa only [appendL,C,List.append_nil,List.append_assoc] using h

theorem growth (k : Nat) : run0 p 16148 (family k) = some (family (k+1)) := by
  simpa only [family,rep,List.append_assoc] using pump (rep B k ++ T)

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_growth p family 39854 (fun _ => 16148) seed (by intro k; decide) growth m hm
#print axioms seed
#print axioms guardedPeriod
#print axioms never
end BB6.Agent6E0ZeroRF1892
''')
    return '\n'.join(out)

if __name__=='__main__':
    Path(__file__).with_name('ZeroRF1892Kernel.lean').write_text(generate())
