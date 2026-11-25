"""Generate the finite exact-cost certificate for SHA-pinned raw59/0LB/190.

All rules and every compressed action are checked in Lean, independently of
this generator. Lists include the scanned cell on the left, nearest first.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parent
TABLE = '1RB0LB_1RC0LB_0RD---_1LD1RE_0RF1LA_1RA0LB'
STEPS = 4_136_170
BOUND = 4_200_000
RULES = [
    # direction, state, fixed L, fixed R, consumed block, emitted block, cost
    (1, 1, (0,), (0,), (1,0,1), (1,0,1), 5),
    (-1, 1, (), (), (1,1,0), (0,1,1), 9),
    (-1, 2, (0,1), (0,), (1,1,0), (0,1,1), 9),
]

def moves():
    s=TABLE.replace('_','')
    return [None if x=='---' else (int(x[0]),1 if x[1]=='R' else -1,ord(x[2])-65)
            for x in (s[i:i+3] for i in range(0,36,3))]

def compress():
    table=moves()
    q=0; L=R=(); time=0; actions=[]; raw=0
    while True:
        m=table[2*q+(L[0] if L else 0)]
        if m is None: break
        best=None
        for ix,(d,s,lp,rp,I,O,k) in enumerate(RULES):
            if q!=s or L[:len(lp)]!=lp or R[:len(rp)]!=rp: continue
            x=L[len(lp):] if d<0 else R[len(rp):]
            if x[:9]!=I*3: continue
            n=3
            while x[3*n:3*n+3]==I: n+=1
            if best is None or k*n>best[0]: best=(k*n,ix,n)
        if best:
            if raw: actions.append((-1,raw)); raw=0
            cost,ix,n=best
            d,s,lp,rp,I,O,k=RULES[ix]
            if d<0:
                L=lp+L[len(lp)+3*n:]; R=rp+O*n+R[len(rp):]
            else:
                R=rp+R[len(rp)+3*n:]; L=lp+O*n+L[len(lp):]
            time+=cost; actions.append((ix,n))
        else:
            w,d,q=m
            if d==1:
                L=(R[0] if R else 0,w)+L[1:]; R=R[1:]
            else:
                L=L[1:]; R=(w,)+R
            raw+=1; time+=1
        assert time <= STEPS, 'candidate cost changed'
    if raw: actions.append((-1,raw))
    assert time==STEPS and q==2 and L[0]==1 and len(actions)==5473
    assert len(L)==2121 and len(R)==13
    return actions,q,L,R

def direct():
    # Independent uncompressed two-stack integer run; no macro rules.
    table=moves(); q=a=l=r=0
    for n in range(STEPS+1):
        m=table[2*q+a]
        if m is None:
            assert n==STEPS and (q,a)==(2,1)
            return n,q,a,l,r
        w,d,q=m
        if d==1: l=(l<<1)|w; a=r&1; r>>=1
        else: r=(r<<1)|w; a=l&1; l>>=1
    raise AssertionError('missing exact final query')

def word(xs):
    return '⟨'+str(len(xs))+','+str(sum(b<<i for i,b in enumerate(xs)))+'⟩'

def generate():
    actions,q,L,R=compress()
    names={-1:'raw',0:'right',1:'leftB',2:'leftC'}
    rows=[f'.{names[i]} {n}' for i,n in actions]
    formatted=',\n  '.join(','.join(rows[i:i+16]) for i in range(0,len(rows),16))
    text=f'''import Raw590LB190Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw590LB190
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
open BB6.Agent10ZipAudit BB6Coverage.Agent10ZipAudit

def trace : List Action := [
  {formatted}]
def startB : BZ := ⟨0,⟨0,0⟩,⟨0,0⟩⟩
def endB : BZ := ⟨{q},{word(L)},{word(R)}⟩
theorem check : traceRun trace startB = some endB := by decide +kernel
theorem costCheck : traceCost trace = {STEPS} := by decide +kernel
theorem runCheck : run0 table {STEPS} ⟨0,[],[]⟩ = some endB.decode := by
  have h := trace_sound trace startB endB check
  rwa [costCheck] at h

theorem read_eq : zipRead table {STEPS} = some (2,true) := by
  have h := (run_project table {STEPS} BB6Coverage.Agent31Pump.start).trans runCheck
  unfold zipRead
  cases he : zrun table {STEPS} BB6Coverage.Agent31Pump.start with
  | none => simp [he] at h
  | some z =>
    have h' : project z = endB.decode := by simpa only [he,Option.map_some,Option.some.injEq] using h
    have hslot : (z.q,z.l.headD false) = (2,true) := by
      change ((project z).q,(project z).l.headD false) = _
      rw [h']
      rfl
    simp [he,hslot]

theorem last_ok : zipCheck {BOUND} table (.last {STEPS} (2,true)) = true := by
  simp only [zipCheck,zipQueryOK,read_eq]
  decide

#print axioms runCheck
#print axioms read_eq
#print axioms last_ok
end BB6.Agent32Raw590LB190
'''
    (ROOT/'Raw590LB190Data.lean').write_text(text)
    print('raw59/0LB/190',STEPS,'steps',len(actions),'actions')

if __name__=='__main__':
    direct()
    generate()
