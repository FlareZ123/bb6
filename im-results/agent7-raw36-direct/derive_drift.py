"""Produce a kernel-checkable exact 902-step opaque-tail pumping proof.

Target: the sole 0RE B1 residual of direct Raw36 D1=0LB:
1RB1LF_1RC0RE_0RD1RA_0LD0LB_1LF---_0LA1LC.

At blank-tape step 14958 the head is C reading blank, with empty left ray,
and a right ray with fixed 8-bit prefix. A literal 902-step transition
returns to the same state, prepending a 20-bit word *without reading the
arbitrary remainder*. Induction yields an infinite run for all completions.

This generator is discovery/proof assembly only; the Lean kernel checks every
transition, the entry and the formal NeverHalts statement. An assertion here
is not a substitute for the Lean check.
"""
from pathlib import Path
import argparse,json

TABLE='1RB1LF_1RC0RE_0RD1RA_0LD0LB_1LF---_0LA1LC'
MOVES=[TABLE.replace('_','')[i:i+3] for i in range(0,36,3)]
ENTRY=14958
CYCLE=902
PREFIX='11111010'
BLOCK='01001001001001001001'
NS='BB6.Agent7Raw36D101Hard10'

def bitstring(s):
    return '['+','.join('true' if x=='1' else 'false' for x in s)+']'

def zexpr(z):
    q,l,r=z
    return f'⟨{q}, {bitstring(l)}, {bitstring(r)}⟩'

def move(z):
    q,l,r=z
    read=int((l+'0')[0])
    mv=MOVES[2*q+read]
    assert mv!='---',('halted',z)
    q=ord(mv[2])-65
    if mv[1]=='R':
        b=(r+'0')[0]
        return (q,b+mv[0]+l[1:],r[1:])
    return (q,l[1:],mv[0]+r)

def symbolic(z):
    q,l,r=z
    read=(l+'0')[0]
    assert read in '01',('opaque read',z)
    mv=MOVES[2*q+int(read)]
    assert mv!='---',('halt',z)
    q=ord(mv[2])-65
    if mv[1]=='R':
        b=(r+'0')[0]
        assert b in '01',('opaque right read',z)
        return(q,b+mv[0]+l[1:],r[1:])
    return(q,l[1:],mv[0]+r)

def source(chunk):
    assert 1<=chunk<=1000
    z=(0,'','')
    snapshots=[(0,z)]
    for t in range(1,ENTRY+1):
        z=move(z)
        if t%chunk==0 or t==ENTRY:snapshots.append((t,z))
    q,l,r=z
    assert q==2 and l=='' and r.startswith(PREFIX) and len(r)==114,(q,l,r)
    tail=r[len(PREFIX):]
    assert len(tail)==106
    # The universal opaque-tail transition must NOT inspect the symbol '?':
    zz=(2,'',PREFIX+'?')
    for j in range(CYCLE):zz=symbolic(zz)
    assert zz==(2,'',PREFIX+BLOCK+'?'),(zz,'failed universal pump')
    forward=z
    for j in range(CYCLE):forward=move(forward)
    assert forward==(2,'',PREFIX+BLOCK+tail)
    out=[
      'import SweepPumping',
      'set_option maxRecDepth 100000',
      'set_option maxHeartbeats 0',
      f'namespace {NS}',
      'open BB6Coverage BB6Coverage.Agent31Pump',
      '',
      '/-- Exact literal Raw36 D1=0LB, B1=0RE residual. -/',
      'def table : PartialMachine := fun s => match s.1.val,s.2 with',
    ]
    for i,mv in enumerate(MOVES):
        if mv=='---':continue
        out.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(mv[0]=="1").lower()},{str(mv[1]=="R").lower()},{ord(mv[2])-65}⟩)')
    out += [
       '  | _,_ => none',
       '',
       'def pre : List Bool := '+bitstring(PREFIX),
       'def block : List Bool := '+bitstring(BLOCK),
       'def tail : List Bool := '+bitstring(tail),
       '',
       '/-- A fixed-length left drift pumps a word before an *arbitrary*',
       '    untouched right tape, not merely the observed finite simulation. -/',
       'theorem one (R : List Bool) :',
       '    run0 table 902 ⟨2,[],pre++R⟩ =',
       '      some ⟨2,[],pre++block++R⟩ := by rfl',
       '',
       'def family (n : Nat) : Z0 := ⟨2,[],pre++rep block n++tail⟩',
       '',
       'theorem growth (n : Nat) :',
       '    run0 table 902 (family n) = some (family (n+1)) := by',
       '  simpa only [family,rep,List.append_assoc] using one (rep block n++tail)',
       ''
    ]
    for j,((start,a),(end,b)) in enumerate(zip(snapshots,snapshots[1:])):
        out += [f'theorem entry{j:02d} :',
                f'    run0 table {end-start} {zexpr(a)} = some {zexpr(b)} := by rfl','']
    out += [
        f'/-- Finite blank-tape entry at exactly {ENTRY} ordinary transitions. -/',
        'theorem entry : run0 table 14958 ⟨0,[],[]⟩ = some (family 0) := by',
    ]
    for j in range(len(snapshots)-1):
        if j==0:out.append(f'  have h{j} := entry{j:02d}')
        else:out.append(f'  have h{j} := join0 h{j-1} entry{j:02d}')
    out += [
        f'  simpa [family,pre,tail,rep] using h{len(snapshots)-2}',
        '',
        '/-- All compatible completions are nonhalting, by exact 902-step pumping. -/',
        'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=',
        '  never_of_growth table family 14958 (fun _ => 902)',
        '    entry (by intro n; decide) growth m hm',
        '',
        '#print axioms one',
        '#print axioms growth',
        '#print axioms entry',
        '#print axioms never',
        f'end {NS}',
    ]
    return '\n'.join(out)+'\n',{'entry':ENTRY,'pump':CYCLE,'pre':PREFIX,'block':BLOCK,
       'tail_bits':len(tail),'entry_lemmas':len(snapshots)-1,
       'universal_step_checked_against_opaque_tail':True}

def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True)
    p.add_argument('--chunk',type=int,default=180);a=p.parse_args()
    src,stats=source(a.chunk)
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(src)
    a.out.with_suffix('.json').write_text(json.dumps(stats,indent=2)+'\n')
    print(json.dumps({'path':str(a.out),'bytes':len(src),**stats}),flush=True)

if __name__=='__main__':main()
