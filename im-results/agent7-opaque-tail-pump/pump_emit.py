from pathlib import Path
import hashlib,json
from collections import deque
import argparse
from detect_pump import search,parse,next_step

def bitstring(s): return '['+','.join('true' if x=='1' else 'false' for x in s)+']'
def zexpr(z):
    q,l,r=z
    return f'⟨{q},{bitstring(l)},{bitstring(r)}⟩'

def build(table,out,ns,chunk=170,max_steps=50000,max_macro_steps=2000):
    found=search(table,max_steps,max_macro_steps)
    assert 'entry' in found,found
    moves=parse(table)
    q=0;L=deque();R=deque()
    snaps=[(0,(0,'',''))]
    for t in range(1,found['entry']+1):
        q=next_step(q,L,R,moves)
        assert q is not None
        if t%chunk==0 or t==found['entry']:
            snaps.append((t,(q,''.join(L),''.join(R))))
    expected=(found['state'],found['fixed'],found['pre']+found['tail']) if found['side']=='right' else (found['state'],found['pre']+found['tail'],found['fixed'])
    assert snaps[-1][1]==expected,(snaps[-1][1],expected)
    lines=[
      'import SweepPumping', 'set_option maxRecDepth 100000','set_option maxHeartbeats 0',
      f'namespace {ns}', 'open BB6Coverage BB6Coverage.Agent31Pump',
      'def table : PartialMachine := fun s => match s.1.val,s.2 with',
    ]
    for i,m in enumerate(moves):
        if m=='---':continue
        lines.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(m[0]=="1").lower()},{str(m[1]=="R").lower()},{ord(m[2])-65}⟩)')
    if found['side']=='right':
        before=f'⟨{found["state"]},{bitstring(found["fixed"])},pre++R⟩'
        after=f'⟨{found["state"]},{bitstring(found["fixed"])},pre++block++R⟩'
        family=f'⟨{found["state"]},{bitstring(found["fixed"])},pre++rep block n++tail⟩'
    else:
        before=f'⟨{found["state"]},pre++R,{bitstring(found["fixed"])}⟩'
        after=f'⟨{found["state"]},pre++block++R,{bitstring(found["fixed"])}⟩'
        family=f'⟨{found["state"]},pre++rep block n++tail,{bitstring(found["fixed"])}⟩'
    lines += ['  | _,_ => none',
      'def pre : List Bool := '+bitstring(found['pre']),
      'def block : List Bool := '+bitstring(found['block']),
      'def tail : List Bool := '+bitstring(found['tail']),
      f'theorem one (R : List Bool) : run0 table {found["macro"]} {before} =',
      f'    some {after} := by rfl',
      f'def family (n : Nat) : Z0 := {family}',
      f'theorem growth (n : Nat) : run0 table {found["macro"]} (family n) = some (family (n+1)) := by',
      '  simpa only [family,rep,List.append_assoc] using one (rep block n++tail)',
    ]
    for i,((t0,z0),(t1,z1)) in enumerate(zip(snaps,snaps[1:])):
        lines.extend([f'theorem part{i:03d} : run0 table {t1-t0} {zexpr(z0)} = some {zexpr(z1)} := by rfl'])
    lines.append(f'theorem entry : run0 table {found["entry"]} ⟨0,[],[]⟩ = some (family 0) := by')
    for i in range(len(snaps)-1):
        if i==0:lines.append('  have h0 := part000')
        else:lines.append(f'  have h{i} := join0 h{i-1} part{i:03d}')
    lines += [f'  simpa [family,pre,tail,rep] using h{len(snaps)-2}',
      'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=',
      f'  never_of_growth table family {found["entry"]} (fun _ => {found["macro"]})',
      '    entry (by intro n; decide) growth m hm',
      '#print axioms one','#print axioms growth','#print axioms entry','#print axioms never',
      f'end {ns}']
    source='\n'.join(lines)+'\n'
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    Path(out).write_text(source)
    found['source_sha256']=hashlib.sha256(source.encode()).hexdigest()
    Path(out).with_suffix('.json').write_text(json.dumps(found,indent=2)+'\n')
    return found

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('table');ap.add_argument('out');ap.add_argument('namespace');
    x=ap.parse_args();print(build(x.table,x.out,x.namespace))
