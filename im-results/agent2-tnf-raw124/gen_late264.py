from pathlib import Path
TABLE='1RB0RB_1RC0LB_0RD0LE_1LD1RE_0RA1LF_---0LB'
t=TABLE.replace('_',''); rows=[t[i:i+3] for i in range(0,36,3)]
def step(z):
 q,l,r=z; v=rows[2*q+(l&1)]
 if v=='---': return None
 w,d,s=int(v[0]),v[1],ord(v[2])-65
 return (s,(r&1)+2*w+4*(l//2),r//2) if d=='R' else (s,l//2,w+2*r)
def lit(z):return '⟨'+','.join(map(str,z))+'⟩'
text=['''import Raw124Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace BB6.Agent2.Raw124M264
open BB6Coverage BB6.Agent4.Raw124Packed
open BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent10ZipAudit BB6.Agent8TNFPath
''']
text.append('def table : PartialMachine\n'+ '\n'.join(f'  | ({i//2},{str(bool(i%2)).lower()}) => '+ ('none' if v=='---' else f'some (some ⟨{str(v[0]=="1").lower()},{str(v[1]=="R").lower()},{ord(v[2])-65}⟩)') for i,v in enumerate(rows))+'\n  | _ => none\n')
z=(0,0,0); points=[(0,z)]
for n in range(1,520987):
 z=step(z);assert z is not None
 if n%512==0 or n==520986:points.append((n,z))
assert step(z) is None and z[0]==5 and z[1]%2==0
for i,(n,z) in enumerate(points):text.append(f'def c{i} : PZ := {lit(z)}')
for i in range(len(points)-1):
 k=points[i+1][0]-points[i][0];text.append(f'theorem step{i} : prun table {k} c{i} = some c{i+1} := by decide +kernel')
def join(lo,hi):
 if hi-lo==1:return f'step{lo}'
 mid=(lo+hi)//2; a=join(lo,mid);b=join(mid,hi);name=f'join{lo}_{hi}';n=points[hi][0]-points[lo][0]
 text.append(f'theorem {name} : prun table {n} c{lo} = some c{hi} := pjoin_fixed table {points[mid][0]-points[lo][0]} {points[hi][0]-points[mid][0]} {n} c{lo} c{mid} c{hi} {a} {b} rfl')
 return name
j=join(0,len(points)-1)
text.append(f'theorem trace : prun table 520986 c0 = some c{len(points)-1} := {j}')
text.append('''theorem checked : zipCheck 520988 table (.last 520986 (5,false)) = true :=
  by
    have h := packed_last (p := table) (n := 520986) (B := 520988) (z := c1018) trace (by decide) (by decide) (by decide)
    exact h
theorem root_ok : table initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem no_assigned_halt : weightedTNFNoAssignedHalt table := by
  intro s; rcases s with ⟨q,b⟩
  have h : ∀ q : Fin 6, ∀ b : Bool, table (q,b) ≠ some none := by decide
  exact h q b
theorem bound (m : Machine) (hm : compatible table m) : WeightedBound 520988 m :=
  (certifiedZip 520988 table (.last 520986 (5,false)) root_ok no_assigned_halt checked).sound m hm
#print axioms trace
#print axioms bound
end BB6.Agent2.Raw124M264''')
Path('Raw124M264.lean').write_text('\n'.join(text)+'\n')
