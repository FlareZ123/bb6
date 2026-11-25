"""Generate kernel-checkable long first-hole certificate; no native_decide."""
TABLE = '1RB1LE_1RC---_0RD1RA_1LD1RE_0LF0LE_1RF0RC'
rows = [r for pair in TABLE.split('_') for r in (pair[:3], pair[3:])]
q=l=r=n=0
trace=[]
checkpoints=[(0,0,0)]
def runlen(x,b):
    y=x if b==0 else ~x
    return (y&-y).bit_length()-1 if y else 0
while (a:=rows[q*2+l%2])!='---':
    w,d,s=int(a[0]),a[1],ord(a[2])-65
    b=l%2
    if s==q:
        x=l if d=='L' else r
        k=runlen(x,b)
        if d=='R': k+=1
        if k>1:
            if d=='L':
                l,r=l>>k,(r<<k)+w*((1<<k)-1)
                ins=('.left',k)
            else:
                tail=r>>(k-1)
                l,r=tail%2+2*((l//2<<k)+w*((1<<k)-1)),tail//2
                ins=('.right',k-1)
            trace.append(ins); n+=k;checkpoints.append((q,l,r));continue
    if d=='L': l,r=l//2,w+2*r
    else: l,r=r%2+2*(w+2*(l//2)),r//2
    q=s;n+=1
    if trace and trace[-1][0]=='.ordinary':
        trace[-1]=('.ordinary',trace[-1][1]+1);checkpoints[-1]=(q,l,r)
    else:
        trace.append(('.ordinary',1));checkpoints.append((q,l,r))
assert n==756495 and (q,l%2)==(1,1)
print("""import PackedSweep
import ZipThreeHoleAudit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
namespace BB6.Agent16Raw118
open BB6Coverage BB6Coverage.Agent16Packed BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with""")
for j,a in enumerate(rows):
    if a!='---':
        print(f"  | {j//2},{str(bool(j%2)).lower()} => some (some ⟨{str(a[0]=='1').lower()},{str(a[1]=='R').lower()},{ord(a[2])-65}⟩)")
print("  | _,_ => none")
def p(i):
    q,l,r=checkpoints[i];return f'⟨{q}, {l}, {r}⟩'
chunks=[]
for j in range(0,len(trace),100):
    end=min(j+100,len(trace)); chunk=trace[j:end]; i=len(chunks); cost=sum(k+(op=='.right') for op,k in chunk)
    chunks.append((i,cost))
    body=', '.join(f'{op} {k}' for op,k in chunk)
    print(f'def block{i} : List Instr := [{body}]\ntheorem proof{i} : prun table {cost} {p(j)} = some {p(end)} :=\n  execList_sound table block{i} _ _ (by rfl)')
print(f'theorem longRun : prun table {n} ⟨0,0,0⟩ = some {p(len(trace))} := by')
print('  have h0 := proof0')
for i,cost in chunks[1:]: print(f'  have h{i} := prun_join h{i-1} proof{i}')
print(f'  exact h{len(chunks)-1}')
print("""theorem longRead : zipRead table 756495 = some (1,true) := by
  rw [←packedRead_eq, packedRead]
  change (prun table 756495 ⟨0,0,0⟩).map (fun z => (z.q,z.l % 2 == 1)) = _
  rw [longRun]
  rfl
theorem longCheck : zipCheck 756496 table (.last 756495 (1,true)) = true := by
  simp only [zipCheck,zipQueryOK,longRead]
  decide
theorem nohalt : weightedTNFNoAssignedHalt table := by
  intro s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases b <;> decide
noncomputable def longCertificate : WeightedTNFCertificate 756496 table 6 :=
  certifiedZip 756496 table (.last 756495 (1,true)) (by decide) nohalt longCheck
#print axioms longRead
#print axioms longCertificate
end BB6.Agent16Raw118""")
