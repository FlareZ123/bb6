"""Exact source-checked one/two-repeat growth for seven irregular live rows."""
from generate_digit_sections import C,M,w,cfg,find,prove
from generate_oneRA_counter import D,cfg2,replay2,prove2
from pathlib import Path
import sys

SPECS=[(44,267,4,244),(372,265,4,244),(311,435,10,292),(353,435,10,292),(363,487,4,356)]
def header(rows,i):
 m=M(rows[i]);lines=['import Raw54RAClosedCore','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace BB6.Agent8Raw54.OneRAGrow.M{i}','open BB6Coverage BB6Coverage.Agent31Pump','def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
 for j,a in enumerate(m.a):
  if a=='---':continue
  b,r,q=a;lines.append(f'  | {j//2},{str(bool(j%2)).lower()} => some (some ⟨{str(b=="1").lower()},{str(r=="R").lower()},{ord(q)-65}⟩)')
 return lines+['  | _,_ => none']
def write(out,i,lines):
 out.joinpath(f'Raw54OneRAGrow{i}.lean').write_text('\n'.join(lines+['#print axioms never',f'end BB6.Agent8Raw54.OneRAGrow.M{i}'])+'\n')
def emit2(rows,out,i,e,start,target,cf):
 m=M(rows[i]);ops=replay2(m,start,target,cf);assert ops,i
 a,b,c=cf;f=cfg2(start).replace(' j)',' p.1)').replace(' k)',' p.2)')
 write(out,i,header(rows,i)+[prove2('epoch',start,target,cf,ops,False),f'def family (p : Nat × Nat) : Z0 := {f}',f'''theorem closed (p : Nat × Nat) : ∃ t p', 0<t ∧ run0 table t (family p) = some (family p') := by
  obtain ⟨j,k⟩ := p
  refine ⟨{a}*j+{b}*k+{c},(j+1,k+1),by omega,?_⟩
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using epoch j k
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.RAClosed.neverOfSection table (Nat × Nat) family (0,0) {e} (by rfl) closed m hm'''])
def emit(rows,out):
 for i,e,u,c in SPECS:
  S='1'*u
  if i==363:S+='000001111'
  start=D(0,'01','0000001111000V'+S+'W0111',('000','01111'))
  target=D(0,'01','0000001111000000V'+S+'01111W0111',start.ps)
  emit2(rows,out,i,e,start,target,(48,48,c))
 s=D(0,'01','000'+'1'*16+'V'+'0111111'+'W'+'011111111',('1111','0111111'))
 t=D(0,'01','000'+'1'*20+'V'+'0111111'+'0111111'+'W'+'011111111',s.ps)
 emit2(rows,out,233,470,s,t,(24,48,301))
 m=M(rows[37]);a=C(0,'011','0101V1','01010101');b=C(0,'011','010101V','01010101');c=C(0,'011','010101010101V1','01010101');aa=find(m,a,b);bb=find(m,b,c)
 assert aa and bb and aa[:2]==(28,23) and bb[:2]==(28,49)
 write(out,37,header(rows,37)+[prove('phase1',a,b,aa,False),prove('phase2',b,c,bb,False),f'def family (p : Bool × Nat) : Z0 :=\n  match p with\n  | (false,n) => {cfg(a)}\n  | (true,n) => {cfg(b)}','''theorem closed (p : Bool × Nat) : ∃ t p', 0<t ∧ run0 table t (family p) = some (family p') := by
  obtain ⟨b,n⟩ := p
  cases b
  · exact ⟨28*n+23,(true,n),by omega,phase1 n⟩
  · refine ⟨28*n+49,(false,n+1),by omega,?_⟩
    simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using phase2 n
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.RAClosed.neverOfSection table (Bool × Nat) family (false,0) 28 (by rfl) closed m hm'''])
if __name__=='__main__':
 emit(Path(sys.argv[1]).read_text().splitlines(),Path(sys.argv[2]))
