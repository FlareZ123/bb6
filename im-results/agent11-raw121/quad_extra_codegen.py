"""Additional nested sweep returns on raw121."""
import quad as q, quad_codegen as g, generate_sweeps as one

def phases318(p):
 def F(k=7,var='n'):return q.E(q.lit('0'+'1'*k)+q.rep('111',var))
 def M(k,l,nv=True,jv=True):return q.E(q.lit('0'+'1'*k)+(q.rep('111','n') if nv else ())+q.lit('0'+'1'*l)+(q.rep('111','j') if jv else ()))
 return [(name,st,tg,q.pump(p,st,tg,120)) for name,st,tg in [('first',F(),M(4,3,jv=False)),('inner',M(7,3),M(4,6)),('finish',M(4,3,nv=False),F(10,'j'))]]

header=g.header.split('abbrev P :=')[0].replace('BB6.Agent11Raw121Quadratic','BB6.Agent11Raw121QuadraticExtra')+'''
def innerCost (b s : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => b+s*n+innerCost b s n

theorem innerAll (p : PartialMachine) (M : Nat → Nat → Z0) (b s : Nat)
    (one : ∀ n j, run0 p (b+s*n) (M (n+1) j) = some (M n (j+1)))
    (n j : Nat) : run0 p (innerCost b s n) (M n j) = some (M 0 (j+n)) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have H := join0 (one n j) (ih (j+1))
    simpa only [innerCost,show j+1+n=j+(n+1) by omega] using H

def epochCost (a s b u c v n : Nat) := a+s*n+innerCost b u n+(c+v*n)

theorem growthAll (p : PartialMachine) (F : Nat → Z0) (M : Nat → Nat → Z0) (a s b u c v : Nat)
    (first : ∀ n, run0 p (a+s*n) (F n) = some (M n 0))
    (one : ∀ n j, run0 p (b+u*n) (M (n+1) j) = some (M n (j+1)))
    (last : ∀ j, run0 p (c+v*j) (M 0 j) = some (F (j+1)))
    (n : Nat) : run0 p (epochCost a s b u c v n) (F n) = some (F (n+1)) := by
  have H := join0 (first n) (innerAll p M b u one n 0)
  rw [Nat.zero_add] at H
  exact join0 H (last n)
'''
def generate(i,p,local=False):
 out=[f'namespace M{i}',g.table(p)];co=[]
 phases=phases318(p) if i==318 else q.phases(p)
 for name,st,tg,ans in phases:
  assert ans,(i,name);s,c=g.generate_phase(name,st,tg,ans);out.append(s);co.append(c)
 (a,s,x),(b,u,y),(c,z,v)=co;assert x==y==z==0
 if i==318:
  out.append('''abbrev P := [true,true,true]
def family (n : Nat) : Z0 := ⟨4,[false,true,true,true,true,true,true,true]++rep P n,[]⟩
def middle (n j : Nat) : Z0 := ⟨4,[false,true,true,true,true]++rep P n++[false,true,true,true]++rep P j,[]⟩''');entry=34
 else:
  out.append(g.header.split('abbrev P :=')[1].split('def innerCost')[0].join(['abbrev P :=','']));entry=8
 out.append(f'''theorem first (n : Nat) : run0 table ({a}+{s}*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,{g.simp}] using firstRaw n

theorem inner (n j : Nat) : run0 table ({b}+{u}*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,{g.simp}] using innerRaw n j

theorem finish (j : Nat) : run0 table ({c}+{v}*j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,{g.simp},Nat.one_mul,Nat.zero_mul,Nat.add_zero] using finishRaw j

def cost := epochCost {a} {s} {b} {u} {c} {v}
theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) :=
  growthAll table family middle {a} {s} {b} {u} {c} {v} first inner finish n
''')
 if not local:out.append(f'''theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family {entry} cost entry (by intro n; unfold cost epochCost; omega) growth m hm
#print axioms never''')
 out.append('#print axioms growth\nend M'+str(i));return '\n\n'.join(out)
