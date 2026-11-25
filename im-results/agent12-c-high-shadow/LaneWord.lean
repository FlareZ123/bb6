import PlaneOps
namespace BB6.Agent12LaneWord
open BB6.Agent12WordBlock BB6.Agent12BitEventWord BB6.Agent12BitPlanes BB6.Agent12PlaneOps

def inputOK (b : BitState) (direct : Bool) : Prop :=
  4+b.o≤b.b ∧ b.b≤(b.m:Int)+b.o ∧ b.b%2=0 ∧
  (if direct then (b.m:Int)+4+2*b.o≤2*b.b else 2*b.b<(b.m:Int)+4+2*b.o)

def outputOK (b : BitState) : Prop := 2+b.o≤b.b ∧ b.b+14≤(b.m:Int)+b.o

theorem source_step_of_exact_guards (next : Nat × Nat → Option (Nat × Nat))
    (law : EdgeLaw next) (r : Nat) (s : State) (hr : 1≤r)
    (hi : inputOK (lift s) (r==1))
    (ho : outputOK (lift (step r s))) :
    next (decode s)=some (decode (step r s)) := by
  obtain ⟨ha0,hg0,hp0,hb0⟩ := hi
  obtain ⟨hx0,hg1⟩ := ho
  simp only [lift] at ha0 hg0 hp0 hb0 hx0 hg1
  have ha : 2≤s.a := by omega
  have hk : 2≤gap s := by unfold gap; omega
  have hp : consistent s := by unfold consistent parity at *; omega
  have hv : valid s := ⟨by omega,by omega,hp⟩
  have hx : 0≤(step r s).a := by omega
  have hg : 16≤gap (step r s) := by unfold gap; omega
  have hb : if r=1 then (s.m:Int)≤2*s.a else 2*s.a<(s.m:Int) := by
    by_cases h:r=1 <;> simp [h] at hb0 ⊢ <;> omega
  have hv' : valid (step r s) := ⟨hx,by omega,step_consistent r s hr⟩
  obtain ⟨_,ha0,hk0,hm0⟩ := decode_coords s hv
  obtain ⟨_,hx0,hy0,hm1⟩ := decode_coords (step r s) hv'
  let a := (decode s).1
  let k := (decode s).2
  let x := (decode (step r s)).1
  let y := (decode (step r s)).2
  change next (a,k)=some (x,y)
  change (a:Int)=s.a at ha0
  change 2*(k:Int)=gap s at hk0
  change a+2*k=s.m at hm0
  change (x:Int)=(step r s).a at hx0
  change 2*(y:Int)=gap (step r s) at hy0
  change x+2*y=(step r s).m at hm1
  have hpar : parity s=(a%2:Nat) := by unfold consistent at hp; omega
  have hM : x+2*y=a+2*k+3*r+1 := by
    change x+2*y=s.m+3*r+1 at hm1
    omega
  have hA : (2:Int)^r*((a:Int)+2+(a%2:Nat))=2*(x:Int)+2*(y:Int)+2*(a%2:Nat) := by
    have hrel : (2:Int)^r*(s.a+2+parity s)=(step r s).a+((step r s).m:Int)+2*parity s := by simp [step]; omega
    rw [←ha0,hpar,←hx0,←hm1] at hrel
    push_cast at hrel
    simpa [Int.add_assoc,Int.two_mul] using hrel
  have hbranch : if r=1 then 2*k≤a else a<2*k := by
    split
    next h => rw [if_pos h] at hb; unfold gap at hk0; omega
    next h => rw [if_neg h] at hb; unfold gap at hk0; omega
  exact law a k x y r hr (by omega) (by omega) (by omega) hbranch hM (by exact_mod_cast hA)

/-- A semantic trace of the bit interpreter. Only at actual event boundaries
    are counter guards imposed. -/
structure LaneSpec (q N : Nat) (u : Nat → BitState) : Prop where
  next : ∀ j<N, u j=tick (q.testBit j) (u (j+1))
  input : ∀ j, 0<j → j≤N → (j=N ∨ q.testBit j=true) → inputOK (u j) (q.testBit (j-1))
  output : ∀ j<N, q.testBit j=true → outputOK (u j)
  closed : q.testBit 0=true

/-- Bitwise recurrence plus actual local guards certifies arbitrary long words,
    without any mass/maximum-shift or streak assumption. -/
theorem lane_word (next : Nat × Nat → Option (Nat × Nat)) (law : EdgeLaw next)
    (q N : Nat) (u : Nat→BitState) (spec : LaneSpec q N u)
    (n d : Nat) (s : State) (hn : n+d≤N)
    (hstart : u (n+d)=lift s) (hevent : n+d=N ∨ q.testBit (n+d)=true)
    (hidle : u n=idle d (lift s)) (hfirst : 0<d → q.testBit (n+d-1)=false)
    (h0 : n=0 → d=0) :
    runNext next (word q d n).length (some (decode s))=some (decode (run (word q d n) s)) ∧
    u 0=lift (run (word q d n) s) := by
  induction n generalizing d s with
  | zero => simp [word,run,runNext,h0 rfl,idle_zero] at hidle ⊢; exact hidle
  | succ n ih =>
    have hnext := spec.next n (by omega)
    rw [hidle] at hnext
    cases hbit:q.testBit n
    · have hn0 : n≠0 := by intro h; subst n; rw [spec.closed] at hbit; contradiction
      have heq : n+(d+1)=n+1+d := by omega
      simp only [word,hbit,Bool.false_eq_true,ite_false]
      rw [hbit,tick_false_idle] at hnext
      apply ih (d+1) s (by omega) (by rwa [heq]) (by rwa [heq]) hnext
      · intro _
        by_cases hd:d=0
        · simpa [hd] using hbit
        · rw [heq]; exact hfirst (by omega)
      · intro h; exact False.elim (hn0 h)
    · rw [hbit,tick_true_lift] at hnext
      have hi := spec.input (n+1+d) (by omega) hn hevent
      rw [hstart] at hi
      have hdir : q.testBit (n+1+d-1) = ((d+1)==1) := by
        by_cases hd:d=0
        · simpa [hd] using hbit
        · rw [hfirst (by omega)]; simp [hd]
      rw [hdir] at hi
      have ho:=spec.output n (by omega) hbit
      rw [hnext] at ho
      have hedge:=source_step_of_exact_guards next law (d+1) s (by omega) hi ho
      have hind := ih 0 (step (d+1) s) (by omega) (by simpa using hnext) (Or.inr (by simpa using hbit))
          (by simpa [idle_zero] using hnext) (by omega) (by simp)
      simp only [word,hbit,ite_true,List.length_cons,runNext,Option.bind_some,hedge,run]
      exact hind

#print axioms source_step_of_exact_guards
#print axioms lane_word
end BB6.Agent12LaneWord
