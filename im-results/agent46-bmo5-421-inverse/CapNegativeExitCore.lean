import Std
import Lean.Elab.Tactic.Omega

namespace CapNegative

/-- Exact negative-coordinate domain. -/
def Valid (k w : Nat) : Prop :=
  0 < w ∧ w ≤ 2*k+7 ∧ w%4 = (2*k+3)%4

def stopCount (k w : Nat) : Nat :=
  if w=0 ∨ w=2*k+3 ∨ w=2*k+7 ∨ 2*k+9<3*w then 0
  else stopCount (k+1) (3*w)+1
termination_by 2*k+8-w + (if w=1 then 1 else 0)
decreasing_by
  have hw : 0<w := by omega
  have hle : 3*w≤2*k+9 := by omega
  have h3 : 3*w≠1 := by omega
  by_cases h1 : w=1 <;> simp [h1,h3] <;> omega

theorem step_valid {k w : Nat} (hv : Valid k w) (h : 3*w≤2*k+9) :
    Valid (k+1) (3*w) := by
  unfold Valid at *
  omega

theorem stop_spec {k w : Nat} (hv : Valid k w) :
    let n := stopCount k w
    let j := k+n
    let v := 3^n*w
    Valid j v ∧ (v=2*j+3 ∨ v=2*j+7 ∨ 2*j+9<3*v) := by
  rw [stopCount]
  split
  next h =>
    simp only [Nat.pow_zero,Nat.one_mul,Nat.add_zero]
    exact ⟨hv,by have := hv.1; omega⟩
  next h =>
    have hstep : 3*w≤2*k+9 := by omega
    have hrec := stop_spec (step_valid hv hstep)
    dsimp at hrec ⊢
    rw [Nat.pow_succ, show 3^(stopCount (k+1) (3*w))*3*w=
      3^(stopCount (k+1) (3*w))*(3*w) by ac_rfl,
      show k+(stopCount (k+1) (3*w)+1)=k+1+stopCount (k+1) (3*w) by omega]
    exact hrec
termination_by 2*k+8-w + (if w=1 then 1 else 0)
decreasing_by
  have hw : 0<w := hv.1
  have hle : 3*w≤2*k+9 := by omega
  have h3 : 3*w≠1 := by omega
  by_cases h1 : w=1 <;> simp [h1,h3] <;> omega

/-- Above the negative window, multiplication by three stays above it. -/
theorem above_grows {k w : Nat} (h : 2*k+7<w) (r : Nat) :
    2*(k+r)+7<3^r*w := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
    rw [Nat.pow_succ,show 3^r*3*w=3*(3^r*w) by ac_rfl]
    omega

theorem window_unique {k w a b : Nat}
    (ha : 3^a*w≤2*(k+a)+7 ∧ 2*(k+a)+9<3^(a+1)*w)
    (hb : 3^b*w≤2*(k+b)+7 ∧ 2*(k+b)+9<3^(b+1)*w) : a=b := by
  have hle : ∀ {u v : Nat}, u<v →
      2*(k+u)+9<3^(u+1)*w → 3^v*w≤2*(k+v)+7 → False := by
    intro u v huv hcross hbound
    have hd : v=u+1+(v-u-1) := by omega
    have hstart : 2*(k+u+1)+7<3^(u+1)*w := by omega
    have hh := above_grows hstart (v-u-1)
    rw [←Nat.mul_assoc,←Nat.pow_add] at hh
    rw [show v-u-1+(u+1)=v by omega] at hh
    omega
  by_cases hab : a=b
  · exact hab
  · rcases Nat.lt_or_gt_of_ne hab with h|h
    · exact False.elim (hle h ha.2 hb.1)
    · exact False.elim (hle h hb.2 ha.1)

/-- For bands at least one, terminal and special endpoints automatically
    cross the next negative-window bound. -/
theorem stop_window {k w : Nat} (hk : 1≤k) (hv : Valid k w) :
    let n := stopCount k w
    3^n*w≤2*(k+n)+7 ∧ 2*(k+n)+9<3^(n+1)*w := by
  dsimp
  obtain ⟨hvalid,hstop⟩ := stop_spec hv
  have hb := hvalid.2.1
  rw [Nat.pow_succ,show 3^(stopCount k w)*3*w=3*(3^(stopCount k w)*w) by ac_rfl]
  exact ⟨hb,by omega⟩

/-- Closed-form terminal test for an entire negative excursion. -/
theorem terminal_iff {k w : Nat} (hk : 1≤k) (hv : Valid k w) :
    3^(stopCount k w)*w=2*(k+stopCount k w)+3 ↔
      ∃ n, 3^n*w=2*(k+n)+3 := by
  constructor
  · intro h; exact ⟨_,h⟩
  · rintro ⟨n,hn⟩
    have hw : 3^n*w≤2*(k+n)+7 ∧ 2*(k+n)+9<3^(n+1)*w := by
      rw [Nat.pow_succ,show 3^n*3*w=3*(3^n*w) by ac_rfl]
      omega
    rw [window_unique (stop_window hk hv) hw]
    exact hn

/-- Terminal/special/skip events. The first component is the final negative
    band; none means a terminal there, and some is the positive return. -/
def event (k w : Nat) : Nat × Option (Nat × Nat) :=
  let n := stopCount k w
  let j := k+n
  let v := 3^n*w
  (j, if v=2*j+3 then none
      else if v=2*j+7 then some (j+1,3*j+15)
      else some (j+2,(3*v+3)/2))

theorem event_step {k w : Nat}
    (h : ¬(w=0 ∨ w=2*k+3 ∨ w=2*k+7 ∨ 2*k+9<3*w)) :
    event k w=event (k+1) (3*w) := by
  unfold event
  rw [stopCount,if_neg h]
  dsimp
  rw [Nat.pow_succ,show 3^(stopCount (k+1) (3*w))*3*w=
      3^(stopCount (k+1) (3*w))*(3*w) by ac_rfl,
      show k+(stopCount (k+1) (3*w)+1)=k+1+stopCount (k+1) (3*w) by omega]

theorem event_stop {k w : Nat}
    (h : w=0 ∨ w=2*k+3 ∨ w=2*k+7 ∨ 2*k+9<3*w) :
    event k w=(k,if w=2*k+3 then none
       else if w=2*k+7 then some (k+1,3*k+15)
       else some (k+2,(3*w+3)/2)) := by
  unfold event
  rw [stopCount,if_pos h]
  simp

theorem event_terminal_iff {k w : Nat} (hk : 1≤k) (hv : Valid k w) :
    (event k w).2=none ↔ ∃ n, 3^n*w=2*(k+n)+3 := by
  unfold event
  dsimp
  rw [←terminal_iff hk hv]
  split
  · simp_all
  · rename_i hn
    split <;> simp_all

#print axioms stop_spec
#print axioms terminal_iff
#print axioms event_step
#print axioms event_terminal_iff
end CapNegative
