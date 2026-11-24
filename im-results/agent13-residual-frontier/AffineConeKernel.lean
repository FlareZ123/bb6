import FullSectionInverse
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 4000000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace BB6.Agent13AffineCone
open BB6.Agent46

private theorem valuation_not_power (q v : Nat)
    (hv : q % 2^(v+1) = 2^v) (hgt : 2^v<q) : ∀ n, q≠2^n := by
  intro n hn
  by_cases h : n≤v
  · have hm : 2^n≤2^v := Nat.pow_le_pow_right (by decide) h
    omega
  · have hd : 2^(v+1)∣2^n := Nat.pow_dvd_pow 2 (by omega)
    rw [←hn] at hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    have hp : 0<2^v := Nat.pow_pos (by decide)
    omega

private theorem high_depth_bound (q v n b : Nat)
    (hv : q%2^(v+1)=2^v) (he : b%2=0)
    (hm : q=2^(n+1)*b) : n+2≤v := by
  by_cases h : n+2≤v
  · exact h
  · exfalso
    have hbe : b=2*(b/2) := by omega
    have hd : 2^(n+2)∣q := by
      refine ⟨b/2,?_⟩
      calc
        q = 2^(n+1)*b := hm
        _ = 2^(n+1)*(2*(b/2)) := by conv => lhs; rw [hbe]
        _ = 2^(n+2)*(b/2) := by rw [show (2:Nat)^(n+2)=2^(n+1)*2 by rfl, Nat.mul_assoc]
    have hd' : 2^(v+1)∣q := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hd
    have hz := Nat.mod_eq_zero_of_dvd hd'
    have hp : 0<2^v := Nat.pow_pos (by decide)
    omega

/-- Uniform all-depth parent equations with one exact 2-adic valuation.
    Exceptional a=0/1 branches have pure-power mass (or small output);
    ordinary high parents have depth bounded by v-2. -/
theorem parent_equations (a k x y v : Nat)
    (hy : 8≤y)
    (hv : (x+y+(x+y)%2)%2^(v+1)=2^v)
    (hgt : 2^v<x+y+(x+y)%2)
    (h : sectionPreimageCriterion a k x y) :
    (y%2=0 ∧ a+2=x+y ∧ 2*k+2=y) ∨
    ∃ n, n+2≤v ∧ n%2=(x+1+(x+y)%2)%2 ∧
      x+y+(x+y)%2=2^(n+1)*(a+2+(x+y)%2) ∧
      2*k+a+7+3*n=x+2*y := by
  have hnp := valuation_not_power (x+y+(x+y)%2) v hv hgt
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageCriterion,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [sectionPreimageCriterion,ha0,hk0,hk1] at h
        omega
      · simp only [sectionPreimageCriterion,if_pos ha0,if_neg hk0,if_neg hk1] at h
        obtain ⟨n,hp,_⟩ := h
        have hsum : (x+y)%2=0 := by rw [hp]; simp [Nat.mul_mod]
        have he : x+y+(x+y)%2=2^(n+3) := by
          rw [hsum,Nat.add_zero,hp,Nat.pow_add]
        exact (hnp (n+3) he).elim
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,ha1,hk0] at h
      · by_cases hk1 : k=1
        · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2] at h
            omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2,hk3] at h
              omega
            · simp only [sectionPreimageCriterion,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
              obtain ⟨n,hp,_⟩ := h
              have hsum : (x+y+1)%2=0 := by rw [hp]; simp [Nat.mul_mod]
              have hs : (x+y)%2=1 := by omega
              have he : x+y+(x+y)%2=2^(n+4) := by rw [hs,hp,Nat.pow_add]
              exact (hnp (n+4) he).elim
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,ha1,hk0] at h
      · by_cases hl : 2*k≤a
        · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,if_neg hk0,if_pos hl] at h
          left
          omega
        · by_cases he : a%2=0
          · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hl,if_pos he] at h
            obtain ⟨n,hp,hc⟩ := h
            have hfac : 2*(a-1)+6=2*(a+2) := by omega
            rw [hfac] at hp
            have hs : (x+y)%2=0 := by rw [hp]; simp [Nat.mul_mod]
            have hm : x+y+(x+y)%2=2^(n+1)*(a+2+(x+y)%2) := by
              rw [hs,Nat.add_zero,Nat.add_zero,hp,Nat.pow_succ,Nat.mul_assoc]
            have hn := high_depth_bound _ v n (a+2+(x+y)%2) hv (by omega) hm
            exact Or.inr ⟨n,hn,by omega,hm,by omega⟩
          · simp only [sectionPreimageCriterion,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hl,if_neg he] at h
            obtain ⟨n,hp,hc⟩ := h
            have hfac : 2*(a-1)+8=2*(a+3) := by omega
            rw [hfac] at hp
            have hs1 : (x+y+1)%2=0 := by rw [hp]; simp [Nat.mul_mod]
            have hs : (x+y)%2=1 := by omega
            have hm : x+y+(x+y)%2=2^(n+1)*(a+2+(x+y)%2) := by
              rw [hs,hp,Nat.pow_succ,Nat.mul_assoc]
            have hn := high_depth_bound _ v n (a+2+(x+y)%2) hv (by omega) hm
            exact Or.inr ⟨n,hn,by omega,hm,by omega⟩

structure Linear where
  s : Nat
  b : Nat
  deriving Repr, DecidableEq
structure Ray where
  x : Linear
  y : Linear
  deriving Repr, DecidableEq

def Linear.eval (l : Linear) (t : Nat) : Nat := l.s*t+l.b
def oddMass (r : Ray) : Nat := (r.x.b+r.y.b)%2
def qSlope (r : Ray) : Nat := r.x.s+r.y.s
def qBase (r : Ray) : Nat := r.x.b+r.y.b+oddMass r

def leaf (r : Ray) : Bool := decide (5≤r.y.b ∧ r.y.s%2=0 ∧ r.y.b%2=1 ∧
  (r.x.s+r.y.s)%4=0 ∧ ((r.x.b+r.y.b)%4=1 ∨ (r.x.b+r.y.b)%4=2))

def v2Aux : Nat → Nat → Nat
  | 0, _ => 0
  | f+1, n => if n%2=0 then 1+v2Aux f (n/2) else 0

def valuation (r : Ray) : Nat := v2Aux (Nat.log2 (qBase r)+1) (qBase r)

def branch (r : Ray) (v : Nat) : Bool := decide (5<r.x.b ∧ 8≤r.y.b ∧
  r.x.s%2=0 ∧ r.y.s%2=0 ∧ qBase r%2^(v+1)=2^v ∧
  qSlope r%2^(v+1)=0 ∧ 2^v<qBase r)

def direct (r : Ray) : Ray := ⟨⟨r.x.s+r.y.s,r.x.b+r.y.b-2⟩,⟨r.y.s/2,(r.y.b-2)/2⟩⟩

def directValid (r c : Ray) : Bool := decide (
  c.x.s=r.x.s+r.y.s ∧ c.x.b+2=r.x.b+r.y.b ∧
  2*c.y.s=r.y.s ∧ 2*c.y.b+2=r.y.b)

def high (r : Ray) (n : Nat) : Ray :=
  let d := 2^(n+1)
  let a : Linear := ⟨qSlope r/d,qBase r/d-(2+oddMass r)⟩
  ⟨a,⟨(r.x.s+2*r.y.s-a.s)/2,(r.x.b+2*r.y.b-a.b-(7+3*n))/2⟩⟩

def highValid (r c : Ray) (n : Nat) : Bool := decide (
  2^(n+1)*c.x.s=qSlope r ∧ 2^(n+1)*(c.x.b+2+oddMass r)=qBase r ∧
  2*c.y.s+c.x.s=r.x.s+2*r.y.s ∧ 2*c.y.b+c.x.b+7+3*n=r.x.b+2*r.y.b)

def allowedDepth (r : Ray) (v n : Nat) : Bool := decide (n+2≤v ∧ n%2=(r.x.b+1+oddMass r)%2)

/-- True means every possible predecessor is covered by an affine
    child and all leaves satisfy the odd-image obstruction.
    Fuel limits proof tree height, not machine time. -/
def excluded : Nat → Ray → Bool
  | 0,r => leaf r
  | f+1,r => leaf r || (branch r (valuation r) &&
      (if r.y.b%2=0 then directValid r (direct r) && excluded f (direct r) else true) &&
      (List.range (valuation r+1)).all (fun n => if allowedDepth r (valuation r) n then
        highValid r (high r n) n && excluded f (high r n) else true))

private theorem mod_linear (s b t m : Nat) (h : s%m=0) : (s*t+b)%m=b%m := by
  rw [Nat.add_mod, Nat.mul_mod, h]
  simp

private theorem eval_parity (l : Linear) (t : Nat) (h : l.s%2=0) : l.eval t%2=l.b%2 :=
  mod_linear l.s l.b t 2 h

private theorem eval_sum (r : Ray) (t : Nat) :
    r.x.eval t+r.y.eval t=qSlope r*t+r.x.b+r.y.b := by
  simp only [Linear.eval,qSlope,Nat.add_mul]
  omega

private theorem eval_oddMass (r : Ray) (t : Nat) (hx : r.x.s%2=0) (hy : r.y.s%2=0) :
    (r.x.eval t+r.y.eval t)%2=oddMass r := by
  unfold oddMass
  rw [Nat.add_mod,eval_parity _ _ hx,eval_parity _ _ hy,←Nat.add_mod]

private theorem eval_q (r : Ray) (t : Nat) (hx : r.x.s%2=0) (hy : r.y.s%2=0) :
    r.x.eval t+r.y.eval t+(r.x.eval t+r.y.eval t)%2=qSlope r*t+qBase r := by
  rw [eval_oddMass r t hx hy,eval_sum]
  unfold qBase
  omega

private theorem leaf_sound (reach : Nat → Nat → Prop)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (r : Ray) (t : Nat) (h : leaf r=true) : ¬reach (r.x.eval t) (r.y.eval t) := by
  obtain ⟨h5,hs,hb,h4,hsum⟩ := of_decide_eq_true h
  apply forbid
  · unfold Linear.eval; omega
  · rw [eval_parity _ _ hs]; exact hb
  · have he : (r.x.eval t+r.y.eval t)%4=(r.x.b+r.y.b)%4 := by
      rw [eval_sum,show qSlope r*t+r.x.b+r.y.b=qSlope r*t+(r.x.b+r.y.b) by omega]
      exact mod_linear _ _ _ _ h4
    rwa [he]

private theorem direct_eval (r c : Ray) (t a k : Nat)
    (h : directValid r c=true) (ha : a+2=r.x.eval t+r.y.eval t)
    (hk : 2*k+2=r.y.eval t) : a=c.x.eval t ∧ k=c.y.eval t := by
  obtain ⟨hxs,hxb,hys,hyb⟩ := of_decide_eq_true h
  have hx : c.x.eval t+2=r.x.eval t+r.y.eval t := by
    simp only [Linear.eval,hxs,Nat.add_mul]; omega
  have hy : 2*c.y.eval t+2=r.y.eval t := by
    simp only [Linear.eval,Nat.mul_add,←Nat.mul_assoc,hys]; omega
  omega

private theorem high_eval (r c : Ray) (t a k n : Nat)
    (h : highValid r c n=true)
    (ha : qSlope r*t+qBase r=2^(n+1)*(a+2+oddMass r))
    (hk : 2*k+a+7+3*n=r.x.eval t+2*r.y.eval t) : a=c.x.eval t ∧ k=c.y.eval t := by
  obtain ⟨hxs,hxb,hys,hyb⟩ := of_decide_eq_true h
  have hx : 2^(n+1)*(c.x.eval t+2+oddMass r)=qSlope r*t+qBase r := by
    simp only [Linear.eval,Nat.mul_add,←Nat.mul_assoc,hxs]
    simp only [Nat.mul_add] at hxb
    omega
  have heq : 2^(n+1)*(a+2+oddMass r)=2^(n+1)*(c.x.eval t+2+oddMass r) := ha.symm.trans hx.symm
  have heq' := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0<(2:Nat))) heq
  have hae : a=c.x.eval t := by omega
  have hy : 2*c.y.eval t+c.x.eval t+7+3*n=r.x.eval t+2*r.y.eval t := by
    simp only [Linear.eval,Nat.mul_add,←Nat.mul_assoc]
    have h : (2*c.y.s+c.x.s)*t=(r.x.s+2*r.y.s)*t := congrArg (·*t) hys
    simp only [Nat.add_mul] at h
    omega
  omega

/-- The checker proves exclusion for every parameter, with all original
    section predecessors covered (including any spurious candidates). -/
theorem excluded_sound (reach : Nat → Nat → Prop)
    (parent : ∀ x y, 5<x → 8≤y → reach x y → ∃ a k, reach a k ∧ sectionPreimageCriterion a k x y)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (f : Nat) (r : Ray) (h : excluded f r=true) (t : Nat) : ¬reach (r.x.eval t) (r.y.eval t) := by
  induction f generalizing r with
  | zero => exact leaf_sound reach forbid r t h
  | succ f ih =>
    simp only [excluded,Bool.or_eq_true,Bool.and_eq_true] at h
    rcases h with hl | ⟨⟨hb,hd⟩,hh⟩
    · exact leaf_sound reach forbid r t hl
    · intro hr
      let v := valuation r
      obtain ⟨hx5,hy8,hxs,hys,hv,hq,hlow⟩ := of_decide_eq_true hb
      change 2^v<qBase r at hlow
      have hx5' : 5<r.x.eval t := by unfold Linear.eval; omega
      have hy8' : 8≤r.y.eval t := by unfold Linear.eval; omega
      have heq := eval_q r t hxs hys
      have hv' : (r.x.eval t+r.y.eval t+(r.x.eval t+r.y.eval t)%2)%2^(v+1)=2^v := by
        rw [heq,mod_linear _ _ _ _ hq]; exact hv
      have hlow' : 2^v<r.x.eval t+r.y.eval t+(r.x.eval t+r.y.eval t)%2 := by rw [heq]; omega
      obtain ⟨a,k,hrp,hp⟩ := parent _ _ hx5' hy8' hr
      rcases parent_equations a k _ _ v hy8' hv' hlow' hp with hd' | hh'
      · obtain ⟨hye,ha,hk⟩ := hd'
        have hb0 : r.y.b%2=0 := by rwa [eval_parity _ _ hys] at hye
        simp only [hb0,if_true,Bool.and_eq_true] at hd
        obtain ⟨ha',hk'⟩ := direct_eval r (direct r) t a k hd.1 ha hk
        rw [ha',hk'] at hrp
        exact ih _ hd.2 hrp
      · obtain ⟨n,hn,hpar,ha,hk⟩ := hh'
        have hp0 : n%2=(r.x.b+1+oddMass r)%2 := by
          rw [eval_oddMass _ _ hxs hys] at hpar
          have hxp := eval_parity r.x t hxs
          omega
        have hn' : n∈List.range (valuation r+1) := List.mem_range.mpr (by change n<v+1; omega)
        have hchk := (List.all_eq_true.mp hh) n hn'
        have had : allowedDepth r (valuation r) n=true := decide_eq_true ⟨hn,hp0⟩
        simp only [had,if_true,Bool.and_eq_true] at hchk
        rw [heq,eval_oddMass _ _ hxs hys] at ha
        obtain ⟨ha',hk'⟩ := high_eval r (high r n) t a k n hchk.1 ha hk
        rw [ha',hk'] at hrp
        exact ih _ hchk.2 hrp

#print axioms parent_equations
#print axioms excluded_sound
end BB6.Agent13AffineCone
