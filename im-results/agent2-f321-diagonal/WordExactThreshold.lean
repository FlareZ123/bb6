import WordGuardComplete
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321ExactThreshold
open BB6.Agent31F321Density
open BB6.Agent2F321Bulk
open BB6.Agent2F321Diagonal
open BB6.Agent2F321LastFarExact
open BB6.Agent2F321WordGuard

/-- The guard for a letter, expressed purely in terms of the terminal scale
    and coefficients of the remaining word (including this letter). -/
def guardAt (w : List InverseLetter) (T : Nat) : Prop :=
  match w with
  | [] => True
  | .high :: _ => P w*(L w+1)+2*(Q w*T) ≤ 2*(P w*T)+2*K w
  | .far :: _ => 6*(P w*T)+4*K w ≤ 4*(Q w*T)+P w*(3*L w+2)

def allGuards : List InverseLetter → Nat → Prop
  | [], _ => True
  | z::w, T => guardAt (z::w) T ∧ allGuards w T

private theorem high_guard_iff {p q l k a d T : Nat} (hp : 0<p)
    (hx : a+d+5+l=2*T) (hv : q*T=p*(d+3)+k) :
    (d+2≤a ↔ p*(l+1)+2*(q*T)≤2*(p*T)+2*k) := by
  have he : d+2≤a ↔ 2*d+l+7≤2*T := by omega
  have hv' : q*T=p*d+3*p+k := by
    rw [Nat.mul_add,Nat.mul_comm p 3] at hv
    exact hv
  rw [he]
  have e1 : p*(2*d)=2*(p*d) := by ac_rfl
  have e2 : p*(2*T)=2*(p*T) := by ac_rfl
  constructor
  · intro h
    have hmul := Nat.mul_le_mul_left p h
    simp only [Nat.mul_add,Nat.mul_one,e1,e2,Nat.mul_comm p 7] at hmul ⊢
    omega
  · intro h
    apply Nat.le_of_mul_le_mul_left _ hp
    simp only [Nat.mul_add,Nat.mul_one,e1,e2,Nat.mul_comm p 7] at h ⊢
    omega

private theorem far_guard_iff {p q l k a d T : Nat} (hp : 0<p)
    (hx : a+d+5+l=2*T) (hv : q*T=p*(d+3)+k) :
    (3*a+1≤d ↔ 6*(p*T)+4*k≤4*(q*T)+p*(3*l+2)) := by
  have he : 3*a+1≤d ↔ 6*T≤4*d+3*l+14 := by omega
  have hv' : q*T=p*d+3*p+k := by
    rw [Nat.mul_add,Nat.mul_comm p 3] at hv
    exact hv
  rw [he]
  have e1 : p*(6*T)=6*(p*T) := by ac_rfl
  have e2 : p*(4*d)=4*(p*d) := by ac_rfl
  have e3 : p*(3*l)=3*(p*l) := by ac_rfl
  constructor
  · intro h
    have hmul := Nat.mul_le_mul_left p h
    simp only [Nat.mul_add,e1,e2,e3,Nat.mul_comm p 14,Nat.mul_comm p 2] at hmul ⊢
    omega
  · intro h
    apply Nat.le_of_mul_le_mul_left _ hp
    simp only [Nat.mul_add,e1,e2,e3,Nat.mul_comm p 14,Nat.mul_comm p 2] at h ⊢
    omega

/-- Transport the two certificate equations exactly one High step. -/
private theorem high_tail {w a d t} (hg : d+2≤a)
    (hx : a+d+5+L (.high::w)=2*(t+3))
    (hv : Q (.high::w)*(t+3)=P (.high::w)*(d+3)+K (.high::w)) :
    (a-d-2)+(2*d+3)+5+L w=2*(t+3) ∧
    Q w*(t+3)=P w*(2*d+3+3)+K w := by
  simp only [L_high] at hx
  simp only [Q_high,P_high,K_high] at hv
  refine ⟨by omega,?_⟩
  rw [show 2*d+3+3=2*(d+3) by omega,show P w*(2*(d+3))=(2*P w)*(d+3) by ac_rfl]
  exact hv

/-- Transport the certificate exactly one Far step. -/
private theorem far_tail {w a d t} (hg : 3*a+1≤d)
    (hx : a+d+5+L (.far::w)=2*(t+3))
    (hv : Q (.far::w)*(t+3)=P (.far::w)*(d+3)+K (.far::w)) :
    (4*a+6)+(d-3*a)+5+L w=2*(t+3) ∧
    Q w*(t+3)=P w*(d-3*a+3)+K w := by
  simp only [L_far] at hx
  simp only [Q_far,P_far,K_far] at hv
  have he : Q w*(t+3)+P w*(3*a)=P w*(d+3)+K w :=
    (far_cert hx).mp (by simpa [Nat.add_assoc] using hv)
  have hd := congrArg (fun x : Nat => P w*x) (show d-3*a+3+3*a=d+3 by omega)
  rw [Nat.mul_add] at hd
  exact ⟨by omega,by omega⟩

/-- Exact, cutoff-free guard criterion. Once the two endpoint equations hold,
    the whole word exists precisely when its linear terminal-scale guards hold. -/
theorem word_run_iff_guards {w : List InverseLetter} {a d t : Nat}
    (hx : a+d+5+L w=2*(t+3)) (hv : Q w*(t+3)=P w*(d+3)+K w) :
    WordRun w a d (t+1) t ↔ allGuards w (t+3) := by
  induction w generalizing a d with
  | nil =>
      simp at hx hv
      have ha : a=t+1 := by omega
      have hd : d=t := by omega
      subst a; subst d
      exact ⟨fun _ => trivial, fun _ => WordRun.nil _ _⟩
  | cons z w ih =>
      cases z with
      | high =>
          have he := high_guard_iff (P_pos (.high::w)) hx hv
          change WordRun (.high::w) a d (t+1) t ↔
            guardAt (.high::w) (t+3) ∧ allGuards w (t+3)
          constructor
          · intro h
            cases h with
            | high hg ht =>
                have htail := high_tail hg hx hv
                exact ⟨he.mp hg,(ih htail.1 htail.2).mp ht⟩
          · rintro ⟨hg,ht⟩
            have hg' := he.mpr hg
            have htail := high_tail hg' hx hv
            exact WordRun.high hg' ((ih htail.1 htail.2).mpr ht)
      | far =>
          have he := far_guard_iff (P_pos (.far::w)) hx hv
          change WordRun (.far::w) a d (t+1) t ↔
            guardAt (.far::w) (t+3) ∧ allGuards w (t+3)
          constructor
          · intro h
            cases h with
            | far hg1 hg2 ht =>
                have htail := far_tail hg2 hx hv
                exact ⟨he.mp hg2,(ih htail.1 htail.2).mp ht⟩
          · rintro ⟨hg,ht⟩
            have hg' := he.mpr hg
            have htail := far_tail hg' hx hv
            exact WordRun.far (by omega) hg' ((ih htail.1 htail.2).mpr ht)

/-- An individual affine guard is exactly a nonnegative lower bound on T.
    This version avoids division and rounding issues. -/
def guardSlope (w : List InverseLetter) : Nat :=
  match w with
  | [] => 1
  | .high::u => 2*(P (.high::u)-Q (.high::u))
  | .far::u => 4*Q (.far::u)-6*P (.far::u)

def guardDemand (w : List InverseLetter) : Nat :=
  match w with
  | [] => 0
  | .high::u => P (.high::u)*(L (.high::u)+1)-2*K (.high::u)
  | .far::u => 4*K (.far::u)-P (.far::u)*(3*L (.far::u)+2)

theorem guardSlope_pos (w : List InverseLetter) : 0<guardSlope w := by
  cases w with
  | nil => decide
  | cons z w =>
      cases z with
      | high =>
          have h := Q_upper w
          simp only [guardSlope,P_high,Q_high]
          omega
      | far =>
          have h := Q_pos w
          simp only [guardSlope,P_far,Q_far]
          omega

theorem guardAt_iff_slope (w : List InverseLetter) (T : Nat) :
    guardAt w T ↔ guardDemand w≤guardSlope w*T := by
  cases w with
  | nil => simp [guardAt,guardDemand,guardSlope]
  | cons z w =>
      cases z with
      | high =>
          have h := Q_upper w
          simp only [guardAt,guardDemand,guardSlope,P_high,Q_high,L_high,K_high]
          rw [Nat.mul_assoc 2 (2*P w-Q w) T,Nat.sub_mul]
          have ht : Q w*T≤2*P w*T := Nat.mul_le_mul_right T (by omega)
          omega
      | far =>
          have h := Q_pos w
          simp only [guardAt,guardDemand,guardSlope,P_far,Q_far,L_far,K_far]
          have hs : 6*(4*P w)≤4*(Q w+6*P w) := by omega
          rw [Nat.sub_mul]
          have ht := Nat.mul_le_mul_right T hs
          simp only [Nat.add_mul,Nat.mul_assoc] at ht ⊢
          omega

/-- Minimum terminal scale required by one letter's exact guard. -/
def guardMin (w : List InverseLetter) : Nat :=
  (guardDemand w+guardSlope w-1)/guardSlope w

/-- Minimum terminal scale required by every remaining letter. -/
def exactMin : List InverseLetter → Nat
  | [] => 0
  | z::w => max (guardMin (z::w)) (exactMin w)

private theorem ceil_le_iff (d s T : Nat) (hs : 0<s) :
    (d+s-1)/s≤T ↔ d≤s*T := by
  rw [←Nat.lt_succ_iff,Nat.div_lt_iff_lt_mul hs]
  rw [Nat.succ_eq_add_one,Nat.add_mul,Nat.one_mul,Nat.mul_comm T s]
  omega

theorem allGuards_iff_exactMin (w : List InverseLetter) (T : Nat) :
    allGuards w T ↔ exactMin w≤T := by
  induction w with
  | nil => simp [allGuards,exactMin]
  | cons z w ih =>
      simp only [allGuards,exactMin,Nat.max_le,ih,guardAt_iff_slope]
      unfold guardMin
      rw [ceil_le_iff _ _ _ (guardSlope_pos _)]

/-- The full arbitrary-word terminal criterion, with an exact lower bound. -/
theorem word_terminal_iff_exactMin (w : List InverseLetter) (a d t : Nat) :
    WordRun w a d (t+1) t ↔
    a+d+5+L w=2*(t+3) ∧ Q w*(t+3)=P w*(d+3)+K w ∧ exactMin w≤t+3 := by
  constructor
  · intro h
    have he := word_terminal_equations h
    exact ⟨he.1,he.2,(allGuards_iff_exactMin _ _).mp ((word_run_iff_guards he.1 he.2).mp h)⟩
  · rintro ⟨hx,hv,hm⟩
    exact (word_run_iff_guards hx hv).mpr ((allGuards_iff_exactMin _ _).mpr hm)

/-- Exact characterization even below the earlier sufficient scale threshold:
    the fixed word minimum and the nonnegativity of the post-High first counter
    are the only extra constraints beyond the two endpoint equations. -/
theorem prefix_tail_iff_exactMin (h : Nat) (w : List InverseLetter) (R c t : Nat) :
    PrefixTail h w R c t ↔
    R+c+h+5+L w=2*(t+3) ∧ Q w*(t+3)=P w*(2^h*(c+3))+K w ∧
    exactMin w≤t+3 ∧ 2^h*(c+3)+L w+2≤2*(t+3) := by
  constructor
  · intro hr
    have he := prefix_tail_equations hr
    rcases hr with ⟨a,d,hh,hw⟩
    have hc := high_run_coordinates hh
    unfold X Y at hc
    have hm : 2^h*(2*(c+3))=2*(2^h*(c+3)) := by ac_rfl
    rw [hm] at hc
    have ht := (word_terminal_iff_exactMin w a d t).mp hw
    exact ⟨he.1,he.2,ht.2.2,by omega⟩
  · rintro ⟨hx,hv,hm,ha⟩
    let v := 2^h*(c+3)
    have hv3 : 3≤v := by
      have hp := Nat.one_le_pow h 2 (by decide)
      have hh := Nat.mul_le_mul_right (c+3) hp
      dsimp [v]
      omega
    let a := 2*(t+3)-L w-v-2
    let d := v-3
    have ha' : a+d+5+L w=2*(t+3) := by dsimp [a,d]; omega
    have hd : d+3=v := by dsimp [d]; omega
    refine ⟨a,d,?_,?_⟩
    · apply highRun_of_balances
      · omega
      · exact hd
    · exact (word_terminal_iff_exactMin w a d t).mpr ⟨ha',by rw [hd]; exact hv,hm⟩

#print axioms word_run_iff_guards
#print axioms word_terminal_iff_exactMin
#print axioms prefix_tail_iff_exactMin
end BB6.Agent2F321ExactThreshold
