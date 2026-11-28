import LastFarExact
import TerminalWordCandidate
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321WordGuard
open BB6.Agent31F321Density
open BB6.Agent2F321Bulk
open BB6.Agent2F321Diagonal
open BB6.Agent2F321LastFarExact

/-- Parameters of the existing inverse-word compiler, expressed in shifted
    second-counter coordinates. -/
def P (w : List InverseLetter) : Nat := 2^(compile w).shift
def L (w : List InverseLetter) : Nat := (compile w).sumDecrease
def Q (w : List InverseLetter) : Nat := terminalDenom w

def K : List InverseLetter → Nat
  | [] => 0
  | .high::w => K w
  | .far::w => K w+(3*L w+24)*P w

/-- A sufficient terminal scale making every individual word guard automatic. -/
def threshold (w : List InverseLetter) : Nat := (L w+4)*P w+K w

@[simp] theorem P_nil : P [] = 1 := rfl
@[simp] theorem L_nil : L [] = 0 := rfl
@[simp] theorem Q_nil : Q [] = 1 := rfl
@[simp] theorem K_nil : K [] = 0 := rfl
@[simp] theorem P_high (w : List InverseLetter) : P (.high::w) = 2*P w := by
  simp [P,compile,advance,Nat.pow_succ,Nat.mul_comm]
@[simp] theorem P_far (w : List InverseLetter) : P (.far::w) = 4*P w := by
  simp [P,compile,advance,Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] <;> omega
@[simp] theorem L_high (w : List InverseLetter) : L (.high::w) = L w+1 := rfl
@[simp] theorem L_far (w : List InverseLetter) : L (.far::w) = L w+6 := rfl
@[simp] theorem Q_high (w : List InverseLetter) : Q (.high::w) = Q w := rfl
@[simp] theorem Q_far (w : List InverseLetter) : Q (.far::w) = Q w+6*P w := by
  simp [Q,terminalDenom,P,Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] <;> omega
@[simp] theorem K_high (w : List InverseLetter) : K (.high::w) = K w := rfl
@[simp] theorem K_far (w : List InverseLetter) : K (.far::w) = K w+(3*L w+24)*P w := rfl

theorem P_pos (w : List InverseLetter) : 0<P w := Nat.pow_pos (by decide)
theorem Q_pos (w : List InverseLetter) : 0<Q w := terminalDenom_pos w
theorem Q_upper (w : List InverseLetter) : Q w+1≤2*P w := by
  have h := terminalDenom_identity w
  have hu := compiled_numerator_odd w
  rw [Nat.pow_succ] at h
  unfold P Q
  omega

theorem threshold_tail (z : InverseLetter) (w : List InverseLetter) : threshold w≤threshold (z::w) := by
  cases z with
  | high =>
      simp only [threshold,P_high,L_high,K_high]
      have h1 : L w+4≤L w+1+4 := by omega
      have h2 : P w≤2*P w := by omega
      have h := Nat.mul_le_mul h1 h2
      omega
  | far =>
      simp only [threshold,P_far,L_far,K_far]
      have h1 : L w+4≤L w+6+4 := by omega
      have h2 : P w≤4*P w := by omega
      have h := Nat.mul_le_mul h1 h2
      omega

/-- Exact source-faithful chronological H/F word, with every guard retained. -/
inductive WordRun : List InverseLetter → Nat → Nat → Nat → Nat → Prop where
  | nil (a d : Nat) : WordRun [] a d a d
  | high {w : List InverseLetter} {a d A D : Nat} (hg : d+2≤a)
      (tail : WordRun w (a-d-2) (2*d+3) A D) : WordRun (.high::w) a d A D
  | far {w : List InverseLetter} {a d A D : Nat} (h1 : a<d) (h2 : 3*a+1≤d)
      (tail : WordRun w (4*a+6) (d-3*a) A D) : WordRun (.far::w) a d A D

theorem far_cert {p q k l a d T : Nat}
    (hx : a+d+5+(l+6)=2*T) :
    (q+6*p)*T=(4*p)*(d+3)+k+(3*l+24)*p ↔
      q*T+p*(3*a)=p*(d+3)+k := by
  have hs := congrArg (fun x : Nat => p*x) hx
  have hP2 : p*(2*T)=2*(p*T) := by ac_rfl
  have hpa : p*(3*a)=3*(p*a) := by ac_rfl
  have hpd : (4*p)*(d+3)=4*(p*d)+12*p := by
    rw [Nat.mul_add, Nat.mul_assoc]
    have hh : (4*p)*3=12*p := by omega
    rw [hh]
  have hQL : (q+6*p)*T=q*T+6*(p*T) := by rw [Nat.add_mul,Nat.mul_assoc]
  have hK : (3*l+24)*p=3*(p*l)+24*p := by
    rw [Nat.add_mul,Nat.mul_assoc,Nat.mul_comm l p]
  simp only [Nat.mul_add,hP2] at hs
  rw [Nat.mul_comm p 5,Nat.mul_comm p 6] at hs
  rw [hQL,hpd,hK,hpa,Nat.mul_add,Nat.mul_comm p 3]
  omega

/-- Necessity of the nonnegative shifted-coordinate certificate, for every
    genuine guarded word, without a scale threshold. -/
theorem word_terminal_equations {w a d t} (hr : WordRun w a d (t+1) t) :
    a+d+5+L w=2*(t+3) ∧ Q w*(t+3)=P w*(d+3)+K w := by
  induction w generalizing a d with
  | nil =>
      cases hr
      simp
      omega
  | cons z w ih =>
      cases hr with
      | high hg tail =>
          have ht := ih tail
          simp only [L_high,Q_high,P_high,K_high]
          constructor
          · omega
          · rw [ht.2]
            have he : P w*(2*d+3+3)=(2*P w)*(d+3) := by
              rw [show 2*d+3+3=2*(d+3) by omega]
              ac_rfl
            rw [he]
      | far h1 h2 tail =>
          have ht := ih tail
          simp only [L_far,Q_far,P_far,K_far]
          have hx : a+d+5+(L w+6)=2*(t+3) := by omega
          refine ⟨hx, ?_⟩
          rw [←Nat.add_assoc]
          apply (far_cert hx).mpr
          have hd := congrArg (fun x : Nat => P w*x) (show (d-3*a+3)+3*a=d+3 by omega)
          rw [Nat.mul_add] at hd
          omega

private theorem scaled_margin {p q v T l k : Nat}
    (hp : 0<p) (hq : q+1≤p) (he : q*T=p*v+k)
    (hT : (l+4)*p+k≤T) : v+l+4≤T := by
  have hm := Nat.mul_le_mul_right T hq
  rw [Nat.add_mul,Nat.one_mul,he] at hm
  apply Nat.le_of_mul_le_mul_left (c:=p) _ hp
  simp only [Nat.mul_add]
  rw [Nat.add_mul, Nat.mul_comm _ p] at hT
  omega

private theorem scaled_double_margin {p q v T l k : Nat}
    (hp : 0<p) (hq : q+1≤2*p) (he : q*T=p*v+k)
    (hT : (l+4)*p+k≤T) : v+l+4≤2*T := by
  have hm := Nat.mul_le_mul_right T hq
  rw [Nat.add_mul,Nat.one_mul,he,Nat.mul_assoc] at hm
  have hm' : p*(v+l+4)≤p*(2*T) := by
    rw [show p*(2*T)=2*(p*T) by ac_rfl]
    simp only [Nat.mul_add]
    rw [Nat.add_mul,Nat.mul_comm l p] at hT
    omega
  exact Nat.le_of_mul_le_mul_left hm' hp

/-- Complete large-scale converse. An exact integral terminal certificate is
    sufficient to realize the whole source-faithful word once T exceeds its
    explicit threshold. This is uniform over all finite words. -/
theorem word_terminal_of_large {w : List InverseLetter} {a d t : Nat}
    (hT : threshold w≤t+3) (hx : a+d+5+L w=2*(t+3))
    (hv : Q w*(t+3)=P w*(d+3)+K w) : WordRun w a d (t+1) t := by
  induction w generalizing a d with
  | nil =>
      simp at hx hv
      have h1 : a=t+1 := by omega
      have h2 : d=t := by omega
      subst a; subst d
      exact WordRun.nil _ _
  | cons z w ih =>
      have ht : threshold w≤t+3 := Nat.le_trans (threshold_tail z w) hT
      cases z with
      | high =>
          have hq : Q (.high::w)+1≤P (.high::w) := by simpa using Q_upper w
          have hm := scaled_margin (P_pos (.high::w)) hq hv hT
          have hg : d+2≤a := by omega
          apply WordRun.high hg
          apply ih ht
          · simp only [L_high] at hx
            omega
          · simp only [Q_high,P_high,K_high] at hv
            have he : P w*(2*d+3+3)=(2*P w)*(d+3) := by
              rw [show 2*d+3+3=2*(d+3) by omega]
              ac_rfl
            rw [he]
            exact hv
      | far =>
          simp only [L_far] at hx
          simp only [Q_far,P_far,K_far] at hv
          have he : Q w*(t+3)+P w*(3*a)=P w*(d+3)+K w := (far_cert hx).mp (by simpa [Nat.add_assoc] using hv)
          have hq := Nat.mul_le_mul_right (t+3) (Q_pos w)
          have hq' : t+3≤Q w*(t+3) := by simpa using hq
          have hp4 := Nat.mul_le_mul_right (P w) (show 4≤L w+4 by omega)
          unfold threshold at ht
          have hh : P w*(3*a+4)≤P w*(d+3) := by
            rw [Nat.mul_add,Nat.mul_comm (P w) 4]
            omega
          have hg2 : 3*a+1≤d := by
            have hh' := Nat.le_of_mul_le_mul_left hh (P_pos w)
            omega
          have hg1 : a<d := by omega
          apply WordRun.far hg1 hg2
          apply ih ht
          · omega
          · have hd := congrArg (fun x : Nat => P w*x) (show d-3*a+3+3*a=d+3 by omega)
            rw [Nat.mul_add] at hd
            omega

/-- Arbitrary leading High run followed by a fixed H/F word. -/
def PrefixTail (h : Nat) (w : List InverseLetter) (R c t : Nat) : Prop :=
  ∃ a d, HighRun h R c a d ∧ WordRun w a d (t+1) t

theorem prefix_tail_equations {h w R c t} (hr : PrefixTail h w R c t) :
    R+c+h+5+L w=2*(t+3) ∧ Q w*(t+3)=P w*(2^h*(c+3))+K w := by
  rcases hr with ⟨a,d,hh,hw⟩
  have hc := high_run_coordinates hh
  unfold X Y at hc
  have hm : 2^h*(2*(c+3))=2*(2^h*(c+3)) := by ac_rfl
  rw [hm] at hc
  have hd : d+3=2^h*(c+3) := by omega
  have he := word_terminal_equations hw
  exact ⟨by omega,by rw [←hd]; exact he.2⟩

/-- Beyond an explicit threshold the exact word/anchor Diophantine equations
    are necessary AND sufficient. No intermediate branch replay is needed. -/
theorem prefix_tail_iff_of_large (h : Nat) (w : List InverseLetter) (R c t : Nat)
    (hT : threshold w≤t+3) : PrefixTail h w R c t ↔
      R+c+h+5+L w=2*(t+3) ∧ Q w*(t+3)=P w*(2^h*(c+3))+K w := by
  constructor
  · exact prefix_tail_equations
  · rintro ⟨hx,hv⟩
    let v := 2^h*(c+3)
    have hv3 : 3≤v := by
      have hp := Nat.one_le_pow h 2 (by decide)
      have hh := Nat.mul_le_mul_right (c+3) hp
      dsimp [v]
      omega
    have hm := scaled_double_margin (P_pos w) (Q_upper w) hv hT
    let a := 2*(t+3)-L w-v-2
    let d := v-3
    have ha : a+d+5+L w=2*(t+3) := by dsimp [a,d]; omega
    have hd : d+3=v := by dsimp [d]; omega
    refine ⟨a,d,?_,?_⟩
    · apply highRun_of_balances
      · omega
      · exact hd
    · exact word_terminal_of_large hT ha (by rw [hd]; exact hv)

/-- Eventually the only condition on an arbitrary leading High length is
    a divisibility test with a fixed modulus. Both quantitative hypotheses
    involve monotone exponential growth and hold for all sufficiently large h. -/
theorem prefix_exists_iff_divides (h : Nat) (w : List InverseLetter) (c : Nat)
    (hs : 2*threshold w≤2^h*(c+3))
    (ha : c+h+5+L w≤2^h*(c+3)) :
    (∃ R t, PrefixTail h w R c t) ↔ Q w ∣ P w*(2^h*(c+3))+K w := by
  constructor
  · rintro ⟨R,t,hr⟩
    exact ⟨t+3,(prefix_tail_equations hr).2.symm⟩
  · rintro ⟨T,he⟩
    have hu : 2^h*(c+3)≤2*T := by
      have hh := Nat.mul_le_mul_right T (Q_upper w)
      rw [Nat.add_mul,Nat.one_mul,←he,Nat.mul_assoc] at hh
      apply Nat.le_of_mul_le_mul_left _ (P_pos w)
      rw [show P w*(2*T)=2*(P w*T) by ac_rfl]
      omega
    have ht : threshold w≤T := by omega
    have h4 : 4≤threshold w := by
      have hp := P_pos w
      have h := Nat.mul_le_mul (show 4≤L w+4 by omega) hp
      unfold threshold
      omega
    let t := T-3
    let R := 2*T-(c+h+5+L w)
    have hT : t+3=T := by dsimp [t]; omega
    have hR : R+c+h+5+L w=2*T := by dsimp [R]; omega
    refine ⟨R,t,(prefix_tail_iff_of_large h w R c t (by rw [hT]; exact ht)).mpr ?_⟩
    exact ⟨by rw [hR,hT],by rw [hT,he]⟩

/-- Every period of powers of two modulo the fixed word denominator is a
    period of its exact candidate test. -/
theorem prefix_divides_period (w : List InverseLetter) (h c p : Nat)
    (hp : 2^p%Q w=1%Q w) :
    Q w ∣ P w*(2^(h+p)*(c+3))+K w ↔
      Q w ∣ P w*(2^h*(c+3))+K w := by
  have hm : 2^(h+p)%Q w=2^h%Q w := by
    rw [Nat.pow_add,Nat.mul_mod,hp]
    rw [←Nat.mul_mod]
    simp
  simp only [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.add_mod,Nat.add_mod (P w*(2^h*(c+3))) (K w),
    Nat.mul_mod (P w) (2^(h+p)*(c+3)),Nat.mul_mod (P w) (2^h*(c+3)),
    Nat.mul_mod (2^(h+p)) (c+3),Nat.mul_mod (2^h) (c+3),hm]

#print axioms word_terminal_equations
#print axioms word_terminal_of_large
#print axioms prefix_tail_iff_of_large
#print axioms prefix_exists_iff_divides
#print axioms prefix_divides_period
end BB6.Agent2F321WordGuard
