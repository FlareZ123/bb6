import OddResetMacro
import Q0MacroCheck

namespace BB429Q0Macro
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Affine rays with arbitrary nonnegative coefficients. -/
structure Ray where
  m0 : Nat
  dm : Nat
  p0 : Nat
  dp : Nat
  y0 : Nat
  dy : Nat

def Ray.m (R : Ray) (t : Nat) := R.m0+R.dm*t
def Ray.p (R : Ray) (t : Nat) := R.p0+R.dp*t
def Ray.y (R : Ray) (t : Nat) := R.y0+R.dy*t

def rayFF : Ray := ⟨13,16,53,48,3,3⟩
def rayFE : Ray := ⟨8,16,36,48,11,15⟩

def rayCut (R : Ray) (e r : Nat) : Bool :=
  dead (min e (R.m r)) (R.p r) (R.y r)

theorem rayCut_sound (R : Ray) (e r t : Nat)
    (hr : r<16^e) (ht : t%16^e=r) (hc : rayCut R e r=true) :
    ¬ Path (R.m t) (R.p t) (R.y t) := by
  intro hp
  have hrt : r≤t := by rw [←ht]; exact Nat.mod_le _ _
  let k := min e (R.m r)
  have hmono : R.m r≤R.m t := by
    unfold Ray.m
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hrt) _
  have hk : k≤R.m t := Nat.le_trans (Nat.min_le_right _ _) hmono
  have he : k≤e := Nat.min_le_left _ _
  have heq : e=k+(e-k) := by omega
  have hpow : 16^e=16^k*16^(e-k) := by
    calc
      16^e = 16^(k+(e-k)) := congrArg (16^·) heq
      _ = _ := Nat.pow_add _ _ _
  have hs : t=r+16^e*(t/16^e) := by
    have h := Nat.mod_add_div t (16^e)
    omega
  let v := 16^(e-k)*(t/16^e)
  have htv : t=r+16^k*v := by
    dsimp [v]
    rw [←Nat.mul_assoc,←hpow]
    exact hs
  have hpv : R.p t=R.p r+16^k*(R.dp*v) := by
    unfold Ray.p
    rw [htv,Nat.mul_add]
    ac_rfl
  have hyv : R.y t=R.y r+16^k*(R.dy*v) := by
    unfold Ray.y
    rw [htv,Nat.mul_add]
    ac_rfl
  have htake := path_take hp k hk
  rw [hpv,hyv] at htake
  exact dead_sound hc (path_lower k _ _ _ _ htake)

/-- Base-16 cylinder tree with safe early cutoff. -/
def rayCover (R : Ray) : Nat → Nat → Nat → Nat → Bool
  | 0,e,r,N => (N≤r) || rayCut R e r
  | f+1,e,r,N => (N≤r) || rayCut R e r ||
      (List.range 16).all (fun d => rayCover R f (e+1) (r+16^e*d) N)

theorem rayCover_sound (R : Ray) (f e r N t : Nat)
    (hr : r<16^e) (ht : t%16^e=r) (hN : t<N)
    (hc : rayCover R f e r N=true) : ¬ Path (R.m t) (R.p t) (R.y t) := by
  have hrt : r≤t := by rw [←ht]; exact Nat.mod_le _ _
  induction f generalizing e r with
  | zero =>
    simp [rayCover,show ¬N≤r by omega] at hc
    exact rayCut_sound R e r t hr ht hc
  | succ f ih =>
    simp [rayCover,show ¬N≤r by omega] at hc
    rcases hc with hcut|hchildren
    · exact rayCut_sound R e r t hr ht hcut
    · let s := t%16^(e+1)
      let d := s/16^e
      have hpow : 16^(e+1)=16^e*16 := Nat.pow_succ _ _
      have hmod : s%16^e=r := by
        dsimp [s]
        rw [Nat.mod_mod_of_dvd t (by rw [hpow]; exact ⟨16,rfl⟩),ht]
      have hs : s<16^(e+1) := Nat.mod_lt _ (Nat.pow_pos (by decide))
      have hlt : d<16 := by
        dsimp [d]
        apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr
        rw [Nat.mul_comm]
        omega
      have hsd : s=r+16^e*d := by
        have h := Nat.mod_add_div s (16^e)
        dsimp [d]
        omega
      have hchild := hchildren d hlt
      apply ih (e+1) (r+16^e*d)
      · omega
      · exact hsd
      · exact hchild
      · rw [←hsd]; exact Nat.mod_le _ _

-- The small-rank interval connects to the first reusable rank barrier.
theorem rayFF_small_cert : rayCover rayFF 20 0 0 43750=true := by decide

theorem rayFE_small_cert : rayCover rayFE 20 0 0 43750=true := by decide

theorem rayFF_small (t : Nat) (ht : t<43750) :
    ¬ Path (13+16*t) (53+48*t) (3+3*t) := by
  exact rayCover_sound rayFF 20 0 0 43750 t (by decide) (by omega) ht rayFF_small_cert

theorem rayFE_small (t : Nat) (ht : t<43750) :
    ¬ Path (8+16*t) (36+48*t) (11+15*t) := by
  exact rayCover_sound rayFE 20 0 0 43750 t (by decide) (by omega) ht rayFE_small_cert

#print axioms rayCut_sound
#print axioms rayCover_sound
#print axioms rayFF_small
#print axioms rayFE_small
end BB429Q0Macro
