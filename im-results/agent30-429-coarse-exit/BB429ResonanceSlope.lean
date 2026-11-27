import BB429Resonance

namespace BB429.CoarseExit
namespace Resonance

/-- Sensitivity of the transformed U-coordinate to the outer low-cycle
    counter j.  The initial low-order errors have j-slopes (48,72);
    a two-step ordinary block leaves the V-slope fixed at 72 and updates
    the U-slope by A -> 4A-144 when the non-F branch is taken. -/
def jSlope (e : Nat → Bool) : Nat → Int
  | 0 => 48
  | i+1 => 4*jSlope e i-(if e i then 144 else 0)

theorem jSlope_word4 (e : Nat → Bool) (i : Nat) :
    jSlope e i = 48*(4:Int)^i-144*word4 e i := by
  induction i with
  | zero => simp [jSlope,word4]
  | succ i ih =>
    simp only [jSlope,word4,ih,Int.pow_succ]
    cases h : e i <;> simp [h] <;> grind +ring

/-- At a first-burst Cantor resonance, the j-slope after the final forced
    true/false block pair collapses to a universal expression depending
    only on d.  The complete dependence on the preceding 0/1 word cancels:

      3 * A_post = 32 d,

    where A_post = 16*A_(2s)-576.

    Thus every resonant post-state has transformed first coordinate affine
    in j with slope 32d/3, independent of the resonant word itself. -/
theorem resonant_post_jSlope (s : Nat) (d : Int) (e : Nat → Bool)
    (hres : d=18+216*word4 (fun k => !e k) (2*s)) :
    3*(16*jSlope e (2*s)-576)=32*d := by
  have hw := word4_complement e (2*s)
  have hp : (4:Int)^(2*s)=(16:Int)^s := by
    rw [Int.pow_mul]
    change (16:Int)^s=(16:Int)^s
    rfl
  rw [hp] at hw
  rw [jSlope_word4,hp]
  omega

/-- In particular every first-burst resonance has d divisible by 6, so the
    integer slope 32d/3 is automatically well-defined. -/
theorem resonant_d_mod6 (s : Nat) (d : Int) (e : Nat → Bool)
    (hres : d=18+216*word4 (fun k => !e k) (2*s)) : d%6=0 := by
  omega

/-- The first nonzero resonance d=234 therefore has universal transformed
    U-slope 2496 with respect to j. -/
theorem d234_post_jSlope (e : Nat → Bool)
    (hres : (234:Int)=18+216*word4 (fun k => !e k) 4) :
    16*jSlope e 4-576=2496 := by
  have h := resonant_post_jSlope 2 234 e (by simpa using hres)
  omega

#print axioms jSlope_word4
#print axioms resonant_post_jSlope
#print axioms resonant_d_mod6
#print axioms d234_post_jSlope

end Resonance
end BB429.CoarseExit
