import BB429ResonanceMinimal

namespace BB429.CoarseExit

def digitResidue256 (z : Int) : Prop :=
  z=0 ∨ z=1 ∨ z=4 ∨ z=5 ∨
  z=16 ∨ z=17 ∨ z=20 ∨ z=21 ∨
  z=64 ∨ z=65 ∨ z=68 ∨ z=69 ∨
  z=80 ∨ z=81 ∨ z=84 ∨ z=85

/-- Every base-four 0/1 word has one of the sixteen possible four-digit
    suffixes modulo 4^4=256. -/
theorem word4_mod256 (e : Nat → Bool) (i : Nat) :
    digitResidue256 (word4 e i % 256) := by
  induction i with
  | zero =>
      simp [word4,digitResidue256]
  | succ i ih =>
      unfold digitResidue256 at ih ⊢
      rcases ih with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
        cases he : e i <;> simp only [word4,he,Bool.false_eq_true,if_false,
          if_true] <;> omega

/-- No minimal doubled-scale d=234 resonance of length at most six exists
    except the single scale m=35. -/
theorem d234_short_resonance_only35
    (m i : Nat) (e : Nat → Bool)
    (hi : i≤6)
    (hres :
      (2496:Int)*(m:Int)+23808 =
        36+108*word4 e i) :
    m=35 := by
  have hb := word4_bound e i
  have hr := word4_mod256 e i
  unfold digitResidue256 at hr
  have hpN : 4^i≤(4096:Nat) := by
    have hpow := Nat.pow_le_pow_right (by decide : 0<4) hi
    norm_num at hpow ⊢
    exact hpow
  have hp : (4:Int)^i≤4096 := by
    exact_mod_cast hpN
  rcases hr with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> omega

/-- The unique short second resonance is itself a finite safe source
    witness.  This theorem is intentionally concrete: it removes the only
    sub-seven-digit exception from the recursive resonance stripping. -/
theorem d234_m35 :
    run 559 (prepared 35 234) =
      some (0,100353353393387804136910732226917626776914176) := by
  native_decide

#print axioms word4_mod256
#print axioms d234_short_resonance_only35
#print axioms d234_m35

end BB429.CoarseExit
