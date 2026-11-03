import Root119Gate

set_option linter.unusedSimpArgs false

namespace BB6Root119

/-- Execute n successful primitive actions, failing on an undefined transition. -/
def shuttleRun : Nat → Conf → Option Conf
  | 0, c => some c
  | n+1, c => (next c).bind (shuttleRun n)

theorem shuttleRun_add (a b : Nat) (c : Conf) :
    shuttleRun (a+b) c = (shuttleRun a c).bind (shuttleRun b) := by
  induction a generalizing c with
  | zero => simp [shuttleRun]
  | succ a ih =>
    simp only [Nat.succ_add, shuttleRun]
    cases h : next c with
    | none => simp [h]
    | some d => simp [h, ih]

/-- Fill n consecutive cells with ones, preserving every other cell. -/
def shuttleFill (t : Int → Bool) (h : Int) (n : Nat) : Int → Bool :=
  fun x => if h ≤ x ∧ x < h+(n:Int) then true else t x

theorem shuttleFill_outside (t : Int → Bool) (h x : Int) (n : Nat)
    (hx : x < h ∨ h+(n:Int) ≤ x) : shuttleFill t h n x = t x := by
  have hf : ¬ (h ≤ x ∧ x < h+(n:Int)) := by omega
  simp [shuttleFill, hf]

theorem shuttleFill_two (t : Int → Bool) (h : Int) :
    setBit (setBit t h true) (h+1) true = shuttleFill t h 2 := by
  funext x
  by_cases h0 : x = h
  · have hi : h ≤ x ∧ x < h+(2:Nat) := by omega
    simp [shuttleFill,setBit,h0,hi] <;> omega
  by_cases h1 : x = h+1
  · have hi : h ≤ x ∧ x < h+(2:Nat) := by omega
    simp [shuttleFill,setBit,h0,h1,hi] <;> omega
  · have ho : ¬(h ≤ x ∧ x < h+(2:Nat)) := by omega
    simp [shuttleFill,setBit,h0,h1,ho] <;> omega

theorem shuttleFill_shift (t : Int → Bool) (h : Int) (n : Nat) :
    setBit (setBit (shuttleFill (setBit (setBit t h true) (h+1) false) (h+2) (2*n+2))
      (h+1) true) h true = shuttleFill t h (2*(n+1)+2) := by
  funext x
  have hend : h+2+((2*n+2:Nat):Int) = h+((2*(n+1)+2:Nat):Int) := by omega
  by_cases h0 : x = h
  · have hi : h ≤ x ∧ x < h+((2*(n+1)+2:Nat):Int) := by omega
    simp [setBit,shuttleFill,h0,hi] <;> omega
  by_cases h1 : x = h+1
  · have hi : h ≤ x ∧ x < h+((2*(n+1)+2:Nat):Int) := by omega
    simp [setBit,shuttleFill,h0,h1,hi] <;> omega
  have ho : (setBit (setBit t h true) (h+1) false) x = t x := by
    simp [setBit,h0,h1]
  have hequiv : (h+2 ≤ x ∧ x < h+2+((2*n+2:Nat):Int)) ↔
                 (h ≤ x ∧ x < h+((2*(n+1)+2:Nat):Int)) := by
    constructor <;> intro hh <;> omega
  calc
    (setBit (setBit (shuttleFill (setBit (setBit t h true) (h+1) false) (h+2) (2*n+2))
      (h+1) true) h true) x =
        (shuttleFill (setBit (setBit t h true) (h+1) false) (h+2) (2*n+2)) x := by
           simp [setBit,h0,h1]
    _ = (if h+2 ≤ x ∧ x < h+2+((2*n+2:Nat):Int) then true else t x) := by
      simp [shuttleFill,ho]
    _ = shuttleFill t h (2*(n+1)+2) x := by
      simp only [shuttleFill]
      by_cases hp : h+2 ≤ x ∧ x < h+2+((2*n+2:Nat):Int)
      · have hq : h ≤ x ∧ x < h+((2*(n+1)+2:Nat):Int) := hequiv.mp hp
        simp only [if_pos hp, if_pos hq]
      · have hq : ¬ (h ≤ x ∧ x < h+((2*(n+1)+2:Nat):Int)) :=
          fun hh => hp (hequiv.mpr hh)
        simp only [if_neg hp, if_neg hq]

theorem shuttleSetBit_same (t : Int → Bool) (h : Int) (b : Bool)
    (hb : t h = b) : setBit t h b = t := by
  funext x
  by_cases heq : x = h
  · subst x; simp [setBit,hb]
  · simp [setBit,heq]

end BB6Root119
