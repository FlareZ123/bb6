import F321BackwardBarrier

namespace BB6.Agent31F321Density

/-- Enumerate all high/far inverse words of the given length. -/
def words : Nat → List (List InverseLetter)
  | 0 => [[]]
  | n+1 => (words n).map (.high::·) ++ (words n).map (.far::·)

theorem words_complete (n:Nat) (w:List InverseLetter)
    (h:w.length=n) : w ∈ words n := by
  induction n generalizing w with
  | zero =>
      cases w with
      | nil => decide
      | cons b bs => simp at h
  | succ n ih =>
      cases w with
      | nil => simp at h
      | cons b bs =>
          have hb : bs.length=n := by simpa using h
          have hs := ih bs hb
          cases b with
          | high => simp [words,hs]
          | far => simp [words,hs]

/-- A finite, executable modular exclusion test for depth n. -/
def residuePass (n d:Nat) : Bool :=
  (words n).all (fun w => decide (
     (((compile w).u:Int)*(d:Int)+(compile w).v) %
        ((2:Int)^(compile w).shift) ≠ 0))

theorem residuePass_sound (n d:Nat) (h:residuePass n d=true) :
    NoResidueWord n d := by
  intro w hw
  have hm : w∈words n := words_complete n w hw
  have hz := (List.all_eq_true.mp h) w hm
  simpa [residuePass] using hz

/-- Every true result from the finite Boolean modular test excludes *all*
    counter-map orbits from genuine seed (1,1) to the terminal gate. -/
theorem no_halting_gate_after_decide (n d:Nat)
    (hbound:6*2^n≤d+3)
    (h:residuePass n d=true) :
    ∀ m, ¬CounterReach 1 1 m (d+1) d :=
  no_halting_gate_from_seed n d hbound (residuePass_sound n d h)

/-- A concrete original-counter-map all-time exclusion, checked solely by
    kernel reduction of the finite condition: no arbitrary orbit from the
    genuine (1,1) seed can reach terminal gate (1001,1000). -/
theorem gate1000_never : ∀ m, ¬CounterReach 1 1 m 1001 1000 := by
  exact no_halting_gate_after_decide 4 1000 (by decide) (by decide)

#print axioms no_halting_gate_after_decide
#print axioms gate1000_never
end BB6.Agent31F321Density
