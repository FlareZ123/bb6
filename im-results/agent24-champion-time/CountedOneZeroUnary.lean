import CountedOddBase
import CountedOddUnary
import CountedSweep
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48Champion

/-- Every source-exact finite trace in a checked finite region lifts to all
physical tapes matching the fixed local input. -/
theorem even_finite_heads (m : Machine) (inside : Int → Bool) (f : FConfig) (n : Nat)
    (hcheck : (List.range n).all (fun k =>
      match fRun m k f with
      | none => true
      | some z => inside z.head) = true) :
    ∀ k, k<n → ∀ d, run m k (embed f) = some d → inside d.head = true := by
  intro k hk d hd
  have hitem := List.all_eq_true.mp hcheck k (List.mem_range.mpr hk)
  have hsource := finite_run_source m k f
  cases hrun : fRun m k f with
  | none =>
      simp only [hrun, Option.map_none] at hsource
      rw [← hsource] at hd
      cases hd
  | some z =>
      simp only [hrun, Option.map_some] at hsource
      have hd' := Option.some.inj (hsource.trans hd)
      subst d
      simpa [hrun, embed] using hitem

def even_prefBase : FConfig := ⟨3,0,[-5,-2,-1,0,2,3,4]⟩
def even_prefFinal : FConfig := ⟨4,7,[6,4,3,2,1,-2,-3,-4,-5]⟩
def even_prefArea (x : Int) : Bool := decide (-5 ≤ x ∧ x ≤ 6)

theorem even_prefix15 (bg : Int → Bool) :
    run tm2 27 (frame even_prefArea bg (embed even_prefBase)) =
      some (frame even_prefArea bg (embed even_prefFinal)) := by
  have he : fRun tm2 27 even_prefBase = some even_prefFinal := by decide
  have hc : (List.range 27).all (fun k =>
      match fRun tm2 k even_prefBase with
      | none => true
      | some z => even_prefArea z.head) = true := by decide
  rw [run_frame tm2 even_prefArea bg (embed even_prefBase) 27
    (even_finite_heads tm2 even_prefArea even_prefBase 27 hc)]
  rw [← finite_run_source tm2 27 even_prefBase, he]
  rfl

def even_tailBase : FConfig := ⟨3,5,[1,2,3,4]⟩
def even_tailFinal : FConfig := ⟨3,0,[2,3,4]⟩
def even_tailArea (x : Int) : Bool := decide (1 ≤ x ∧ x ≤ 6)

theorem even_tail11 (bg : Int → Bool) :
    run tm2 11 (frame even_tailArea bg (embed even_tailBase)) =
      some (frame even_tailArea bg (embed even_tailFinal)) := by
  have he : fRun tm2 11 even_tailBase = some even_tailFinal := by decide
  have hc : (List.range 11).all (fun k =>
      match fRun tm2 k even_tailBase with
      | none => true
      | some z => even_tailArea z.head) = true := by decide
  rw [run_frame tm2 even_tailArea bg (embed even_tailBase) 11
    (even_finite_heads tm2 even_tailArea even_tailBase 11 hc)]
  rw [← finite_run_source tm2 11 even_tailBase, he]
  rfl

/-- Exact closed-form effect of sweeping the moving zero leftwards across a
block of n+1 ones. The source theorem counted_left_sweep supplies its 3(n+1) cost. -/
theorem even_swept_closed (n : Nat) (T : Int → Bool) (h : Int)
    (hon : leftOnes T h (n+1)) (hr : T (h+1) = false) :
    sweptLeft (n+1) T h =
      (fun x => if x = h-(n:Int) then false else if x = h+1 then true else T x) := by
  induction n generalizing T h with
  | zero =>
    funext x
    simp only [sweptLeft, holeThree]
    by_cases hx0 : x=h <;> by_cases hx1 : x=h+1 <;>
      simp [hx0,hx1] <;> omega
  | succ n ih =>
    have hon' : leftOnes (holeThree T h) (h-1) (n+1) :=
      leftOnes_tail T h (n+1) hon
    have hr' : holeThree T h ((h-1)+1) = false := by
      have hh : h≠h+1 := by omega
      simp [holeThree, hh, show (h-1)+1=h by omega]
    have hh : T h = true := by simpa using hon 0 (by omega)
    change sweptLeft (n+1) (holeThree T h) (h-1) = _
    rw [ih (holeThree T h) (h-1) hon' hr']
    funext x
    have heq : h-1-(n:Int) = h-((n+1:Int)) := by omega
    by_cases hxa : x=h-((n+1:Int)) <;>
      by_cases hxb : x=h+1 <;>
      by_cases hxc : x=h <;>
      simp [holeThree, heq,hxa,hxb,hxc,hh] <;> omega

#print axioms even_prefix15
#print axioms even_tail11
#print axioms even_swept_closed

end BB6Coverage.Agent48Champion

namespace BB6Coverage.Agent48Champion

/-- The next zero cell after c+1 blocks of three unary marks. -/
def even_rightStop (c : Nat) : Int := 10 + 3*(c:Int)
def even_prefixTape (T : Int → Bool) : Int → Bool :=
  (frame even_prefArea T (embed even_prefFinal)).tape
def even_middleTape (c : Nat) (T : Int → Bool) : Int → Bool :=
  afterEZero (even_prefixTape T) (even_rightStop c)
def even_finalSweepTape (c : Nat) (T : Int → Bool) : Int → Bool :=
  sweptLeft (5+3*c) (even_middleTape c T) (even_rightStop c)

theorem even_prefixTape_external (T : Int → Bool) (x : Int) (hx : x > 6) :
    even_prefixTape T x = T x := by
  have harea : even_prefArea x = false := by
    simp [even_prefArea]; omega
  simp [even_prefixTape,frame,harea]

theorem even_prefixTape_local (T : Int → Bool) (x : Int)
    (hx : -5 ≤ x) (hy : x ≤ 6) :
    even_prefixTape T x = decide (x ∈ even_prefFinal.marked) := by
  have harea : even_prefArea x = true := by
    simp [even_prefArea]; omega
  simp [even_prefixTape,frame,harea,embed]

theorem even_prefixTape_start (T : Int → Bool) (c : Nat)
    (hone : ∀ i : Nat, i<3*(c+1) → T (7+(i:Int))=true) :
    linearRightOnes (even_prefixTape T) 7 (3*(c+1)) := by
  intro i hi
  rw [even_prefixTape_external T (7+(i:Int)) (by omega)]
  exact hone i hi

theorem even_prefixTape_stop (T : Int → Bool) (c : Nat)
    (h0 : T (even_rightStop c) = false)
    (h1 : T (even_rightStop c+1) = false)
    (h2 : T (even_rightStop c+2) = false) :
    even_prefixTape T (even_rightStop c) = false ∧
    even_prefixTape T (even_rightStop c+1) = false ∧
    even_prefixTape T (even_rightStop c+2) = false := by
  constructor
  · rw [even_prefixTape_external _ _ (by unfold even_rightStop; omega)]
    exact h0
  constructor
  · rw [even_prefixTape_external _ _ (by unfold even_rightStop; omega)]
    exact h1
  · rw [even_prefixTape_external _ _ (by unfold even_rightStop; omega)]
    exact h2

theorem even_middle_ones (T : Int → Bool) (c : Nat)
    (hone : ∀ i : Nat, i<3*(c+1) → T (7+(i:Int))=true) :
    leftOnes (even_middleTape c T) (even_rightStop c) (5+3*c) := by
  intro i hi
  have hright : even_rightStop c - (i:Int) ≤ even_rightStop c := by omega
  have hleft : 6 ≤ even_rightStop c - (i:Int) := by unfold even_rightStop; omega
  by_cases hi0 : i=0
  · subst i
    simp [even_middleTape,afterEZero]
  · have hdiff : even_rightStop c - (i:Int) ≠ even_rightStop c := by omega
    have hdiff1 : even_rightStop c - (i:Int) ≠ even_rightStop c+1 := by omega
    have hdiff2 : even_rightStop c - (i:Int) ≠ even_rightStop c+2 := by omega
    simp only [even_middleTape,afterEZero,if_neg hdiff,if_neg hdiff1,if_neg hdiff2]
    by_cases h6 : even_rightStop c - (i:Int) = 6
    · rw [h6, even_prefixTape_local T 6 (by omega) (by omega)]
      decide
    · have hxgt : 7 ≤ even_rightStop c - (i:Int) := by omega
      have hk : ∃ k : Nat, even_rightStop c - (i:Int) = 7+(k:Int) ∧ k<3*(c+1) := by
        refine ⟨(even_rightStop c - (i:Int) - 7).toNat, ?_, ?_⟩
        · have hnonneg : 0 ≤ even_rightStop c - (i:Int) - 7 := by omega
          have hcast : (((even_rightStop c - (i:Int) - 7).toNat):Int) =
            even_rightStop c - (i:Int) - 7 := Int.toNat_of_nonneg hnonneg
          omega
        · have hcast : (((even_rightStop c - (i:Int) - 7).toNat):Int) =
            even_rightStop c - (i:Int) - 7 := Int.toNat_of_nonneg (by omega)
          unfold even_rightStop at *
          omega
      obtain ⟨k,heq,hk⟩ := hk
      rw [heq,even_prefixTape_external T _ (by omega)]
      exact hone k hk

theorem even_middle_zero_right (T : Int → Bool) (c : Nat) :
    even_middleTape c T (even_rightStop c+1) = false := by
  have hx : even_rightStop c+1 ≠ even_rightStop c := by omega
  simp [even_middleTape,afterEZero,hx]

theorem even_sweepTape_local (T : Int → Bool) (c : Nat)
    (hone : ∀ i : Nat, i<3*(c+1) → T (7+(i:Int))=true)
    (x : Int) (hx : 1 ≤ x) (hy : x ≤ 6) :
    even_finalSweepTape c T x = decide (x ∈ even_tailBase.marked) := by
  have hon := even_middle_ones T c hone
  have hright := even_middle_zero_right T c
  have hcount : 5+3*c = (4+3*c)+1 := by omega
  unfold even_finalSweepTape
  rw [hcount, even_swept_closed (4+3*c) (even_middleTape c T) (even_rightStop c)
    (by simpa [hcount] using hon) hright]
  have h6 : even_rightStop c - (((4+3*c):Nat):Int) = 6 := by unfold even_rightStop; omega
  have haway : x ≠ even_rightStop c+1 := by unfold even_rightStop; omega
  simp only [h6, if_neg haway]
  by_cases hx6 : x = 6
  · subst x
    simp [even_tailBase]
  · simp only [if_neg hx6, even_middleTape,afterEZero]
    have h0 : x≠even_rightStop c := by unfold even_rightStop; omega
    have h1 : x≠even_rightStop c+1 := by unfold even_rightStop; omega
    have h2 : x≠even_rightStop c+2 := by unfold even_rightStop; omega
    rw [if_neg h0,if_neg h1,if_neg h2]
    rw [even_prefixTape_local T x (by omega) hy]
    have hn2 : x ≠ -2 := by omega
    have hn3 : x ≠ -3 := by omega
    have hn4 : x ≠ -4 := by omega
    have hn5 : x ≠ -5 := by omega
    simp [even_prefFinal,even_tailBase,hx6,hn2,hn3,hn4,hn5,
      Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

#print axioms even_middle_ones
#print axioms even_middle_zero_right
#print axioms even_sweepTape_local

end BB6Coverage.Agent48Champion
namespace BB6Coverage.Agent48Champion

/-- Original physical configuration of the odd-z/c binary-decrement local
submacro; outside [-1,6] the supplied tape can carry any surrounding data. -/
def even_oddCounterInput (T : Int → Bool) : Config :=
  frame even_prefArea T (embed even_prefBase)

def even_oddCounterOutput (c : Nat) (T : Int → Bool) : Config :=
  frame even_tailArea (even_finalSweepTape c T) (embed even_tailFinal)

theorem even_tail_match (T : Int → Bool) (c : Nat)
    (hone : ∀ i : Nat, i<3*(c+1) → T (7+(i:Int))=true) :
    frame even_tailArea (even_finalSweepTape c T) (embed even_tailBase) =
      (⟨3,5,even_finalSweepTape c T⟩ : Config) := by
  unfold frame
  apply congrArg (fun f : Int → Bool => (Config.mk 3 5 f))
  funext x
  by_cases ha : even_tailArea x = true
  · have harea : 1 ≤ x ∧ x ≤ 6 := by simpa [even_tailArea] using ha
    have hx := harea.1
    have hy := harea.2
    simp only [ha,if_pos]
    exact (even_sweepTape_local T c hone x hx hy).symm
  · simp [ha]

/-- Complete physical cost of the one-trailing-zero-bit right-unary micro-macro.
For c arbitrary, the original TM63 runs exactly 60+12c successful moves,
starting from the explicit local odd-decrement section and ending in state D
at the same head with the exact infinite tape specified by even_oddCounterOutput.
No assumption on the exterior context beyond the right unary run and the
three following zero cells is necessary. -/
theorem even_counted_odd_counter (T : Int → Bool) (c : Nat)
    (hone : ∀ i : Nat, i<3*(c+1) → T (7+(i:Int))=true)
    (h0 : T (even_rightStop c) = false)
    (h1 : T (even_rightStop c+1) = false)
    (h2 : T (even_rightStop c+2) = false) :
    run tm2 (60+12*c) (even_oddCounterInput T) =
      some (even_oddCounterOutput c T) := by
  let P := even_prefixTape T
  let h := even_rightStop c
  let B := even_middleTape c T
  let U := even_finalSweepTape c T
  have hp : run tm2 27 (even_oddCounterInput T) = some ⟨4,7,P⟩ :=
    even_prefix15 T
  have hs : run tm2 (3*(c+1)) (⟨4,7,P⟩ : Config) =
      some ⟨4,h,P⟩ := by
    have he := E_scan P 7 (3*(c+1)) (even_prefixTape_start T c hone)
    have heq : 7 + ((3*(c+1)):Int) = h := by unfold h even_rightStop; omega
    simpa [heq] using he
  have hz : run tm2 4 (⟨4,h,P⟩ : Config) =
      some ⟨3,h,B⟩ := by
    obtain ⟨hx0,hx1,hx2⟩ := even_prefixTape_stop T c h0 h1 h2
    simpa [h,B,P,even_middleTape] using E_zero_bridge P h hx0 hx1 hx2
  have hl : run tm2 (3*(5+3*c)) (⟨3,h,B⟩ : Config) =
      some ⟨3,5,U⟩ := by
    have hon := even_middle_ones T c hone
    have hr := even_middle_zero_right T c
    have heq : h - ((5+3*c):Int) = 5 := by unfold h even_rightStop; omega
    simpa [heq,U,B,h,even_finalSweepTape] using counted_left_sweep (5+3*c) B h hon hr
  have ht : run tm2 11 (⟨3,5,U⟩ : Config) =
      some (even_oddCounterOutput c T) := by
    have heq := even_tail_match T c hone
    have hr := even_tail11 U
    rw [heq] at hr
    simpa [even_oddCounterOutput,U] using hr
  have hnum : 60+12*c = 27+(3*(c+1)+(4+(3*(5+3*c)+11))) := by omega
  rw [hnum,run_append,hp]
  simp only [Option.bind_some]
  rw [run_append,hs]
  simp only [Option.bind_some]
  rw [run_append,hz]
  simp only [Option.bind_some]
  rw [run_append,hl]
  simpa using ht

#print axioms even_counted_odd_counter
end BB6Coverage.Agent48Champion
