import CountedOddBase
import CountedSweep
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48Champion

/-- Every source-exact finite trace in a checked finite region lifts to all
physical tapes matching the fixed local input. -/
theorem finite_heads (m : Machine) (inside : Int → Bool) (f : FConfig) (n : Nat)
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

def prefBase : FConfig := ⟨3,0,[2,3,4]⟩
def prefFinal : FConfig := ⟨4,7,[6,4,3,2,1,0,-1]⟩
def prefArea (x : Int) : Bool := decide (-1 ≤ x ∧ x ≤ 6)

theorem prefix15 (bg : Int → Bool) :
    run tm2 15 (frame prefArea bg (embed prefBase)) =
      some (frame prefArea bg (embed prefFinal)) := by
  have he : fRun tm2 15 prefBase = some prefFinal := by decide
  have hc : (List.range 15).all (fun k =>
      match fRun tm2 k prefBase with
      | none => true
      | some z => prefArea z.head) = true := by decide
  rw [run_frame tm2 prefArea bg (embed prefBase) 15
    (finite_heads tm2 prefArea prefBase 15 hc)]
  rw [← finite_run_source tm2 15 prefBase, he]
  rfl

def tailBase : FConfig := ⟨3,5,[-1,0,1,2,3,4]⟩
def tailFinal : FConfig := ⟨3,0,[2,3,4,-1,0]⟩
def tailArea (x : Int) : Bool := decide (-1 ≤ x ∧ x ≤ 6)

theorem tail11 (bg : Int → Bool) :
    run tm2 11 (frame tailArea bg (embed tailBase)) =
      some (frame tailArea bg (embed tailFinal)) := by
  have he : fRun tm2 11 tailBase = some tailFinal := by decide
  have hc : (List.range 11).all (fun k =>
      match fRun tm2 k tailBase with
      | none => true
      | some z => tailArea z.head) = true := by decide
  rw [run_frame tm2 tailArea bg (embed tailBase) 11
    (finite_heads tm2 tailArea tailBase 11 hc)]
  rw [← finite_run_source tm2 11 tailBase, he]
  rfl

/-- Exact closed-form effect of sweeping the moving zero leftwards across a
block of n+1 ones. The source theorem counted_left_sweep supplies its 3(n+1) cost. -/
theorem swept_closed (n : Nat) (T : Int → Bool) (h : Int)
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

#print axioms prefix15
#print axioms tail11
#print axioms swept_closed

end BB6Coverage.Agent48Champion

namespace BB6Coverage.Agent48Champion

/-- The next zero cell after c+1 blocks of three unary marks. -/
def rightStop (c : Nat) : Int := 10 + 3*(c:Int)
def prefixTape (T : Int → Bool) : Int → Bool :=
  (frame prefArea T (embed prefFinal)).tape
def middleTape (c : Nat) (T : Int → Bool) : Int → Bool :=
  afterEZero (prefixTape T) (rightStop c)
def finalSweepTape (c : Nat) (T : Int → Bool) : Int → Bool :=
  sweptLeft (5+3*c) (middleTape c T) (rightStop c)

theorem prefixTape_external (T : Int → Bool) (x : Int) (hx : x > 6) :
    prefixTape T x = T x := by
  have harea : prefArea x = false := by
    simp [prefArea]; omega
  simp [prefixTape,frame,harea]

theorem prefixTape_local (T : Int → Bool) (x : Int)
    (hx : -1 ≤ x) (hy : x ≤ 6) :
    prefixTape T x = decide (x ∈ prefFinal.marked) := by
  have harea : prefArea x = true := by
    simp [prefArea]; omega
  simp [prefixTape,frame,harea,embed]

theorem prefixTape_start (T : Int → Bool) (c : Nat)
    (hone : ∀ i : Nat, i<3*(c+1) → T (7+(i:Int))=true) :
    linearRightOnes (prefixTape T) 7 (3*(c+1)) := by
  intro i hi
  rw [prefixTape_external T (7+(i:Int)) (by omega)]
  exact hone i hi

theorem prefixTape_stop (T : Int → Bool) (c : Nat)
    (h0 : T (rightStop c) = false)
    (h1 : T (rightStop c+1) = false)
    (h2 : T (rightStop c+2) = false) :
    prefixTape T (rightStop c) = false ∧
    prefixTape T (rightStop c+1) = false ∧
    prefixTape T (rightStop c+2) = false := by
  constructor
  · rw [prefixTape_external _ _ (by unfold rightStop; omega)]
    exact h0
  constructor
  · rw [prefixTape_external _ _ (by unfold rightStop; omega)]
    exact h1
  · rw [prefixTape_external _ _ (by unfold rightStop; omega)]
    exact h2

theorem middle_ones (T : Int → Bool) (c : Nat)
    (hone : ∀ i : Nat, i<3*(c+1) → T (7+(i:Int))=true) :
    leftOnes (middleTape c T) (rightStop c) (5+3*c) := by
  intro i hi
  have hright : rightStop c - (i:Int) ≤ rightStop c := by omega
  have hleft : 6 ≤ rightStop c - (i:Int) := by unfold rightStop; omega
  by_cases hi0 : i=0
  · subst i
    simp [middleTape,afterEZero]
  · have hdiff : rightStop c - (i:Int) ≠ rightStop c := by omega
    have hdiff1 : rightStop c - (i:Int) ≠ rightStop c+1 := by omega
    have hdiff2 : rightStop c - (i:Int) ≠ rightStop c+2 := by omega
    simp only [middleTape,afterEZero,if_neg hdiff,if_neg hdiff1,if_neg hdiff2]
    by_cases h6 : rightStop c - (i:Int) = 6
    · rw [h6, prefixTape_local T 6 (by omega) (by omega)]
      decide
    · have hxgt : 7 ≤ rightStop c - (i:Int) := by omega
      have hk : ∃ k : Nat, rightStop c - (i:Int) = 7+(k:Int) ∧ k<3*(c+1) := by
        refine ⟨(rightStop c - (i:Int) - 7).toNat, ?_, ?_⟩
        · have hnonneg : 0 ≤ rightStop c - (i:Int) - 7 := by omega
          have hcast : (((rightStop c - (i:Int) - 7).toNat):Int) =
            rightStop c - (i:Int) - 7 := Int.toNat_of_nonneg hnonneg
          omega
        · have hcast : (((rightStop c - (i:Int) - 7).toNat):Int) =
            rightStop c - (i:Int) - 7 := Int.toNat_of_nonneg (by omega)
          unfold rightStop at *
          omega
      obtain ⟨k,heq,hk⟩ := hk
      rw [heq,prefixTape_external T _ (by omega)]
      exact hone k hk

theorem middle_zero_right (T : Int → Bool) (c : Nat) :
    middleTape c T (rightStop c+1) = false := by
  have hx : rightStop c+1 ≠ rightStop c := by omega
  simp [middleTape,afterEZero,hx]

theorem sweepTape_local (T : Int → Bool) (c : Nat)
    (hone : ∀ i : Nat, i<3*(c+1) → T (7+(i:Int))=true)
    (x : Int) (hx : -1 ≤ x) (hy : x ≤ 6) :
    finalSweepTape c T x = decide (x ∈ tailBase.marked) := by
  have hon := middle_ones T c hone
  have hright := middle_zero_right T c
  have hcount : 5+3*c = (4+3*c)+1 := by omega
  unfold finalSweepTape
  rw [hcount, swept_closed (4+3*c) (middleTape c T) (rightStop c)
    (by simpa [hcount] using hon) hright]
  have h6 : rightStop c - (((4+3*c):Nat):Int) = 6 := by unfold rightStop; omega
  have haway : x ≠ rightStop c+1 := by unfold rightStop; omega
  simp only [h6, if_neg haway]
  by_cases hx6 : x = 6
  · subst x
    simp [tailBase]
  · simp only [if_neg hx6, middleTape,afterEZero]
    have h0 : x≠rightStop c := by unfold rightStop; omega
    have h1 : x≠rightStop c+1 := by unfold rightStop; omega
    have h2 : x≠rightStop c+2 := by unfold rightStop; omega
    rw [if_neg h0,if_neg h1,if_neg h2]
    rw [prefixTape_local T x hx hy]
    simp [prefFinal,tailBase,hx6, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

#print axioms middle_ones
#print axioms middle_zero_right
#print axioms sweepTape_local

end BB6Coverage.Agent48Champion
namespace BB6Coverage.Agent48Champion

/-- Original physical configuration of the odd-z/c binary-decrement local
submacro; outside [-1,6] the supplied tape can carry any surrounding data. -/
def oddCounterInput (T : Int → Bool) : Config :=
  frame prefArea T (embed prefBase)

def oddCounterOutput (c : Nat) (T : Int → Bool) : Config :=
  frame tailArea (finalSweepTape c T) (embed tailFinal)

theorem tail_match (T : Int → Bool) (c : Nat)
    (hone : ∀ i : Nat, i<3*(c+1) → T (7+(i:Int))=true) :
    frame tailArea (finalSweepTape c T) (embed tailBase) =
      (⟨3,5,finalSweepTape c T⟩ : Config) := by
  unfold frame
  apply congrArg (fun f : Int → Bool => (Config.mk 3 5 f))
  funext x
  by_cases ha : tailArea x = true
  · have harea : -1 ≤ x ∧ x ≤ 6 := by simpa [tailArea] using ha
    have hx := harea.1
    have hy := harea.2
    simp only [ha,if_pos]
    exact (sweepTape_local T c hone x hx hy).symm
  · simp [ha]

/-- Complete physical cost of the valuation-zero right-unary micro-macro.
For c arbitrary, the original TM63 runs exactly 48+12c successful moves,
starting from the explicit local odd-decrement section and ending in state D
at the same head with the exact infinite tape specified by oddCounterOutput.
No assumption on the exterior context beyond the right unary run and the
three following zero cells is necessary. -/
theorem counted_odd_counter (T : Int → Bool) (c : Nat)
    (hone : ∀ i : Nat, i<3*(c+1) → T (7+(i:Int))=true)
    (h0 : T (rightStop c) = false)
    (h1 : T (rightStop c+1) = false)
    (h2 : T (rightStop c+2) = false) :
    run tm2 (48+12*c) (oddCounterInput T) =
      some (oddCounterOutput c T) := by
  let P := prefixTape T
  let h := rightStop c
  let B := middleTape c T
  let U := finalSweepTape c T
  have hp : run tm2 15 (oddCounterInput T) = some ⟨4,7,P⟩ :=
    prefix15 T
  have hs : run tm2 (3*(c+1)) (⟨4,7,P⟩ : Config) =
      some ⟨4,h,P⟩ := by
    have he := E_scan P 7 (3*(c+1)) (prefixTape_start T c hone)
    have heq : 7 + ((3*(c+1)):Int) = h := by unfold h rightStop; omega
    simpa [heq] using he
  have hz : run tm2 4 (⟨4,h,P⟩ : Config) =
      some ⟨3,h,B⟩ := by
    obtain ⟨hx0,hx1,hx2⟩ := prefixTape_stop T c h0 h1 h2
    simpa [h,B,P,middleTape] using E_zero_bridge P h hx0 hx1 hx2
  have hl : run tm2 (3*(5+3*c)) (⟨3,h,B⟩ : Config) =
      some ⟨3,5,U⟩ := by
    have hon := middle_ones T c hone
    have hr := middle_zero_right T c
    have heq : h - ((5+3*c):Int) = 5 := by unfold h rightStop; omega
    simpa [heq,U,B,h,finalSweepTape] using counted_left_sweep (5+3*c) B h hon hr
  have ht : run tm2 11 (⟨3,5,U⟩ : Config) =
      some (oddCounterOutput c T) := by
    have heq := tail_match T c hone
    have hr := tail11 U
    rw [heq] at hr
    simpa [oddCounterOutput,U] using hr
  have hnum : 48+12*c = 15+(3*(c+1)+(4+(3*(5+3*c)+11))) := by omega
  rw [hnum,run_append,hp]
  simp only [Option.bind_some]
  rw [run_append,hs]
  simp only [Option.bind_some]
  rw [run_append,hz]
  simp only [Option.bind_some]
  rw [run_append,hl]
  simpa using ht

#print axioms counted_odd_counter
end BB6Coverage.Agent48Champion
