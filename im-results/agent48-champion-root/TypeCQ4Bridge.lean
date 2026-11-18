import CountedOddBase
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48Champion

/-!
A source-table finite bridge for the type-C q4 checkpoint produced after
the P22 / P34 / P22 prefix sequence. The exact local input is eight
consecutive ones immediately left of the state-4 head, followed by two
zeros farther left and four zeros to the right. The 33-step trace reaches
state 4 at head -8. The frame lift below preserves arbitrary exterior tape.
-/

/-- Type-C q4 input: state 4 at head 1, with ones on [-7,0]. -/
def typeCStart : FConfig := ⟨4, 1, [-7,-6,-5,-4,-3,-2,-1,0]⟩

/-- Finite output of the 33-step trace, including the final write at -9. -/
def typeCEnd : FConfig := ⟨4, -8, [-9,-6,-5,-4,-3,-2,-1,0,1,2,3]⟩

/-- Literal finite trace in the original TM63 transition table. -/
theorem typeC_bridge_finite :
    fRun tm2 33 typeCStart = some typeCEnd := by
  decide

/-- The exact read interval of the 33-step trace is [-9,3]. -/
def typeCInside (x : Int) : Bool := decide (-9 ≤ x ∧ x ≤ 3)

/-- The head of every intermediate finite run lies in the read interval. -/
def typeCHeadAt (k : Nat) : Bool :=
  match fRun tm2 k typeCStart with
  | none => false
  | some c => typeCInside c.head

theorem typeC_head_bound : ∀ k : Fin 33, typeCHeadAt k.val = true := by
  decide

theorem typeC_reads_inside :
    ∀ k, k < 33 → ∀ d, run tm2 k (embed typeCStart) = some d →
      typeCInside d.head = true := by
  intro k hk d hd
  have hsource := finite_run_source tm2 k typeCStart
  rw [← hsource] at hd
  cases hrun : fRun tm2 k typeCStart with
  | none => simp [hrun] at hd
  | some c =>
    have hEq : embed c = d := by
      have hmap : some (embed c) = some d := by simpa [hrun] using hd
      injection hmap with hEq
    subst d
    have hb := typeC_head_bound ⟨k, hk⟩
    simpa [typeCHeadAt, hrun, embed] using hb

/-- The 33-step bridge, lifted to any bi-infinite tape agreeing with the
    finite input on [-9,3]. The exterior is preserved exactly. -/
theorem typeC_bridge_at (T : Int → Bool)
    (hin : ∀ x, typeCInside x = true → T x = (embed typeCStart).tape x) :
    run tm2 33 ({ state := 4, head := 1, tape := T } : Config) =
      some (frame typeCInside T (embed typeCEnd)) := by
  have hstart : frame typeCInside T (embed typeCStart) =
      ({ state := 4, head := 1, tape := T } : Config) := by
    apply congrArg (fun f : Int → Bool => Config.mk 4 1 f)
    funext x
    by_cases hx : typeCInside x = true
    · simp [hx, hin x hx, embed, typeCStart]
    · simp [hx]
  rw [← hstart]
  rw [run_frame tm2 typeCInside T (embed typeCStart) 33 typeC_reads_inside]
  have hblank : run tm2 33 (embed typeCStart) = some (embed typeCEnd) := by
    have h := congrArg (Option.map embed) typeC_bridge_finite
    rw [finite_run_source] at h
    simpa using h
  rw [hblank]
  rfl

#print axioms typeC_bridge_finite
#print axioms typeC_bridge_at

end BB6Coverage.Agent48Champion
