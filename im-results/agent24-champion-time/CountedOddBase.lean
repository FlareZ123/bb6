import ChampionRootBridge
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48Champion

/-!
Source-authentic counted 48-step odd binary-decrement base.
This imports the original physical TM63 table and infinite-tape semantics
from ChampionRootBridge/Frontier. The proof supports arbitrary tape content
outside the closed interval [-1,12]. Neither the full Inc0 cost for all
valuations nor the global champion score is claimed here.
-/

/-- Keep the canonical local tape inside the chosen neighborhood, while
preserving an arbitrary infinite-tape background outside that neighborhood. -/
def frame (inside : Int → Bool) (background : Int → Bool) (c : Config) : Config :=
  {c with tape := fun x => if inside x then c.tape x else background x}

theorem frame_rawStep (m : Machine) (inside : Int → Bool)
    (background : Int → Bool) (c : Config) (h : inside c.head = true) :
    rawStep m (frame inside background c) =
      (rawStep m c).map (frame inside background) := by
  unfold rawStep
  have hr : readSlot (frame inside background c) = readSlot c := by
    simp [frame, readSlot, h]
  rw [hr]
  cases ht : m (readSlot c) with
  | none => simp
  | some t =>
    simp only [Option.map_some]
    cases c with
    | mk s p tape =>
      cases t with
      | mk w dir next =>
        simp only [frame, applyMove]
        apply congrArg (fun f : Int → Bool =>
          some (Config.mk next (p + if dir then 1 else -1) f))
        funext x
        by_cases hx : x = p
        · subst x
          simp [h]
        · simp [hx]

/-- Frame theorem for any machine whose canonical run never reads outside
the specified neighborhood: arbitrary exterior bits cannot change the trace
or influence any written bit in the neighborhood. -/
theorem run_frame (m : Machine) (inside : Int → Bool) (background : Int → Bool)
    (c : Config) (n : Nat)
    (hin : ∀ k, k<n → ∀ d, run m k c = some d → inside d.head = true) :
    run m n (frame inside background c) =
      (run m n c).map (frame inside background) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hp : ∀ k, k<n → ∀ d, run m k c = some d → inside d.head = true := by
      intro k hk d hd
      exact hin k (by omega) d hd
    have ih' := ih hp
    simp only [run, ih']
    cases hh : run m n c with
    | none => simp
    | some d =>
      have hd := hin n (by omega) d hh
      simp [hh, frame_rawStep m inside background d hd]

private theorem counted_embed_fMove (c : FConfig) (t : Move) :
    embed (fMove c t) = applyMove (embed c) t := by
  cases c with
  | mk q h marks =>
    cases t with
    | mk w d q' =>
      cases w <;> cases d <;>
        simp only [embed, fMove, applyMove] <;>
        apply congrArg (fun f : Int → Bool => Config.mk q' _ f) <;>
        funext x <;>
        (by_cases hx : x = h <;> simp [hx])

private theorem counted_embed_fStep (m : Machine) (c : FConfig) :
    (fStep m c).map embed = rawStep m (embed c) := by
  simp only [fStep, rawStep, readSlot, embed, Option.map_map]
  congr 1
  funext t
  simpa only [Function.comp_def, embed] using counted_embed_fMove c t

theorem finite_run_source (m : Machine) (n : Nat) (c : FConfig) :
    (fRun m n c).map embed = run m n (embed c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fRun, run]
    rw [← ih]
    cases h : fRun m n c with
    | none => simp [h]
    | some d => simp [h, counted_embed_fStep]

/-- The true physical tape pattern of the c=0, v₂(z)=0 Inc0 branch within
the 14 cells it will query. Everything beyond may be arbitrary. -/
def oddBase : FConfig := ⟨3,0,[2,3,4,7,8,9]⟩
def oddFinal : FConfig := ⟨3,0,[2,3,4,7,8,9,10,11,12,0,-1]⟩

/-- Exact finite trace of 48 raw source steps, with an independently checked
complete marked-cell list and terminal state/head. -/
theorem odd48_exact : fRun tm2 48 oddBase = some oddFinal := by decide

def inside48 (x : Int) : Bool := decide (-1 ≤ x ∧ x ≤ 12)

/-- No head query outside [-1,12] in the entire 48-step physical trace. -/
theorem odd48_heads :
    ∀ k, k<48 → ∀ d, run tm2 k (embed oddBase) = some d →
      inside48 d.head = true := by
  intro k hk d hd
  have hcheck : (List.range 48).all (fun k =>
      match fRun tm2 k oddBase with
      | none => true
      | some f => inside48 f.head) = true := by decide
  have hitem := List.all_eq_true.mp hcheck k (List.mem_range.mpr hk)
  have hsource := finite_run_source tm2 k oddBase
  cases hrun : fRun tm2 k oddBase with
  | none =>
      simp only [hrun, Option.map_none] at hsource
      rw [← hsource] at hd
      cases hd
  | some f =>
      simp only [hrun, Option.map_some] at hsource
      have hd' := Option.some.inj (hsource.trans hd)
      subst d
      simpa [hrun, embed] using hitem

/-- An arbitrary surrounding tape is allowed. The genuine original TM63
performs exactly 48 successful steps, restoring D at head 0; its resulting
entire infinite tape consists of the stated local edits, plus the original
unmodified arbitrary exterior. This source-proves one valuation-zero,
right-counter-zero branch of the conjectured Inc0 primitive-step formula. -/
theorem odd48_frame (background : Int → Bool) :
    run tm2 48 (frame inside48 background (embed oddBase)) =
      some (frame inside48 background (embed oddFinal)) := by
  rw [run_frame tm2 inside48 background (embed oddBase) 48 odd48_heads]
  rw [← finite_run_source tm2 48 oddBase, odd48_exact]
  rfl

#print axioms frame_rawStep
#print axioms run_frame
#print axioms odd48_exact
#print axioms odd48_heads
#print axioms odd48_frame

end BB6Coverage.Agent48Champion
