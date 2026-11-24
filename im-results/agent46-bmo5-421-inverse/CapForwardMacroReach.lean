import CapForwardMacro
import CapBmo
namespace CapSieve
open Bmo

/-- Executable exact test for a terminal at or below the given band limit.
    The termination measure is the remaining number of bands, not raw steps. -/
def bandHaltBy (limit k q : Nat) : Bool :=
  if k>limit then false else
    match bandMacro k q with
    | none => true
    | some (j,v) => if k<j then bandHaltBy limit j v else false
termination_by limit+1-k
decreasing_by omega

theorem macro_arc_grows {x y : Nat} (h : Arc x y) : x<y := by
  cases h with
  | one => decide
  | regular k r hr => have := l_add k; omega
  | special k => have := l_add k; have := p_ge k; omega

theorem macro_reach_le {x y : Nat} (h : AReach x y) : x≤y := by
  induction h with
  | refl => omega
  | tail _ e ih => have := macro_arc_grows e; omega

theorem reached_terminal_band {k x i : Nat} (hb : Band k x) (h : AReach x (T i)) : k≤i := by
  by_cases hki : k≤i
  · exact hki
  · have hle := macro_reach_le h
    have hL := l_mono (show i+1≤k by omega)
    have ht := (terminal_band i).2
    have hx := hb.1
    omega

theorem same_run_prepend_reach {k n x z t : Nat} (hs : SameRun k n x z)
    (h : AReach z t) : AReach x t := by
  induction hs with
  | zero => exact h
  | head e _ ih => exact areach_prepend (regFrom_arc e) (ih h)

theorem strip_arc_to_terminal {x y i : Nat} (e : Arc x y) (h : AReach x (T i)) : AReach y (T i) := by
  rcases strip_first e h with he|hr
  · exact False.elim (terminal_no_arc i y (he.symm ▸ e))
  · exact hr

theorem same_run_strip_terminal {k n x z i : Nat} (hs : SameRun k n x z)
    (h : AReach x (T i)) : AReach z (T i) := by
  induction hs with
  | zero => exact h
  | head e _ ih => exact ih (strip_arc_to_terminal (regFrom_arc e) h)

/-- Exact finite-prefix equivalence, in both directions. No possible
    halting path at a skipped band or inside a compressed run is lost. -/
theorem band_halt_by_iff {limit k x : Nat} (hb : Band k x) :
    bandHaltBy limit k (Q k x)=true ↔ ∃ i, i≤limit ∧ AReach x (T i) := by
  rw [bandHaltBy]
  by_cases hkl : k>limit
  · rw [if_pos hkl]
    constructor
    · intro h; contradiction
    · rintro ⟨i,hi,hr⟩
      have := reached_terminal_band hb hr
      omega
  · rw [if_neg hkl]
    obtain ⟨z,hs,hq,hcase⟩ := band_macro_sound hb
    cases he : bandMacro k (Q k x) with
    | none =>
      rw [he] at hcase
      constructor
      · intro _
        have hzt : z=T k := hcase
        subst z
        exact ⟨k,by omega,same_run_prepend_reach hs .refl⟩
      · intro _; rfl
    | some v =>
      obtain ⟨j,q⟩ := v
      rw [he] at hcase
      obtain ⟨hj,hj',y,ea,hyb,hyq⟩ := hcase
      change (if k<j then bandHaltBy limit j q else false)=true ↔ _
      rw [if_pos hj,←hyq]
      rw [band_halt_by_iff hyb]
      constructor
      · rintro ⟨i,hi,hr⟩
        exact ⟨i,hi,same_run_prepend_reach hs (areach_prepend ea hr)⟩
      · rintro ⟨i,hi,hr⟩
        exact ⟨i,hi,strip_arc_to_terminal ea (same_run_strip_terminal hs hr)⟩
termination_by limit+1-k
decreasing_by omega

/-- All-time existence criterion for the exact forward macro. -/
theorem band_halt_iff {k x : Nat} (hb : Band k x) :
    (∃ limit, bandHaltBy limit k (Q k x)=true) ↔ ∃ i, AReach x (T i) := by
  constructor
  · rintro ⟨b,h⟩
    obtain ⟨i,_,hr⟩ := (band_halt_by_iff hb).mp h
    exact ⟨i,hr⟩
  · rintro ⟨i,hr⟩
    exact ⟨i,(band_halt_by_iff hb).mpr ⟨i,by omega,hr⟩⟩

theorem macro_root_two : (∃ limit, bandHaltBy limit 0 6=true) ↔ ∃ i, AReach 2 (T i) := by
  exact band_halt_iff (x:=2) (k:=0) (by unfold Band L P; decide)

theorem macro_root_three : (∃ limit, bandHaltBy limit 0 8=true) ↔ ∃ i, AReach 3 (T i) := by
  exact band_halt_iff (x:=3) (k:=0) (by unfold Band L P; decide)

theorem macro_root_one : (∃ limit, bandHaltBy limit 0 12=true) ↔ ∃ i, AReach 1 (T i) := by
  have h := band_halt_iff (x:=5) (k:=0) (by unfold Band L P; decide : Band 0 5)
  change (∃ limit, bandHaltBy limit 0 12=true) ↔ ∃ i, AReach 5 (T i) at h
  rw [h]
  constructor
  · rintro ⟨i,hr⟩; exact ⟨i,areach_prepend Arc.one hr⟩
  · rintro ⟨i,hr⟩
    have hi := t_ge4 i
    exact ⟨i,(strip_first Arc.one hr).resolve_left (by omega)⟩

#print axioms band_halt_by_iff
#print axioms macro_root_one
#print axioms macro_root_two
#print axioms macro_root_three
end CapSieve
