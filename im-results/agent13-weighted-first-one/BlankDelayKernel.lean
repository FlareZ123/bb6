import Lean

namespace BB6.Agent13BlankDelay

/-- Follow the deterministic zero-writing state graph until an action is
    either a halt or writes a one. The endpoint has no zero successor. -/
inductive TerminalPath (next : α → Option α) : α → Nat → α → Prop where
  | stop (s : α) (h : next s = none) : TerminalPath next s 0 s
  | step {s t u : α} {d : Nat} (h : next s = some t)
      (tail : TerminalPath next t d u) : TerminalPath next s (d+1) u

theorem TerminalPath.unique {next : α → Option α} {s t u : α} {d e : Nat}
    (h : TerminalPath next s d t) (h' : TerminalPath next s e u) : d=e ∧ t=u := by
  induction h generalizing e u with
  | stop s hs =>
    cases h' with
    | stop => exact ⟨rfl,rfl⟩
    | step hs' _ => rw [hs] at hs'; contradiction
  | step hs tail ih =>
    cases h' with
    | stop _ hs' => rw [hs] at hs'; contradiction
    | step hs' tail' =>
      have he := Option.some.inj (hs.symm.trans hs')
      subst he
      obtain ⟨hd,ht⟩ := ih tail'
      exact ⟨congrArg (·+1) hd,ht⟩

/-- Every terminal path admits a list of its distinct states. Each member
    has a suffix terminal path of length no larger than the whole path. -/
theorem TerminalPath.distinct {next : α → Option α} {s t : α} {d : Nat}
    (h : TerminalPath next s d t) :
    ∃ l : List α, l.Nodup ∧ l.length=d+1 ∧
      ∀ q∈l, ∃ e≤d, TerminalPath next q e t := by
  induction h with
  | stop s hs =>
    refine ⟨[s],by simp,rfl,?_⟩
    intro q hq
    have he : q=s := by simpa using hq
    subst q
    exact ⟨0,Nat.le_refl _,.stop _ hs⟩
  | @step s u t d hs tail ih =>
    obtain ⟨l,hn,hl,hmem⟩ := ih
    have hnot : s∉l := by
      intro hm
      obtain ⟨e,hed,he⟩ := hmem s hm
      have hh := (TerminalPath.step hs tail).unique he
      omega
    refine ⟨s::l, List.nodup_cons.mpr ⟨hnot,hn⟩,by simp [hl],?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨d+1,Nat.le_refl _,.step hs tail⟩
    · obtain ⟨e,he,ht⟩ := hmem q hq
      exact ⟨e,by omega,ht⟩

/-- Six states imply at most five successful blank-preserving moves
    before the first halt or first write. No finite trace approximation. -/
theorem terminal_delay_le_five {next : Fin 6 → Option (Fin 6)} {s t : Fin 6}
    {d : Nat} (h : TerminalPath next s d t) : d≤5 := by
  obtain ⟨l,hn,hl,_⟩ := h.distinct
  have hh : l.length ≤ (List.finRange 6).length :=
    hn.length_le_of_subset (fun q _ => by simp)
  simp at hh
  omega

/-- Executable graph iteration, for enumeration of all six starting states
    and at most six delays. -/
def follow (next : α → Option α) : Nat → α → Option α
  | 0,s => some s
  | d+1,s => (next s).bind (follow next d)

theorem terminalPath_iff_follow {next : α → Option α} {s t : α} {d : Nat} :
    TerminalPath next s d t ↔ follow next d s = some t ∧ next t=none := by
  induction d generalizing s with
  | zero =>
    constructor
    · intro h; cases h with | stop _ h => exact ⟨rfl,h⟩
    · intro h
      have he : s=t := Option.some.inj h.1
      subst t
      exact .stop s h.2
  | succ d ih =>
    constructor
    · intro h
      cases h with
      | step hs ht =>
        obtain ⟨hf,hn⟩ := ih.mp ht
        exact ⟨by simp [follow,hs,hf],hn⟩
    · intro h
      cases hs : next s with
      | none => simp [follow,hs] at h
      | some q =>
        exact .step hs (ih.mpr ⟨by simpa [follow,hs] using h.1,h.2⟩)

/-- All possible blank delays for a distinguished endpoint. The terminal
    check belongs to the caller; the empty path always contributes zero. -/
def delays (next : Fin 6 → Option (Fin 6)) (t : Fin 6) : List Nat :=
  (List.range 6).filter (fun d => (List.finRange 6).any (fun s => follow next d s == some t))

theorem mem_delays_iff {next : Fin 6 → Option (Fin 6)} {t : Fin 6} {d : Nat}
    (ht : next t=none) : d∈delays next t ↔ ∃ s, TerminalPath next s d t := by
  constructor
  · intro h
    simp [delays] at h
    obtain ⟨_,s,hs⟩ := h
    exact ⟨s,terminalPath_iff_follow.mpr ⟨hs,ht⟩⟩
  · rintro ⟨s,hs⟩
    have hd := terminal_delay_le_five hs
    have hf := (terminalPath_iff_follow.mp hs).1
    simp [delays]
    exact ⟨by omega,s,hf⟩

#print axioms terminal_delay_le_five
#print axioms mem_delays_iff
end BB6.Agent13BlankDelay
