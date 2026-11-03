import MarkerOracle
import Lean.Elab.Tactic.Omega

namespace BB6Coverage

/-- The finite support to the right of a head is exactly a supplied finite
    list of nonnegative offsets, with arbitrary older marks to its left. -/
def finitePatternRight (c : FinRayCfg) (word : List Int) : Bool :=
  c.ones.all (fun x =>
    if decide (c.head ≤ x) then word.contains (x-c.head) else true) &&
    word.all (fun k => decide (0 ≤ k) && c.ones.contains (c.head+k))

theorem finitePatternRight_nonneg (c : FinRayCfg) (word : List Int)
    (h : finitePatternRight c word = true) :
    ∀ k, k ∈ word → 0 ≤ k := by
  have hp := (Bool.and_eq_true _ _).mp h
  intro k hk
  have hk' := (List.all_eq_true.mp hp.2) k hk
  exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hk').1

theorem finitePatternRight_sound (c : FinRayCfg) (word : List Int)
    (h : finitePatternRight c word = true) :
    ∀ x, c.head ≤ x → finiteTape c x = word.contains (x-c.head) := by
  have hp := (Bool.and_eq_true _ _).mp h
  have hfwd : ∀ y, y ∈ c.ones → c.head ≤ y → y-c.head ∈ word := by
    intro y hy hge
    have hy' := (List.all_eq_true.mp hp.1) y hy
    have hm : word.contains (y-c.head) = true := by
      simpa [hge] using hy'
    exact List.contains_iff_mem.mp hm
  have hrev : ∀ k, k ∈ word → c.head+k ∈ c.ones := by
    intro k hk
    have hk' := (List.all_eq_true.mp hp.2) k hk
    exact List.contains_iff_mem.mp ((Bool.and_eq_true _ _).mp hk').2
  intro x hx
  change c.ones.contains x = word.contains (x-c.head)
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hmem
    exact List.contains_iff_mem.mpr (hfwd x (List.contains_iff_mem.mp hmem) hx)
  · intro hmem
    have hmatch := hrev (x-c.head) (List.contains_iff_mem.mp hmem)
    have heq : c.head+(x-c.head) = x := by omega
    exact List.contains_iff_mem.mpr (heq ▸ hmatch)

def finitePatternSeed (s : Fin 6) (word : List Int) : FinRayCfg :=
  {state := s, head := 0, ones := word}

theorem embed_finitePatternSeed (s : Fin 6) (word : List Int)
    (hnonneg : ∀ k, k ∈ word → 0 ≤ k) :
    embedFinRay (finitePatternSeed s word) =
      tailSeed s (fun k => word.contains k) := by
  apply congrArg (fun tape : Int → Bool =>
    ({state := s, head := 0, tape := tape} : Config))
  funext x
  change word.contains x = (if 0 ≤ x then word.contains x else false)
  by_cases hx : 0 ≤ x
  · simp [hx]
  · have hnot : x ∉ word := by
      intro hm
      have hge := hnonneg x hm
      omega
    simp [hx, hnot]

/-- Compute the exact support of the finite ray currently under the head;
    duplicates are harmless because all comparisons use membership. -/
def finiteRightWord (c : FinRayCfg) : List Int :=
  (c.ones.filter (fun x => decide (c.head ≤ x))).map (fun x => x-c.head)

/-- Original-machine finite-prefix certificate for any finite right-tail
    word, including two or more marked positions and the empty word. -/
def finiteWordEntryCheck (p : PartialMachine)
    (entrySteps n : Nat) : Bool :=
  match finitePartialRun p entrySteps finiteBlank with
  | none => false
  | some entry =>
      let word := finiteRightWord entry
      match finitePartialRun p n (finitePatternSeed entry.state word) with
      | none => false
      | some c =>
          finitePatternRight entry word &&
          decide (c.state = entry.state) &&
          decide (0 < c.head) &&
          finitePatternRight c word &&
          (List.range n).all (fun j =>
            match finitePartialRun p j (finitePatternSeed entry.state word) with
            | none => false
            | some d => decide (0 ≤ d.head))

theorem finiteWordEntryCheck_sound (p : PartialMachine)
    (entrySteps n bound : Nat) (hn : 0 < n)
    (h : finiteWordEntryCheck p entrySteps n = true) :
    Cover (DecidedBelow bound) p := by
  cases he : finitePartialRun p entrySteps finiteBlank with
  | none => simp [finiteWordEntryCheck, he] at h
  | some entry =>
      let word := finiteRightWord entry
      cases hc : finitePartialRun p n (finitePatternSeed entry.state word) with
      | none => simp [finiteWordEntryCheck, he, word, hc] at h
      | some c =>
          simp only [finiteWordEntryCheck, he, word, hc,
            Bool.and_eq_true, decide_eq_true_eq] at h
          rcases h with ⟨⟨⟨⟨hentryWord, hstate⟩, hpos⟩, hmacroWord⟩, hwindow⟩
          have hseed : embedFinRay (finitePatternSeed entry.state word) =
              tailSeed entry.state (fun x => word.contains x) :=
            embed_finitePatternSeed entry.state word
              (finitePatternRight_nonneg entry word hentryWord)
          apply Cover.leaf
          intro m hm
          left
          apply entry_tail_pattern_never m entry.state
            (fun x => word.contains x) entrySteps n c.head.toNat hn (by omega)
          · refine ⟨embedFinRay entry, ?_, ?_⟩
            · simpa only [embedFinRay_blank] using
                (finitePartialRun_sound p m hm finiteBlank entry entrySteps he)
            · constructor
              · rfl
              · intro x hx
                exact finitePatternRight_sound entry word hentryWord x hx
          · refine ⟨embedFinRay c, ?_, ?_, ?_, ?_⟩
            · simpa only [hseed] using
                (finitePartialRun_sound p m hm
                  (finitePatternSeed entry.state word) c n hc)
            · exact hstate
            · simp only [embedFinRay]
              omega
            · intro x hx
              have hge : c.head ≤ x := by omega
              have ht := finitePatternRight_sound c word hmacroWord x hge
              have hcast : (c.head.toNat : Int) = c.head := by omega
              simpa only [embedFinRay, hcast] using ht
          · intro j hj d hrun
            have hflag :
                (match finitePartialRun p j (finitePatternSeed entry.state word) with
                 | none => false
                 | some t => decide (0 ≤ t.head)) = true :=
              (List.all_eq_true.mp hwindow) j (List.mem_range.mpr hj)
            cases hjfin : finitePartialRun p j (finitePatternSeed entry.state word) with
            | none => simp [hjfin] at hflag
            | some t =>
                have hge : 0 ≤ t.head :=
                  of_decide_eq_true (by simpa [hjfin] using hflag)
                have hsource : run m j
                    (tailSeed entry.state (fun x => word.contains x)) =
                    some (embedFinRay t) := by
                  simpa only [hseed] using
                    (finitePartialRun_sound p m hm
                      (finitePatternSeed entry.state word) t j hjfin)
                have heq : d = embedFinRay t :=
                  Option.some.inj (hrun.symm.trans hsource)
                subst d
                simpa [embedFinRay] using hge

def finiteWordEntryOracle (p : PartialMachine)
    (entryLimit macroLimit : Nat) : Bool :=
  (List.range entryLimit).any (fun k =>
    (List.range macroLimit).any (fun i =>
      finiteWordEntryCheck p k (i+1)))

theorem finiteWordEntryOracle_sound (p : PartialMachine)
    (entryLimit macroLimit bound : Nat)
    (h : finiteWordEntryOracle p entryLimit macroLimit = true) :
    Cover (DecidedBelow bound) p := by
  obtain ⟨k, _, hk⟩ := List.any_eq_true.mp h
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp hk
  exact finiteWordEntryCheck_sound p k (i+1) bound (by omega) hi

/-- Two adjacent marked cells genuinely enter the all-time translated word
    recurrence after exactly two ordinary blank-root moves. -/
def twoMarkWordPump : PartialMachine := fun s =>
  if s = (0,false) then some (some ⟨true,true,1⟩)
  else if s = (1,false) then some (some ⟨true,false,2⟩)
  else if s = (2,true) then some (some ⟨true,true,3⟩)
  else if s = (3,true) then some (some ⟨true,true,4⟩)
  else if s = (4,false) then some (some ⟨true,false,2⟩)
  else none

theorem twoMark_word_check :
    finiteWordEntryCheck twoMarkWordPump 2 3 = true := by decide

theorem twoMark_word_cover (bound : Nat) :
    Cover (DecidedBelow bound) twoMarkWordPump :=
  finiteWordEntryCheck_sound twoMarkWordPump 2 3 bound
    (by decide) twoMark_word_check

#print axioms finitePatternRight_sound
#print axioms finiteWordEntryCheck_sound
#print axioms finiteWordEntryOracle_sound
#print axioms twoMark_word_cover
end BB6Coverage
