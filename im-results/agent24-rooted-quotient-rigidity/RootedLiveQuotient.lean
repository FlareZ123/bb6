import Lean
import Lean.Elab.Tactic.Omega

/-! General rooted-quotient rigidity, independent of the Busy Beaver machine library. -/
namespace RootedLiveQuotient

universe u
variable {Q : Type u} [DecidableEq Q]

structure Move (Q : Type u) where
  write : Bool
  right : Bool
  next : Q
  deriving DecidableEq

structure Perm (Q : Type u) where
  forward : Q → Q
  backward : Q → Q
  leftInverse : ∀ x, backward (forward x) = x
  rightInverse : ∀ x, forward (backward x) = x

abbrev PartialTable (Q : Type u) := Q → Bool → Option (Option (Move Q))
abbrev Machine (Q : Type u) := Q → Bool → Option (Move Q)

/-- Every defined transition of the partial table is respected by this relabeling. -/
def Compatible (p : PartialTable Q) (m : Machine Q) (e : Perm Q) : Prop :=
  ∀ s b t, p s b = some (some t) →
    ∃ u, m (e.backward s) b = some u ∧
      u.write = t.write ∧ u.right = t.right ∧
      e.forward u.next = t.next

/-- Transition reachability in the defined rows of a partial table, not blank tape reachability. -/
inductive NamedReach (p : PartialTable Q) (root : Q) : Q → Prop where
  | root : NamedReach p root root
  | step {s : Q} {t : Move Q} (hs : NamedReach p root s) (b : Bool)
      (ht : p s b = some t) : NamedReach p root t.next

/-- Common physical identity of every name reachable through the fixed transition graph. -/
theorem named_reachable_agreement (p : PartialTable Q) (m : Machine Q)
    (e f : Perm Q) (root : Q)
    (he : Compatible p m e) (hf : Compatible p m f)
    (hroot : e.backward root = f.backward root) :
    ∀ s, NamedReach p root s → e.backward s = f.backward s := by
  intro s hs
  induction hs with
  | root => exact hroot
  | @step s t hs b ht ih =>
    obtain ⟨ue, hPhysicalE, _,_,hnextE⟩ := he s b t ht
    obtain ⟨uf, hPhysicalF, _,_,hnextF⟩ := hf s b t ht
    have hSame : ue = uf := Option.some.inj (by
      calc
        some ue = m (e.backward s) b := hPhysicalE.symm
        _ = m (f.backward s) b := by rw [ih]
        _ = some uf := hPhysicalF)
    calc
      e.backward t.next = ue.next := by rw [← hnextE]; exact e.leftInverse _
      _ = uf.next := congrArg Move.next hSame
      _ = f.backward t.next := by rw [← hnextF]; exact (f.leftInverse _).symm

/-- Source-table extension. -/
def Extends (r p : PartialTable Q) : Prop :=
  ∀ s b t, r s b = some (some t) → p s b = some (some t)

theorem compatible_of_extends {r p : PartialTable Q} {m : Machine Q}
    {e : Perm Q} (h : Extends r p) (hc : Compatible p m e) :
    Compatible r m e := by
  intro s b t ht
  exact hc s b t (h s b t ht)

/-- Two renamed copies of the same machine agree on any defined row whose
    source is reachable in the shared parent, and agree on target identities
    whenever either target is already reachable there. -/
theorem rooted_slot_agrees (r p q : PartialTable Q) (m : Machine Q)
    (e f : Perm Q) (root s : Q) (b : Bool) (a c : Move Q)
    (hpe : Extends r p) (hqf : Extends r q)
    (he : Compatible p m e) (hf : Compatible q m f)
    (hroot : e.backward root = f.backward root)
    (hs : NamedReach r root s)
    (ha : p s b = some (some a)) (hc : q s b = some (some c)) :
    a.write = c.write ∧ a.right = c.right ∧
      ((NamedReach r root a.next ∨ NamedReach r root c.next) → a.next = c.next) := by
  have hre : Compatible r m e := compatible_of_extends hpe he
  have hrf : Compatible r m f := compatible_of_extends hqf hf
  have hSource := named_reachable_agreement r m e f root hre hrf hroot s hs
  obtain ⟨ue,hue,hwe,hre',hne⟩ := he s b a ha
  obtain ⟨uf,huf,hwf,hrf',hnf⟩ := hf s b c hc
  have hSame : ue = uf := Option.some.inj (by
    calc
      some ue = m (e.backward s) b := hue.symm
      _ = m (f.backward s) b := by rw [hSource]
      _ = some uf := huf)
  have hW : a.write = c.write := by calc
    a.write = ue.write := hwe.symm
    _ = uf.write := by rw [hSame]
    _ = c.write := hwf
  have hR : a.right = c.right := by calc
    a.right = ue.right := hre'.symm
    _ = uf.right := by rw [hSame]
    _ = c.right := hrf'
  have hPhysicalNext : e.backward a.next = f.backward c.next := by
    calc
      e.backward a.next = ue.next := by rw [← hne]; exact e.leftInverse _
      _ = uf.next := congrArg Move.next hSame
      _ = f.backward c.next := by rw [← hnf]; exact (f.leftInverse _).symm
  refine ⟨hW, hR, ?_⟩
  intro ht
  rcases ht with haReach | hcReach
  · have hCommon := named_reachable_agreement r m e f root hre hrf hroot a.next haReach
    have hf_inj : Function.Injective f.backward := by
      intro x y hxy
      have h := congrArg f.forward hxy
      simpa [f.rightInverse] using h
    exact hf_inj (hCommon.symm.trans hPhysicalNext)
  · have hCommon := named_reachable_agreement r m e f root hre hrf hroot c.next hcReach
    have he_inj : Function.Injective e.backward := by
      intro x y hxy
      have h := congrArg e.forward hxy
      simpa [e.rightInverse] using h
    exact he_inj (hPhysicalNext.trans hCommon.symm)

/-- Sufficient combinatorial collision criterion for two partial tables.
    It depends on the *parent transition graph*, not the machine run. -/
def RootConflict (r p q : PartialTable Q) (root : Q) : Prop :=
  ∃ s b a c, NamedReach r root s ∧ p s b = some (some a) ∧ q s b = some (some c) ∧
    (a.write ≠ c.write ∨ a.right ≠ c.right ∨
      ((NamedReach r root a.next ∨ NamedReach r root c.next) ∧ a.next ≠ c.next))

/-- A true combinatorial conflict excludes any common physical completion,
    including completions presented through different name permutations. -/
theorem root_conflict_no_common (r p q : PartialTable Q) (root : Q)
    (hpe : Extends r p) (hqf : Extends r q)
    (hconf : RootConflict r p q root) :
    ¬ ∃ (m : Machine Q) (e f : Perm Q),
        e.backward root = f.backward root ∧
        Compatible p m e ∧ Compatible q m f := by
  rintro ⟨m,e,f,hroot,he,hf⟩
  rcases hconf with ⟨s,b,a,c,hs,ha,hc,hneq⟩
  obtain ⟨hw,hr,hn⟩ := rooted_slot_agrees r p q m e f root s b a c
    hpe hqf he hf hroot hs ha hc
  rcases hneq with h | h | ⟨hreach,h⟩
  · exact h hw
  · exact h hr
  · exact h (hn hreach)

/-- Syntactic one-step targets of the defined parent transitions. -/
def neighbors (r : PartialTable Q) (s : Q) : List Q :=
  [false, true].filterMap (fun b => (r s b).bind (fun mt => mt.map Move.next))

/-- Iterated finite closure from the parent root; no graph completeness
    assumption is needed for soundness at an arbitrary chosen depth. -/
def namedReachRows (r : PartialTable Q) (root : Q) : Nat → List Q
  | 0 => [root]
  | n+1 =>
      let xs := namedReachRows r root n
      xs ++ xs.flatMap (neighbors r)

theorem neighbors_sound (r : PartialTable Q) (root s x : Q)
    (hs : NamedReach r root s) (hx : x ∈ neighbors r s) :
    NamedReach r root x := by
  obtain ⟨b, _, he⟩ := List.mem_filterMap.mp hx
  cases ht : r s b with
  | none => simp [ht] at he
  | some mt =>
      cases mt with
      | none => simp [ht] at he
      | some t =>
          have hn : t.next = x := by simpa [ht] using he
          rw [← hn]
          exact NamedReach.step hs b ht

theorem namedReachRows_sound (r : PartialTable Q) (root : Q) (fuel : Nat) :
    ∀ x, x ∈ namedReachRows r root fuel → NamedReach r root x := by
  induction fuel with
  | zero =>
    intro x hx
    have heq : x = root := by simpa [namedReachRows] using hx
    subst x
    exact NamedReach.root
  | succ n ih =>
    intro x hx
    have h : x ∈ namedReachRows r root n ∨
        x ∈ (namedReachRows r root n).flatMap (neighbors r) := by
      exact List.mem_append.mp hx
    rcases h with hprev | hnext
    · exact ih x hprev
    · obtain ⟨s, hs, hn⟩ := List.mem_flatMap.mp hnext
      exact neighbors_sound r root s x (ih s hs) hn

/-- If the bounded worklist is closed under all live transitions, it is
    already the *entire* connected component of the root. The certificate
    is data-dependent, so no completeness depth is assumed globally. -/
def closureCheck (r : PartialTable Q) (root : Q) (fuel : Nat) : Bool :=
  let rows := namedReachRows r root fuel
  rows.all (fun s =>
    ([false,true] : List Bool).all (fun b =>
      match r s b with
      | some (some t) => decide (t.next ∈ rows)
      | _ => true))

theorem namedReachRows_root_mem (r : PartialTable Q) (root : Q)
    (fuel : Nat) : root ∈ namedReachRows r root fuel := by
  induction fuel with
  | zero => simp [namedReachRows]
  | succ n ih =>
    exact List.mem_append.mpr (Or.inl ih)

theorem closureCheck_complete (r : PartialTable Q) (root : Q) (fuel : Nat)
    (h : closureCheck r root fuel = true) :
    ∀ s, NamedReach r root s → s ∈ namedReachRows r root fuel := by
  intro s hs
  induction hs with
  | root => exact namedReachRows_root_mem r root fuel
  | @step s t hs b ht ih =>
    have hRows : (namedReachRows r root fuel).all (fun s =>
      ([false,true] : List Bool).all (fun b =>
        match r s b with
        | some (some t) => decide (t.next ∈ namedReachRows r root fuel)
        | _ => true)) = true := by exact h
    have hStep := List.all_eq_true.mp hRows s ih
    have hb : b ∈ ([false,true] : List Bool) := by cases b <;> simp
    have hCell := List.all_eq_true.mp hStep b hb
    have htmem : decide (t.next ∈ namedReachRows r root fuel) = true := by
      simpa [ht] using hCell
    exact of_decide_eq_true htmem

theorem namedReachRows_exact (r : PartialTable Q) (root : Q) (fuel : Nat)
    (h : closureCheck r root fuel = true) (s : Q) :
    NamedReach r root s ↔ s ∈ namedReachRows r root fuel := by
  constructor
  · exact closureCheck_complete r root fuel h s
  · exact namedReachRows_sound r root fuel s

/-- Executable, finite-depth conflict search; every `true` produces a
    rigorous quotient-disjointness proof without any completeness claim. -/
def conflictCheck (r p q : PartialTable Q) (root : Q) (fuel : Nat) : Bool :=
  let rows := namedReachRows r root fuel
  rows.any (fun s =>
    ([false, true] : List Bool).any (fun b =>
      match p s b, q s b with
      | some (some a), some (some c) =>
          decide (a.write ≠ c.write ∨ a.right ≠ c.right ∨
            (((a.next ∈ rows) ∨ (c.next ∈ rows)) ∧ a.next ≠ c.next))
      | _, _ => false))

theorem conflictCheck_sound (r p q : PartialTable Q) (root : Q) (fuel : Nat)
    (h : conflictCheck r p q root fuel = true) : RootConflict r p q root := by
  unfold conflictCheck at h
  obtain ⟨s, hs, hsHit⟩ := List.any_eq_true.mp h
  obtain ⟨b, hb, hbHit⟩ := List.any_eq_true.mp hsHit
  cases hp : p s b with
  | none => simp [hp] at hbHit
  | some mt =>
    cases mt with
    | none => simp [hp] at hbHit
    | some a =>
      cases hq : q s b with
      | none => simp [hp,hq] at hbHit
      | some nt =>
        cases nt with
        | none => simp [hp,hq] at hbHit
        | some c =>
          have hdiff : a.write ≠ c.write ∨ a.right ≠ c.right ∨
             ((a.next ∈ namedReachRows r root fuel ∨
               c.next ∈ namedReachRows r root fuel) ∧ a.next ≠ c.next) := by
            exact of_decide_eq_true (by simpa [hp,hq] using hbHit)
          refine ⟨s, b, a, c, namedReachRows_sound r root fuel s hs, hp, hq, ?_⟩
          rcases hdiff with hwrite | hright | ⟨hmem,hnext⟩
          · exact Or.inl hwrite
          · exact Or.inr (Or.inl hright)
          · refine Or.inr (Or.inr ⟨?_,hnext⟩)
            rcases hmem with ha | hc
            · exact Or.inl (namedReachRows_sound r root fuel a.next ha)
            · exact Or.inr (namedReachRows_sound r root fuel c.next hc)

/-- A boolean certificate entails quotient-disjointness for every finite
    graph depth, even when the reachable-name list is incomplete. -/
theorem conflictCheck_no_common (r p q : PartialTable Q) (root : Q)
    (hpe : Extends r p) (hqf : Extends r q) (fuel : Nat)
    (h : conflictCheck r p q root fuel = true) :
    ¬ ∃ (m : Machine Q) (e f : Perm Q),
        e.backward root = f.backward root ∧
        Compatible p m e ∧ Compatible q m f :=
  root_conflict_no_common r p q root hpe hqf (conflictCheck_sound r p q root fuel h)

/-- The canonical state-renaming operation on a live machine instruction. -/
def renameMove (e : Perm Q) (t : Move Q) : Move Q :=
  { t with next := e.forward t.next }

/-- Source-compatible uses the full two-level partial table convention:
    `none` is an unspecified row, `some none` is a halt. -/
def SourceCompatible (p : PartialTable Q) (m : Machine Q)
    (e : Perm Q) : Prop :=
  ∀ s b out, p s b = some out →
    (m (e.backward s) b).map (renameMove e) = out

theorem source_implies_live (p : PartialTable Q) (m : Machine Q)
    (e : Perm Q) (h : SourceCompatible p m e) : Compatible p m e := by
  intro s b t ht
  have hs : (m (e.backward s) b).map (renameMove e) = some t :=
    h s b (some t) ht
  cases hm : m (e.backward s) b with
  | none => simp [hm] at hs
  | some u =>
      have hu : renameMove e u = t := Option.some.inj (by simpa [hm] using hs)
      refine ⟨u, rfl, ?_, ?_, ?_⟩
      · simpa [renameMove] using congrArg Move.write hu
      · simpa [renameMove] using congrArg Move.right hu
      · simpa [renameMove] using congrArg Move.next hu

theorem anchored_from_forward (e : Perm Q) (root : Q)
    (h : e.forward root = root) : e.backward root = root := by
  calc
    e.backward root = e.backward (e.forward root) := by rw [h]
    _ = root := e.leftInverse root

/-- The relative naming permutation between two quotient witnesses. -/
def relativePerm (e f : Perm Q) : Perm Q where
  forward := fun s => f.forward (e.backward s)
  backward := fun s => e.forward (f.backward s)
  leftInverse := by
    intro s
    simp [f.leftInverse, e.rightInverse]
  rightInverse := by
    intro s
    simp [e.leftInverse, f.rightInverse]

/-- A root-connected name is invariant under the *relative* permutation. -/
theorem relative_fixes_named (r : PartialTable Q) (m : Machine Q)
    (e f : Perm Q) (root : Q)
    (hre : Compatible r m e) (hrf : Compatible r m f)
    (hroot : e.backward root = f.backward root) :
    ∀ s, NamedReach r root s → (relativePerm e f).forward s = s := by
  intro s hs
  have hsame := named_reachable_agreement r m e f root hre hrf hroot s hs
  change f.forward (e.backward s) = s
  rw [hsame]
  exact f.rightInverse s

/-- Comparison after changing the names through a relative permutation.
    Halting and all live transitions are compared uniformly. -/
def RenamingOverlap (p q : PartialTable Q) (g : Perm Q) : Prop :=
  ∀ s b a c, p s b = some a → q (g.forward s) b = some c →
    c = a.map (renameMove g)

/-- Common physical completion implies consistency after *one* relative
    state permutation, not two independent global witnesses. -/
theorem common_implies_renaming_overlap (p q : PartialTable Q)
    (m : Machine Q) (e f : Perm Q)
    (he : SourceCompatible p m e) (hf : SourceCompatible q m f) :
    RenamingOverlap p q (relativePerm e f) := by
  intro s b a c hpa hqc
  let g := relativePerm e f
  have hcell : f.backward (g.forward s) = e.backward s := by
    simp [g, relativePerm, f.leftInverse]
  have heq : (m (e.backward s) b).map (renameMove e) = a := he s b a hpa
  have hfq : (m (e.backward s) b).map (renameMove f) = c := by
    simpa [hcell] using (hf (g.forward s) b c hqc)
  calc
    c = (m (e.backward s) b).map (renameMove f) := hfq.symm
    _ = ((m (e.backward s) b).map (renameMove e)).map (renameMove g) := by
      cases h : m (e.backward s) b with
      | none => simp
      | some u =>
          simp only [Option.map_some]
          cases u with
          | mk w d n =>
              simp [renameMove, g, relativePerm, e.leftInverse]
    _ = a.map (renameMove g) := by rw [heq]

#print axioms relative_fixes_named
#print axioms common_implies_renaming_overlap

/-- A permutation of the six states that fixes A/B/C has only six
    possible restrictions to the remaining names D/E/F. -/
theorem perm_tail_range (g : Perm (Fin 6))
    (h0 : g.forward 0 = 0) (h1 : g.forward 1 = 1)
    (h2 : g.forward 2 = 2) (s : Fin 6) (hs : 3 ≤ s.val) :
    3 ≤ (g.forward s).val := by
  have hinj : Function.Injective g.forward := by
    intro x y hxy
    have h := congrArg g.backward hxy
    simpa [g.leftInverse] using h
  have hn0 : s ≠ 0 := by intro h; subst s; omega
  have hn1 : s ≠ 1 := by intro h; subst s; omega
  have hn2 : s ≠ 2 := by intro h; subst s; omega
  by_cases hlt : (g.forward s).val < 3
  · have hsmall : (g.forward s).val = 0 ∨
        (g.forward s).val = 1 ∨ (g.forward s).val = 2 := by omega
    rcases hsmall with h | h | h
    · have heq : g.forward s = g.forward 0 := by
        rw [h0]; exact Fin.ext h
      exact False.elim (hn0 (hinj heq))
    · have heq : g.forward s = g.forward 1 := by
        rw [h1]; exact Fin.ext h
      exact False.elim (hn1 (hinj heq))
    · have heq : g.forward s = g.forward 2 := by
        rw [h2]; exact Fin.ext h
      exact False.elim (hn2 (hinj heq))
  · omega

theorem six_tail_permutations (g : Perm (Fin 6))
    (h0 : g.forward 0 = 0) (h1 : g.forward 1 = 1)
    (h2 : g.forward 2 = 2) :
    ((g.forward 3).val = 3 ∧ (g.forward 4).val = 4 ∧ (g.forward 5).val = 5) ∨
    ((g.forward 3).val = 3 ∧ (g.forward 4).val = 5 ∧ (g.forward 5).val = 4) ∨
    ((g.forward 3).val = 4 ∧ (g.forward 4).val = 3 ∧ (g.forward 5).val = 5) ∨
    ((g.forward 3).val = 4 ∧ (g.forward 4).val = 5 ∧ (g.forward 5).val = 3) ∨
    ((g.forward 3).val = 5 ∧ (g.forward 4).val = 3 ∧ (g.forward 5).val = 4) ∨
    ((g.forward 3).val = 5 ∧ (g.forward 4).val = 4 ∧ (g.forward 5).val = 3) := by
  have h3 := perm_tail_range g h0 h1 h2 3 (by decide)
  have h4 := perm_tail_range g h0 h1 h2 4 (by decide)
  have h5 := perm_tail_range g h0 h1 h2 5 (by decide)
  have hinj : Function.Injective g.forward := by
    intro x y hxy
    have h := congrArg g.backward hxy
    simpa [g.leftInverse] using h
  have h34 : (g.forward 3).val ≠ (g.forward 4).val := by
    intro h
    have := hinj (Fin.ext h)
    exact (by decide : (3 : Fin 6) ≠ 4) this
  have h35 : (g.forward 3).val ≠ (g.forward 5).val := by
    intro h
    have := hinj (Fin.ext h)
    exact (by decide : (3 : Fin 6) ≠ 5) this
  have h45 : (g.forward 4).val ≠ (g.forward 5).val := by
    intro h
    have := hinj (Fin.ext h)
    exact (by decide : (4 : Fin 6) ≠ 5) this
  have u3 := (g.forward 3).isLt
  have u4 := (g.forward 4).isLt
  have u5 := (g.forward 5).isLt
  omega

#print axioms six_tail_permutations

/-- Six executable tail renamings. These are the only possible relative
    names for a common completion of two Raw11-rooted tables. -/
def tailMap (i j k : Fin 6) (s : Fin 6) : Fin 6 :=
  if s = 3 then i else if s = 4 then j else if s = 5 then k else s

def tail345 : Perm (Fin 6) where
  forward := tailMap 3 4 5
  backward := tailMap 3 4 5
  leftInverse := by decide
  rightInverse := by decide

def tail354 : Perm (Fin 6) where
  forward := tailMap 3 5 4
  backward := tailMap 3 5 4
  leftInverse := by decide
  rightInverse := by decide

def tail435 : Perm (Fin 6) where
  forward := tailMap 4 3 5
  backward := tailMap 4 3 5
  leftInverse := by decide
  rightInverse := by decide

def tail453 : Perm (Fin 6) where
  forward := tailMap 4 5 3
  backward := tailMap 5 3 4
  leftInverse := by decide
  rightInverse := by decide

def tail534 : Perm (Fin 6) where
  forward := tailMap 5 3 4
  backward := tailMap 4 5 3
  leftInverse := by decide
  rightInverse := by decide

def tail543 : Perm (Fin 6) where
  forward := tailMap 5 4 3
  backward := tailMap 5 4 3
  leftInverse := by decide
  rightInverse := by decide

def sixTailPerms : List (Perm (Fin 6)) :=
  [tail345,tail354,tail435,tail453,tail534,tail543]

/-- Every root-preserving six-state permutation whose A/B/C images are
    fixed acts on the remaining states as one of six explicit permutations. -/
theorem tail_forward_of_images (g : Perm (Fin 6))
    (i j k : Fin 6)
    (h0 : g.forward 0 = 0) (h1 : g.forward 1 = 1)
    (h2 : g.forward 2 = 2)
    (h3 : g.forward 3 = i) (h4 : g.forward 4 = j)
    (h5 : g.forward 5 = k) :
    ∀ s, g.forward s = tailMap i j k s := by
  intro s
  have hs : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by
    have hbound := s.isLt
    omega
  rcases hs with h | h | h | h | h | h <;> subst s <;>
    simp [tailMap, h0, h1, h2, h3, h4, h5]

theorem six_tail_forward_cover (g : Perm (Fin 6))
    (h0 : g.forward 0 = 0) (h1 : g.forward 1 = 1)
    (h2 : g.forward 2 = 2) :
    ∃ h ∈ sixTailPerms, ∀ s, g.forward s = h.forward s := by
  rcases six_tail_permutations g h0 h1 h2 with
    h | h | h | h | h | h
  · refine ⟨tail345, by simp [sixTailPerms], ?_⟩
    exact tail_forward_of_images g 3 4 5 h0 h1 h2
      (Fin.ext h.1) (Fin.ext h.2.1) (Fin.ext h.2.2)
  · refine ⟨tail354, by simp [sixTailPerms], ?_⟩
    exact tail_forward_of_images g 3 5 4 h0 h1 h2
      (Fin.ext h.1) (Fin.ext h.2.1) (Fin.ext h.2.2)
  · refine ⟨tail435, by simp [sixTailPerms], ?_⟩
    exact tail_forward_of_images g 4 3 5 h0 h1 h2
      (Fin.ext h.1) (Fin.ext h.2.1) (Fin.ext h.2.2)
  · refine ⟨tail453, by simp [sixTailPerms], ?_⟩
    exact tail_forward_of_images g 4 5 3 h0 h1 h2
      (Fin.ext h.1) (Fin.ext h.2.1) (Fin.ext h.2.2)
  · refine ⟨tail534, by simp [sixTailPerms], ?_⟩
    exact tail_forward_of_images g 5 3 4 h0 h1 h2
      (Fin.ext h.1) (Fin.ext h.2.1) (Fin.ext h.2.2)
  · refine ⟨tail543, by simp [sixTailPerms], ?_⟩
    exact tail_forward_of_images g 5 4 3 h0 h1 h2
      (Fin.ext h.1) (Fin.ext h.2.1) (Fin.ext h.2.2)

#print axioms six_tail_forward_cover

/-- A finite, literal test of overlap under a fixed relative renaming. -/
def overlapCheck (p q : PartialTable (Fin 6)) (g : Perm (Fin 6)) : Bool :=
  ([0,1,2,3,4,5] : List (Fin 6)).all (fun s =>
    ([false,true] : List Bool).all (fun b =>
      match p s b, q (g.forward s) b with
      | some a, some c => decide (c = a.map (renameMove g))
      | _, _ => true))

def sixTailCheck (p q : PartialTable (Fin 6)) : Bool :=
  sixTailPerms.any (fun g => overlapCheck p q g)

theorem renamingOverlap_check_true (p q : PartialTable (Fin 6))
    (g : Perm (Fin 6)) (h : RenamingOverlap p q g) :
    overlapCheck p q g = true := by
  unfold overlapCheck
  apply List.all_eq_true.mpr
  intro s _
  apply List.all_eq_true.mpr
  intro b _
  cases hp : p s b with
  | none => simp [hp]
  | some a =>
      cases hq : q (g.forward s) b with
      | none => simp [hp,hq]
      | some c =>
          have heq := h s b a c hp hq
          simp [hp,hq,heq]

theorem allSixNames_mem (s : Fin 6) :
    s ∈ ([0,1,2,3,4,5] : List (Fin 6)) := by
  have hs : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by
    have bound := s.isLt
    omega
  rcases hs with h | h | h | h | h | h <;> subst s <;> decide

theorem overlapCheck_true_iff (p q : PartialTable (Fin 6))
    (g : Perm (Fin 6)) :
    overlapCheck p q g = true ↔ RenamingOverlap p q g := by
  constructor
  · intro h s b a c ha hc
    have hs : ([false,true] : List Bool).all (fun b =>
      match p s b, q (g.forward s) b with
      | some a, some c => decide (c = a.map (renameMove g))
      | _,_ => true) = true :=
      List.all_eq_true.mp h s (allSixNames_mem s)
    have hb : b ∈ ([false,true] : List Bool) := by cases b <;> simp
    have hcell := List.all_eq_true.mp hs b hb
    exact of_decide_eq_true (by simpa [ha,hc] using hcell)
  · exact renamingOverlap_check_true p q g

theorem renamingOverlap_transport (p q : PartialTable (Fin 6))
    (g h : Perm (Fin 6)) (hforward : ∀ s, g.forward s = h.forward s)
    (hOverlap : RenamingOverlap p q g) : RenamingOverlap p q h := by
  intro s b a c hpa hqc
  have hcG : q (g.forward s) b = some c := by
    simpa [hforward s] using hqc
  have heq := hOverlap s b a c hpa hcG
  have hmap : a.map (renameMove g) = a.map (renameMove h) := by
    cases a with
    | none => rfl
    | some mv =>
        cases mv with
        | mk w d n =>
            simp [renameMove, hforward n]
  exact heq.trans hmap

/-- The reverse direction is constructive: a pair of consistently
    renamed partial tables can be merged into a total physical machine,
    defaulting to a halting instruction at every unconstrained row. -/
def inversePerm (g : Perm Q) : Perm Q where
  forward := g.backward
  backward := g.forward
  leftInverse := g.rightInverse
  rightInverse := g.leftInverse

def identityPerm (Q : Type u) : Perm Q where
  forward := id
  backward := id
  leftInverse := by intro s; rfl
  rightInverse := by intro s; rfl

def mergeMachine (p q : PartialTable Q) (g : Perm Q) : Machine Q :=
  fun s b =>
    match p s b with
    | some out => out
    | none => (q (g.forward s) b).join.map (renameMove (inversePerm g))

theorem merge_first_compatible (p q : PartialTable Q) (g : Perm Q) :
    SourceCompatible p (mergeMachine p q g) (identityPerm Q) := by
  intro s b out hp
  cases out with
  | none => simp [mergeMachine, identityPerm, hp]
  | some mv =>
      cases mv
      simp [mergeMachine, identityPerm, hp, renameMove]

theorem merge_second_compatible (p q : PartialTable Q) (g : Perm Q)
    (hov : RenamingOverlap p q g) :
    SourceCompatible q (mergeMachine p q g) g := by
  intro s b out hq
  have hqc : q (g.forward (g.backward s)) b = some out := by
    simpa [g.rightInverse] using hq
  cases hp : p (g.backward s) b with
  | none =>
    cases out with
    | none => simp [mergeMachine, hp, g.rightInverse, hq, inversePerm]
    | some mv =>
        cases mv
        simp [mergeMachine, hp, g.rightInverse, hq, inversePerm,
          renameMove, g.rightInverse]
  | some a =>
      have hEq := hov (g.backward s) b a out hp hqc
      simpa [mergeMachine, hp] using hEq.symm

#print axioms merge_second_compatible

/-- The six-comparison check is necessary for any pair of quotient cylinders
    extending a root that reaches A, B and C by its defined transitions. -/
theorem sixTailCheck_necessary
    (r p q : PartialTable (Fin 6))
    (hr1 : NamedReach r 0 1) (hr2 : NamedReach r 0 2)
    (hpe : Extends r p) (hqf : Extends r q)
    (m : Machine (Fin 6)) (e f : Perm (Fin 6))
    (he0 : e.forward 0 = 0) (hf0 : f.forward 0 = 0)
    (he : SourceCompatible p m e) (hf : SourceCompatible q m f) :
    sixTailCheck p q = true := by
  have hroot : e.backward 0 = f.backward 0 := by
    rw [anchored_from_forward e 0 he0, anchored_from_forward f 0 hf0]
  have hre : Compatible r m e :=
    compatible_of_extends hpe (source_implies_live p m e he)
  have hrf : Compatible r m f :=
    compatible_of_extends hqf (source_implies_live q m f hf)
  let g := relativePerm e f
  have hfix := relative_fixes_named r m e f 0 hre hrf hroot
  have h0 : g.forward 0 = 0 := hfix 0 NamedReach.root
  have h1 : g.forward 1 = 1 := hfix 1 hr1
  have h2 : g.forward 2 = 2 := hfix 2 hr2
  obtain ⟨h, hh, hforward⟩ := six_tail_forward_cover g h0 h1 h2
  have overlap : RenamingOverlap p q g :=
    common_implies_renaming_overlap p q m e f he hf
  have overlapH := renamingOverlap_transport p q g h hforward overlap
  exact List.any_eq_true.mpr ⟨h, hh, renamingOverlap_check_true p q h overlapH⟩

#print axioms sixTailCheck_necessary

/-- Standard blank-root compatibility, quantified over a relabeling. -/
def QuotientCompatible (p : PartialTable Q) (m : Machine Q)
    (root : Q) : Prop :=
  ∃ e : Perm Q, e.forward root = root ∧ SourceCompatible p m e

theorem sixTail_fixed_root (g : Perm (Fin 6))
    (hg : g ∈ sixTailPerms) : g.forward 0 = 0 := by
  simp only [sixTailPerms, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst g <;> decide

/-- Exact, fully certified six-permutation quotient-overlap decision. The
    *only* parent conditions are rooted reachability of 1 and 2 and the
    two table-extension hypotheses. `true` constructs a common machine;
    `false` rules out every common machine, regardless of relabeling. -/
theorem sixTailCheck_exact
    (r p q : PartialTable (Fin 6))
    (hr1 : NamedReach r 0 1) (hr2 : NamedReach r 0 2)
    (hpe : Extends r p) (hqf : Extends r q) :
    sixTailCheck p q = true ↔
      ∃ m : Machine (Fin 6),
        QuotientCompatible p m 0 ∧ QuotientCompatible q m 0 := by
  constructor
  · intro h
    obtain ⟨g, hg, hcheck⟩ := List.any_eq_true.mp h
    have hov := (overlapCheck_true_iff p q g).mp hcheck
    refine ⟨mergeMachine p q g, ?_, ?_⟩
    · exact ⟨identityPerm (Fin 6), rfl, merge_first_compatible p q g⟩
    · exact ⟨g, sixTail_fixed_root g hg, merge_second_compatible p q g hov⟩
  · rintro ⟨m, ⟨e,he0,he⟩, ⟨f,hf0,hf⟩⟩
    exact sixTailCheck_necessary r p q hr1 hr2 hpe hqf m e f he0 hf0 he hf

#print axioms sixTailCheck_exact

/-- Source-faithful complete exclusion theorem: no machine, including
    halting completions and all permutations of unused states, belongs to
    both cylinders when the finite check succeeds. -/
theorem quotient_cylinders_disjoint
    (r p q : PartialTable Q) (root : Q)
    (hpe : Extends r p) (hqf : Extends r q) (fuel : Nat)
    (hconf : conflictCheck r p q root fuel = true) :
    ¬ ∃ m : Machine Q, QuotientCompatible p m root ∧ QuotientCompatible q m root := by
  rintro ⟨m, ⟨e, he0, he⟩, ⟨f, hf0, hf⟩⟩
  have hroot : e.backward root = f.backward root := by
    rw [anchored_from_forward e root he0, anchored_from_forward f root hf0]
  exact (conflictCheck_no_common r p q root hpe hqf fuel hconf)
    ⟨m, e, f, hroot, source_implies_live p m e he, source_implies_live q m f hf⟩

#print axioms quotient_cylinders_disjoint

/-- Extending an undefined transition preserves every old source row. -/
def setUndefined (r : PartialTable Q) (s : Q) (b : Bool)
    (mv : Move Q) : PartialTable Q :=
  fun s' b' => if s' = s ∧ b' = b then some (some mv) else r s' b'

theorem setUndefined_extends (r : PartialTable Q) (s : Q) (b : Bool)
    (mv : Move Q) (hnone : r s b = none) :
    Extends r (setUndefined r s b mv) := by
  intro s' b' t ht
  by_cases h : s' = s ∧ b' = b
  · obtain ⟨rfl, rfl⟩ := h
    simp [hnone] at ht
  · simpa [setUndefined,h] using ht

/-- Concrete Raw11 3-state root skeleton, shown in source encoding
    1RB---_1RC---_0LA---_------_------_------. -/
def raw11Parent : PartialTable (Fin 6) :=
  fun s b =>
    if s = 0 ∧ b = false then some (some ⟨true, true, 1⟩)
    else if s = 1 ∧ b = false then some (some ⟨true, true, 2⟩)
    else if s = 2 ∧ b = false then some (some ⟨false, false, 0⟩)
    else none

/-- Exact finite closure of the three named states A/B/C. -/
theorem raw11ParentClosed : closureCheck raw11Parent 0 2 = true := by
  decide +kernel

theorem raw11NamedReachExact (s : Fin 6) :
    NamedReach raw11Parent 0 s ↔ s ∈ namedReachRows raw11Parent 0 2 :=
  namedReachRows_exact raw11Parent 0 2 raw11ParentClosed s

#print axioms raw11ParentClosed

/-- A1=1LC and A1=1LD differ by an *anchored vs fresh* target name. -/
def raw11Q0A : PartialTable (Fin 6) :=
  setUndefined raw11Parent 0 true ⟨true, false, 2⟩
def raw11Q0D : PartialTable (Fin 6) :=
  setUndefined raw11Parent 0 true ⟨true, false, 3⟩

theorem raw11Q0A_extends : Extends raw11Parent raw11Q0A :=
  setUndefined_extends raw11Parent 0 true ⟨true,false,2⟩ (by decide)

theorem raw11Q0D_extends : Extends raw11Parent raw11Q0D :=
  setUndefined_extends raw11Parent 0 true ⟨true,false,3⟩ (by decide)

theorem raw11Reach1 : NamedReach raw11Parent 0 1 :=
  NamedReach.step (s := (0 : Fin 6)) (t := ⟨true,true,1⟩)
    NamedReach.root false (by decide)

theorem raw11Reach2 : NamedReach raw11Parent 0 2 :=
  NamedReach.step (s := (1 : Fin 6)) (t := ⟨true,true,2⟩)
    raw11Reach1 false (by decide)

/-- Exact overlap criterion for *any two* partial six-state machines extending
    this Raw11 parent. All six possible relative D/E/F permutations are checked. -/
theorem raw11_sixTailCheck_exact (p q : PartialTable (Fin 6))
    (hp : Extends raw11Parent p) (hq : Extends raw11Parent q) :
    sixTailCheck p q = true ↔
      ∃ m : Machine (Fin 6),
        QuotientCompatible p m 0 ∧ QuotientCompatible q m 0 :=
  sixTailCheck_exact raw11Parent p q raw11Reach1 raw11Reach2 hp hq

/-- This pair differs by rooted C versus fresh D; no permutation can repair
    its A1 collision. -/
theorem raw11Q0CD_sixTailFalse :
    sixTailCheck raw11Q0A raw11Q0D = false := by decide +kernel

theorem raw11Q0CD_no_common_quotient :
    ¬ ∃ m : Machine (Fin 6),
      QuotientCompatible raw11Q0A m 0 ∧ QuotientCompatible raw11Q0D m 0 := by
  intro hm
  have hTrue := (raw11_sixTailCheck_exact raw11Q0A raw11Q0D
    raw11Q0A_extends raw11Q0D_extends).mpr hm
  rw [raw11Q0CD_sixTailFalse] at hTrue
  contradiction

#print axioms raw11_sixTailCheck_exact
#print axioms raw11Q0CD_no_common_quotient

theorem raw11Q0CD_collision :
    conflictCheck raw11Parent raw11Q0A raw11Q0D 0 2 = true := by
  decide +kernel

theorem raw11Q0CD_disjoint :
    ¬ ∃ (m : Machine (Fin 6)) (e f : Perm (Fin 6)),
        e.backward 0 = f.backward 0 ∧
        Compatible raw11Q0A m e ∧ Compatible raw11Q0D m f :=
  conflictCheck_no_common raw11Parent raw11Q0A raw11Q0D 0
    raw11Q0A_extends raw11Q0D_extends 2 raw11Q0CD_collision

#print axioms raw11Q0CD_disjoint
#print axioms conflictCheck_sound
#print axioms conflictCheck_no_common
#print axioms named_reachable_agreement
#print axioms rooted_slot_agrees
#print axioms root_conflict_no_common
end RootedLiveQuotient