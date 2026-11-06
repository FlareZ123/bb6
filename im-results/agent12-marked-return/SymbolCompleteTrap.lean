import RayFinite
import FrontierMass

namespace BB6Coverage

/-- A finite-state trap on *both* read symbols. Tape contents and head
    motion are unrestricted. All transitions in the marked state set
    are ordinary and retain membership in that set. -/
def BothSymbolClosed (m : Machine) (states : Fin 6 → Prop) : Prop :=
  ∀ s, states s → ∀ bit, ∃ mv : Move,
    m (s, bit) = some mv ∧ states mv.next

def PartialBothSymbolClosed (p : PartialMachine) (states : Fin 6 → Prop) : Prop :=
  ∀ s, states s → ∀ bit, ∃ mv : Move,
    p (s, bit) = some (some mv) ∧ states mv.next

private theorem bothSymbolRun (m : Machine) (states : Fin 6 → Prop)
    (c : Config) (hstate : states c.state)
    (hclosed : BothSymbolClosed m states) (n : Nat) :
    ∃ d, run m n c = some d ∧ states d.state := by
  induction n with
  | zero => exact ⟨c, rfl, hstate⟩
  | succ n ih =>
      obtain ⟨d, hd, hs⟩ := ih
      obtain ⟨mv, hm, hn⟩ := hclosed d.state hs (d.tape d.head)
      refine ⟨applyMove d mv, ?_, hn⟩
      simp [run, hd, rawStep, readSlot, hm]

private theorem bothSymbolRun_add (m : Machine) (c : Config) (n k : Nat) :
    run m (n+k) c = (run m n c).bind (run m k) := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
      rw [Nat.add_succ, run, ih]
      cases h : run m n c with
      | none => simp
      | some d => rfl

/-- Entering an all-symbol control trap on a genuine blank prefix
    prevents a halt at *every* future attempted transition. -/
theorem bothSymbolPrefix_never (m : Machine) (states : Fin 6 → Prop)
    (k : Nat) (c : Config) (hentry : run m k blank = some c)
    (hstate : states c.state) (hclosed : BothSymbolClosed m states) :
    NeverHalts m := by
  intro n
  by_cases hle : n ≤ k
  · cases hn : run m n blank with
    | none =>
        obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
        have hnone : run m k blank = none := by
          rw [ht, bothSymbolRun_add, hn]
          rfl
        rw [hnone] at hentry
        contradiction
    | some _ => rfl
  · have hge : k ≤ n := by omega
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hge
    obtain ⟨d, hd, _⟩ := bothSymbolRun m states c hstate hclosed t
    rw [ht, bothSymbolRun_add, hentry]
    simp [hd]

/-- A sparse original-source certificate: the finite physical tape prefix
    is checked exactly, and every future read of either bit is assigned
    a nonhalting transition inside the closed set. -/
theorem bothSymbolPrefix_cover (p : PartialMachine) (states : Fin 6 → Prop)
    (k : Nat) (c : FinRayCfg) (bound : Nat)
    (hentry : finitePartialRun p k finiteBlank = some c)
    (hstate : states c.state)
    (hclosed : PartialBothSymbolClosed p states) :
    Cover (DecidedBelow bound) p := by
  apply Cover.leaf
  intro m hm
  left
  have he : run m k blank = some (embedFinRay c) := by
    simpa only [embedFinRay_blank] using
      finitePartialRun_sound p m hm finiteBlank c k hentry
  apply bothSymbolPrefix_never m states k (embedFinRay c) he hstate
  intro s hs bit
  obtain ⟨mv, hp, hn⟩ := hclosed s hs bit
  exact ⟨mv, hm (s, bit) (some mv) hp, hn⟩

def bothSymbolStepCheck (p : PartialMachine)
    (mask : Fin 6 → Bool) (s : Fin 6) (bit : Bool) : Bool :=
  match p (s, bit) with
  | some (some mv) => mask mv.next
  | _ => false

def bothSymbolClosedCheck (p : PartialMachine)
    (mask : Fin 6 → Bool) : Bool :=
  (List.finRange 6).all (fun s =>
    if mask s then
      bothSymbolStepCheck p mask s false &&
        bothSymbolStepCheck p mask s true
    else true)

theorem bothSymbolClosedCheck_sound (p : PartialMachine)
    (mask : Fin 6 → Bool)
    (h : bothSymbolClosedCheck p mask = true) :
    PartialBothSymbolClosed p (fun s => mask s = true) := by
  intro s hs bit
  have hall := (List.all_eq_true.mp h) s (List.mem_finRange s)
  have hboth :
      (bothSymbolStepCheck p mask s false &&
        bothSymbolStepCheck p mask s true) = true := by
    simpa [bothSymbolClosedCheck, hs] using hall
  have hstep : bothSymbolStepCheck p mask s bit = true := by
    cases bit with
    | false => exact ((Bool.and_eq_true _ _).mp hboth).1
    | true => exact ((Bool.and_eq_true _ _).mp hboth).2
  cases hp : p (s, bit) with
  | none => simp [bothSymbolStepCheck, hp] at hstep
  | some outcome =>
      cases outcome with
      | none => simp [bothSymbolStepCheck, hp] at hstep
      | some mv =>
          exact ⟨mv, rfl, by simpa [bothSymbolStepCheck, hp] using hstep⟩

def bothSymbolPrefixCheck (p : PartialMachine) (n : Nat)
    (mask : Fin 6 → Bool) : Bool :=
  match finitePartialRun p n finiteBlank with
  | none => false
  | some c => mask c.state && bothSymbolClosedCheck p mask

theorem bothSymbolPrefixCheck_sound (p : PartialMachine) (n : Nat)
    (mask : Fin 6 → Bool) (bound : Nat)
    (h : bothSymbolPrefixCheck p n mask = true) :
    Cover (DecidedBelow bound) p := by
  cases he : finitePartialRun p n finiteBlank with
  | none => simp [bothSymbolPrefixCheck, he] at h
  | some c =>
      have hp : mask c.state = true ∧
          bothSymbolClosedCheck p mask = true := by
        simpa only [bothSymbolPrefixCheck, he, Bool.and_eq_true] using h
      exact bothSymbolPrefix_cover p (fun s => mask s = true) n c bound
        he hp.1 (bothSymbolClosedCheck_sound p mask hp.2)

/-- Enumerate at most 64 state masks and physically verified prefix lengths.
    Accepted certificates are global statements about all completions. -/
def bothSymbolFiniteOracle (p : PartialMachine) (maxSteps : Nat) : Bool :=
  (List.range (maxSteps + 1)).any (fun n =>
    (List.range 64).any (fun u =>
      bothSymbolPrefixCheck p n (fun s => u.testBit s.val)))

theorem bothSymbolFiniteOracle_sound (p : PartialMachine)
    (maxSteps bound : Nat)
    (h : bothSymbolFiniteOracle p maxSteps = true) :
    Cover (DecidedBelow bound) p := by
  obtain ⟨n, _, hn⟩ := List.any_eq_true.mp h
  obtain ⟨u, _, hu⟩ := List.any_eq_true.mp hn
  exact bothSymbolPrefixCheck_sound p n
    (fun s => u.testBit s.val) bound hu

/-- New source-exact family: A writes a marked 1 and enters q; q/0
    reverses, and q/1 may move either direction, provided both stay q. -/
def markedSinkTable (q : Fin 6)
    (dir w0 w1 readOneDir : Bool) : PartialMachine :=
  fun slot =>
    if slot = initialSlot then some (some ⟨true, dir, q⟩)
    else if slot = (q, false) then some (some ⟨w0, !dir, q⟩)
    else if slot = (q, true) then some (some ⟨w1, readOneDir, q⟩)
    else none

def markedSinkParams : List (Fin 6 × Bool × Bool × Bool × Bool) :=
  ((List.finRange 6).filter (fun q => q != 0)).flatMap (fun q =>
    [true, false].flatMap (fun dir =>
      [true, false].flatMap (fun w0 =>
        [true, false].flatMap (fun w1 =>
          [true, false].map (fun readOneDir =>
            (q, dir, w0, w1, readOneDir))))))

def markedSinkCases : List PartialMachine :=
  markedSinkParams.map (fun (q, dir, w0, w1, readOneDir) =>
    markedSinkTable q dir w0 w1 readOneDir)

theorem markedSinkParams_length : markedSinkParams.length = 80 := by decide
theorem markedSinkParams_nodup : markedSinkParams.Nodup := by decide

theorem markedSinkParams_source :
    markedSinkParams.all (fun (q, dir, w0, w1, readOneDir) =>
      bothSymbolPrefixCheck
        (markedSinkTable q dir w0 w1 readOneDir)
        1 (fun s => s == q)) = true := by
  decide

theorem markedSink_source_cover (q : Fin 6)
    (dir w0 w1 readOneDir : Bool) (bound : Nat)
    (h : (q, dir, w0, w1, readOneDir) ∈ markedSinkParams) :
    Cover (DecidedBelow bound)
      (markedSinkTable q dir w0 w1 readOneDir) :=
  bothSymbolPrefixCheck_sound _ 1 (fun s => s == q) bound
    ((List.all_eq_true.mp markedSinkParams_source) _ h)

theorem markedSinkCases_mass :
    markedSinkCases.all (fun p => decide (cylinderMass p = 25^9)) = true := by
  decide

theorem markedSinkCase_mass (p : PartialMachine)
    (h : p ∈ markedSinkCases) : cylinderMass p = 25^9 :=
  of_decide_eq_true ((List.all_eq_true.mp markedSinkCases_mass) p h)

/-- Pairwise disjointness of all eighty original-source cylinders. -/
theorem markedSink_unique (m : Machine) (q q' : Fin 6)
    (dir dir' w0 w0' w1 w1' e e' : Bool)
    (hq : q ≠ 0) (_hq' : q' ≠ 0)
    (h : compatible (markedSinkTable q dir w0 w1 e) m)
    (h' : compatible (markedSinkTable q' dir' w0' w1' e') m) :
    (q, dir, w0, w1, e) = (q', dir', w0', w1', e') := by
  have hA : m initialSlot = some ⟨true, dir, q⟩ :=
    h initialSlot _ (by simp [markedSinkTable])
  have hA' : m initialSlot = some ⟨true, dir', q'⟩ :=
    h' initialSlot _ (by simp [markedSinkTable])
  have heq : (⟨true, dir, q⟩ : Move) = ⟨true, dir', q'⟩ :=
    Option.some.inj (hA.symm.trans hA')
  have hdir : dir = dir' := congrArg Move.right heq
  have hstate : q = q' := congrArg Move.next heq
  subst dir'
  subst q'
  have hs0 : (q, false) ≠ initialSlot := by
    simp [initialSlot, hq]
  have hs1 : (q, true) ≠ initialSlot := by
    simp [initialSlot]
  have h0 : m (q, false) = some ⟨w0, !dir, q⟩ :=
    h (q, false) _ (by simp [markedSinkTable, hs0])
  have h0' : m (q, false) = some ⟨w0', !dir, q⟩ :=
    h' (q, false) _ (by simp [markedSinkTable, hs0])
  have hw0 : w0 = w0' :=
    congrArg Move.write (Option.some.inj (h0.symm.trans h0'))
  have h1 : m (q, true) = some ⟨w1, e, q⟩ :=
    h (q, true) _ (by simp [markedSinkTable, hs1])
  have h1' : m (q, true) = some ⟨w1', e', q⟩ :=
    h' (q, true) _ (by simp [markedSinkTable, hs1])
  have hmv1 : (⟨w1, e, q⟩ : Move) = ⟨w1', e', q⟩ :=
    Option.some.inj (h1.symm.trans h1')
  have hw1 : w1 = w1' := congrArg Move.write hmv1
  have he : e = e' := congrArg Move.right hmv1
  simp [hw0, hw1, he]

#print axioms bothSymbolPrefix_never
#print axioms bothSymbolPrefix_cover
#print axioms bothSymbolPrefixCheck_sound
#print axioms bothSymbolFiniteOracle_sound
#print axioms markedSinkParams_source
#print axioms markedSink_source_cover
#print axioms markedSinkCases_mass
#print axioms markedSink_unique

end BB6Coverage
