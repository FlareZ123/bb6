import TNFPilot
import SideCycle
import R3Sweep
import R5ZeroSweep

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6.Agent50CryptidSiblings
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6Coverage.Agent50SideCycle

inductive SiblingWitness where
  | last (n : Nat)
  | cycle (entry period : Nat) (right : Bool) (boundary : Int)
  | growth
  | r5Growth (write : Bool)
  | known

structure SiblingSpec where
  path : List PathEntry
  hole : Slot
  splitAt : Nat
  lastSlot : Slot
  bound : Nat
  special : Move
  witness : Move → SiblingWitness

def SiblingSpec.parent (s : SiblingSpec) : PartialMachine :=
  (pathEnd root 2 s.path).1

def SiblingSpec.child (s : SiblingSpec) (mv : Move) : PartialMachine :=
  refine s.parent s.hole (some mv)

def partialEq (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun i => [false,true].all fun b =>
    decide (p (i,b) = q (i,b))

theorem partialEq_sound (p q : PartialMachine) (h : partialEq p q = true) : p = q := by
  funext slot
  rcases slot with ⟨i,b⟩
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  have hb : b ∈ [false,true] := by cases b <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp hi b hb)

def siblingOK (s : SiblingSpec) (mv : Move) : Bool :=
  let p := s.child mv
  match s.witness mv with
  | .last n =>
    decide ((knownRun p n).map readSlot = some s.lastSlot) &&
      (decide (p s.lastSlot = none) &&
        (restOK p s.lastSlot && weightOK p s.lastSlot n s.bound))
  | .cycle entry period right boundary =>
    decide (0 < period) && finiteSideCycleCheck p entry period right boundary
  | .growth => partialEq p BB6Coverage.Agent50R3Sweep.r3Table
  | .r5Growth w => partialEq p (BB6Coverage.Agent50R5Sweep.table w)
  | .known => decide (mv = s.special)

def siblingsOK (s : SiblingSpec) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun w =>
    [false,true].all fun r => siblingOK s ⟨w,r,q⟩

structure ValidSpec (s : SiblingSpec) : Prop where
  pathCheck : pathOK root 2 s.path = true
  cutCheck : (pathEnd root 2 s.path).2 = 6
  rootCheck : s.parent initialSlot = some (some ⟨true,true,1⟩)
  queryCheck : (knownRun s.parent s.splitAt).map readSlot = some s.hole
  holeCheck : s.parent s.hole = none
  weightCheck : weightOK s.parent s.hole s.splitAt s.bound = true
  childrenCheck : siblingsOK s = true

theorem spec_reachable (s : SiblingSpec) (v : ValidSpec s) :
    FirstHolePath s.parent 6 := by
  have h := pathOK_sound root 2 s.path FirstHolePath.root v.pathCheck
  rw [v.cutCheck] at h
  exact h

theorem spec_nohalt (s : SiblingSpec) : weightedTNFNoAssignedHalt s.parent :=
  pathEnd_nohalt root 2 s.path firstOneCylinder_no_assigned_halt

theorem sibling_checked (s : SiblingSpec) (v : ValidSpec s) (mv : Move) :
    siblingOK s mv = true := by
  rcases mv with ⟨w,r,q⟩
  have hq := List.all_eq_true.mp v.childrenCheck q (List.mem_finRange q)
  have hw : w ∈ [false,true] := by cases w <;> simp
  have hr : r ∈ [false,true] := by cases r <;> simp
  exact List.all_eq_true.mp (List.all_eq_true.mp hq w hw) r hr

def lastCertAt (p : PartialMachine) (n : Nat) (hole : Slot) (B : Nat)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hread : (knownRun p n).map readSlot = some hole)
    (hh : p hole = none) (hrest : restOK p hole = true)
    (hw : weightOK p hole n B = true) :
    WeightedTNFCertificate B p 6 := by
  cases hr : knownRun p n with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = hole := by simpa [hr] using hread
    exact .lastHole hf (support6 p) (by decide) hr
      (by simpa [hs] using hh)
      (by simpa [hs] using restOK_sound p hole hrest)
      (by simpa [hs] using weightOK_sound p hole n B hw)

def siblingCert (s : SiblingSpec) (v : ValidSpec s)
    (specialCert : WeightedTNFCertificate s.bound (s.child s.special) 6)
    (mv : Move) : WeightedTNFCertificate s.bound (s.child mv) 6 := by
  have hc := sibling_checked s v mv
  have hr : s.child mv initialSlot = some (some ⟨true,true,1⟩) :=
    refine_preserves_firstOne s.parent s.hole (some mv) v.holeCheck v.rootCheck
  have hno : weightedTNFNoAssignedHalt (s.child mv) :=
    weightedTNFNoAssignedHalt_refine s.parent s.hole mv (spec_nohalt s)
  cases he : s.witness mv with
  | last n =>
    have h : ((knownRun (s.child mv) n).map readSlot = some s.lastSlot) ∧
        s.child mv s.lastSlot = none ∧ restOK (s.child mv) s.lastSlot = true ∧
        weightOK (s.child mv) s.lastSlot n s.bound = true := by
      simpa only [siblingOK, he, Bool.and_eq_true, decide_eq_true_eq] using hc
    exact lastCertAt _ n s.lastSlot s.bound hr h.1 h.2.1 h.2.2.1 h.2.2.2
  | cycle entry period right boundary =>
    have h : 0 < period ∧
        finiteSideCycleCheck (s.child mv) entry period right boundary = true := by
      simpa only [siblingOK,he,Bool.and_eq_true,decide_eq_true_eq] using hc
    exact .nonhalt hr (support6 _) hno
      (finiteSideCycleCheck_sound _ entry period right boundary h.1 h.2)
  | growth =>
    have h : partialEq (s.child mv) BB6Coverage.Agent50R3Sweep.r3Table = true := by
      simpa only [siblingOK,he] using hc
    have heq := partialEq_sound _ _ h
    exact .nonhalt hr (support6 _) hno (by
      rw [heq]
      exact BB6Coverage.Agent50R3Sweep.r3_never)
  | r5Growth w =>
    have h : partialEq (s.child mv) (BB6Coverage.Agent50R5Sweep.table w) = true := by
      simpa only [siblingOK,he] using hc
    have heq := partialEq_sound _ _ h
    exact .nonhalt hr (support6 _) hno (by
      rw [heq]
      cases w
      · exact BB6Coverage.Agent50R5ZeroSweep.never_zero
      · exact BB6Coverage.Agent50R5Sweep.never_one)
  | known =>
    have h : mv = s.special := by
      simpa only [siblingOK,he,decide_eq_true_eq] using hc
    subst mv
    exact specialCert

/-- A real expanded normalized tree; only the explicitly designated existing
    hard leaf needs a supplied certificate. Every other ordinary child and
    the halt sibling are checked by finite observations. -/
def assemble (s : SiblingSpec) (v : ValidSpec s)
    (specialCert : WeightedTNFCertificate s.bound (s.child s.special) 6) :
    WeightedTNFCertificate s.bound s.parent 6 := by
  have hread := v.queryCheck
  cases hr : knownRun s.parent s.splitAt with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = s.hole := by simpa [hr] using hread
    refine .expand v.rootCheck (support6 _) (by decide) (spec_nohalt s) hr
      (by simpa [hs] using v.holeCheck)
      (by simpa [hs] using weightOK_sound s.parent s.hole s.splitAt s.bound v.weightCheck) ?_ ?_
    · intro mv _
      simpa only [hs,SiblingSpec.child] using siblingCert s v specialCert mv
    · intro q hq _ _
      have hlt := q.isLt
      omega

def r2 : SiblingSpec where
  path :=
    [(1,(1,false),⟨false,true,2⟩), (2,(2,false),⟨true,false,0⟩),
     (4,(1,true),⟨false,false,3⟩), (5,(3,true),⟨true,false,3⟩),
     (7,(3,false),⟨true,false,4⟩), (8,(4,false),⟨true,false,1⟩),
     (10,(2,true),⟨true,true,5⟩), (11,(5,true),⟨true,true,0⟩),
     (12,(0,true),⟨false,true,0⟩)]
  hole := (4,true)
  splitAt := 35
  lastSlot := (5,false)
  bound := 471
  special := ⟨true,true,4⟩
  witness := fun mv =>
    match mv.write,mv.right,mv.next.val with
    | false,false,0 => .cycle 23 15 false 0
    | false,false,1 => .last 117
    | false,false,2 => .last 37
    | false,false,3 => .cycle 24 12 false 0
    | false,false,4 => .last 40
    | false,false,5 => .cycle 20 30 false 2
    | false,true,0 => .cycle 132 61 true 3
    | false,true,1 => .last 48
    | false,true,2 => .cycle 20 31 false 2
    | false,true,3 => .cycle 20 45 false 2
    | false,true,4 => .cycle 8 30 true (-5)
    | false,true,5 => .cycle 95 61 true (-1)
    | true,false,0 => .cycle 0 81 true (-5)
    | true,false,1 => .last 470
    | true,false,2 => .cycle 20 22 false 2
    | true,false,3 => .cycle 20 40 false 2
    | true,false,4 => .cycle 22 37 false 2
    | true,false,5 => .last 111
    | true,true,0 => .cycle 20 20 false 2
    | true,true,1 => .cycle 20 28 false 2
    | true,true,2 => .cycle 1034 12 true 20
    | true,true,3 => .cycle 19 44 false 3
    | true,true,4 => .known
    | true,true,5 => .cycle 93 67 true (-3)
    | _,_,_ => .known

def r6 : SiblingSpec where
  path :=
    [(1,(1,false),⟨true,true,2⟩), (2,(2,false),⟨false,false,3⟩),
     (3,(3,true),⟨true,false,4⟩), (4,(4,true),⟨true,false,5⟩),
     (5,(5,false),⟨true,false,2⟩), (7,(3,false),⟨true,true,5⟩),
     (9,(2,true),⟨false,true,0⟩), (10,(0,true),⟨true,true,0⟩),
     (19,(5,true),⟨false,false,5⟩)]
  hole := (1,true)
  splitAt := 62
  lastSlot := (4,false)
  bound := 582
  special := ⟨true,false,1⟩
  witness := fun mv =>
    match mv.write,mv.right,mv.next.val with
    | false,false,0 => .cycle 47 45 true (-1)
    | false,false,1 => .cycle 65 30 false 2
    | false,false,2 => .last 75
    | false,false,3 => .cycle 46 31 true (-2)
    | false,false,4 => .cycle 164 61 false (-4)
    | false,false,5 => .cycle 82 61 false (-1)
    | false,true,0 => .cycle 51 12 true 1
    | false,true,1 => .last 67
    | false,true,2 => .last 144
    | false,true,3 => .last 64
    | false,true,4 => .cycle 46 30 true (-2)
    | false,true,5 => .cycle 50 15 true 1
    | true,false,0 => .cycle 47 44 true (-1)
    | true,false,1 => .known
    | true,false,2 => .cycle 46 28 true (-2)
    | true,false,3 => .last 581
    | true,false,4 => .cycle 160 67 false (-2)
    | true,false,5 => .cycle 46 20 true (-2)
    | true,true,0 => .cycle 47 40 true (-1)
    | true,true,1 => .cycle 49 37 true (-1)
    | true,true,2 => .last 363
    | true,true,3 => .cycle 46 22 true (-2)
    | true,true,4 => .last 104
    | true,true,5 => .cycle 64 96 false 4
    | _,_,_ => .known

def r3 : SiblingSpec where
  path :=
    [(1,(1,false),⟨false,true,2⟩), (2,(2,false),⟨true,false,3⟩),
     (3,(3,false),⟨true,false,1⟩), (4,(1,true),⟨false,false,4⟩),
     (5,(4,false),⟨true,false,3⟩), (8,(2,true),⟨true,true,5⟩),
     (9,(5,true),⟨true,true,0⟩), (12,(4,true),⟨true,false,4⟩),
     (20,(0,true),⟨false,true,0⟩)]
  hole := (3,true)
  splitAt := 38
  lastSlot := (5,false)
  bound := 1768
  special := ⟨true,true,3⟩
  witness := fun mv =>
    match mv.write,mv.right,mv.next.val with
    | false,false,0 => .cycle 45 15 false (-2)
    | false,false,1 => .last 51
    | false,false,2 => .last 40
    | false,false,3 => .last 58
    | false,false,4 => .cycle 39 12 false (-1)
    | false,false,5 => .cycle 43 30 false (-1)
    | false,true,0 => .last 260
    | false,true,1 => .last 70
    | false,true,2 => .last 40
    | false,true,3 => .cycle 27 13 true (-2)
    | false,true,4 => .cycle 37 45 false 1
    | false,true,5 => .last 1767
    | true,false,0 => .cycle 0 60 true (-5)
    | true,false,1 => .growth
    | true,false,2 => .cycle 56 22 false 1
    | true,false,3 => .cycle 37 37 false 1
    | true,false,4 => .cycle 96 40 false (-2)
    | true,false,5 => .last 106
    | true,true,0 => .cycle 52 20 false 1
    | true,true,1 => .cycle 41 28 false (-1)
    | true,true,2 => .last 40
    | true,true,3 => .known
    | true,true,4 => .cycle 102 44 false (-2)
    | true,true,5 => .cycle 99 102 true (-7)
    | _,_,_ => .known

theorem r3_valid : ValidSpec r3 := by
  constructor <;> decide

theorem r3_reachable : FirstHolePath r3.parent 6 := spec_reachable r3 r3_valid

def r5 : SiblingSpec where
  path :=
    [(1,(1,false),⟨false,false,2⟩), (2,(2,true),⟨true,false,3⟩),
     (3,(3,false),⟨false,false,1⟩), (5,(2,false),⟨true,true,2⟩),
     (9,(3,true),⟨true,false,4⟩), (10,(4,true),⟨false,true,2⟩),
     (13,(1,true),⟨false,true,0⟩), (16,(0,true),⟨true,true,0⟩),
     (21,(4,false),⟨true,false,5⟩)]
  hole := (5,true)
  splitAt := 22
  lastSlot := (5,false)
  bound := 28
  special := ⟨false,false,3⟩
  witness := fun mv =>
    match mv.write,mv.right,mv.next.val with
    | false,false,0 => .cycle 18 33 false 3
    | false,false,1 => .cycle 8 32 true (-4)
    | false,false,2 => .cycle 148 42 true (-2)
    | false,false,3 => .known
    | false,false,4 => .last 24
    | false,false,5 => .last 23
    | false,true,0 => .cycle 8 20 true (-3)
    | false,true,1 => .r5Growth false
    | false,true,2 => .cycle 8 34 true (-4)
    | false,true,3 => .last 25
    | false,true,4 => .cycle 178 46 true (-2)
    | false,true,5 => .last 26
    | true,false,0 => .cycle 8 22 true (-3)
    | true,false,1 => .cycle 95 60 true (-1)
    | true,false,2 => .last 27
    | true,false,3 => .cycle 124 36 true (-2)
    | true,false,4 => .last 24
    | true,false,5 => .last 23
    | true,true,0 => .cycle 8 20 true (-3)
    | true,true,1 => .r5Growth true
    | true,true,2 => .last 26
    | true,true,3 => .cycle 8 36 true (-4)
    | true,true,4 => .cycle 10 13 true (-3)
    | true,true,5 => .last 26
    | _,_,_ => .known

theorem r5_valid : ValidSpec r5 := by
  constructor <;> decide

theorem r5_reachable : FirstHolePath r5.parent 6 := spec_reachable r5 r5_valid

theorem r2_valid : ValidSpec r2 := by
  constructor <;> decide

theorem r6_valid : ValidSpec r6 := by
  constructor <;> decide

theorem r2_reachable : FirstHolePath r2.parent 6 := spec_reachable r2 r2_valid
theorem r6_reachable : FirstHolePath r6.parent 6 := spec_reachable r6 r6_valid

theorem attain_last (s : SiblingSpec) (v : ValidSpec s) (mv : Move) (n : Nat)
    (hw : s.witness mv = .last n) :
    ∃ m, compatible s.parent m ∧ HaltsAfter m n := by
  have hc := sibling_checked s v mv
  have h : ((knownRun (s.child mv) n).map readSlot = some s.lastSlot) ∧
      s.child mv s.lastSlot = none ∧ restOK (s.child mv) s.lastSlot = true ∧
      weightOK (s.child mv) s.lastSlot n s.bound = true := by
    simpa only [siblingOK, hw, Bool.and_eq_true, decide_eq_true_eq] using hc
  let m := weightedTNFDefaultCompletion (refine (s.child mv) s.lastSlot none)
  have hm : compatible (refine (s.child mv) s.lastSlot none) m :=
    weightedTNFDefaultCompletion_compatible _
  have hmp : compatible (s.child mv) m :=
    refine_preserves_compat (s.child mv) m s.lastSlot none h.2.1 hm
  have hp : compatible s.parent m :=
    refine_preserves_compat s.parent m s.hole (some mv) v.holeCheck hmp
  refine ⟨m,hp,?_⟩
  cases hrun : knownRun (s.child mv) n with
  | none => simp [hrun] at h
  | some c =>
    have hs : readSlot c = s.lastSlot := by simpa [hrun] using h.1
    apply first_hole_halts (s.child mv) n c hrun
    · simpa [hs] using h.2.1
    · simpa [hs] using hm

theorem r2_attained : ∃ m, compatible r2.parent m ∧ HaltsAfter m 470 :=
  attain_last r2 r2_valid ⟨true,false,1⟩ 470 rfl

theorem r3_attained : ∃ m, compatible r3.parent m ∧ HaltsAfter m 1767 :=
  attain_last r3 r3_valid ⟨false,true,5⟩ 1767 rfl

theorem r5_attained : ∃ m, compatible r5.parent m ∧ HaltsAfter m 27 :=
  attain_last r5 r5_valid ⟨true,false,2⟩ 27 rfl

theorem r6_attained : ∃ m, compatible r6.parent m ∧ HaltsAfter m 581 :=
  attain_last r6 r6_valid ⟨true,false,3⟩ 581 rfl

theorem exact_from_attained (s : SiblingSpec) (v : ValidSpec s)
    (cert : WeightedTNFCertificate s.bound s.parent 6)
    (n : Nat) (hn : n+1 = s.bound)
    (ha : ∃ m, compatible s.parent m ∧ HaltsAfter m n) (B : Nat) :
    (∀ m, compatible s.parent m → WeightedBound B m) ↔ s.bound ≤ B := by
  constructor
  · intro h
    obtain ⟨m,hm,hh⟩ := ha
    have hz := firstOne_terminal s.parent v.rootCheck m hm
    have hd : 0 ∈ delays (zeroNext m) 0 :=
      (mem_delays_iff hz).mpr ⟨0, TerminalPath.stop 0 hz⟩
    have hb := h m hm n 0 hh hd
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (cert.sound m hm k d hk hd) hb

#print axioms r5_valid
#print axioms r5_reachable
#print axioms r5_attained
#print axioms r3_valid
#print axioms r3_reachable
#print axioms r3_attained
#print axioms r2_valid
#print axioms r6_valid
#print axioms r2_reachable
#print axioms r6_reachable
#print axioms assemble
#print axioms r2_attained
#print axioms r6_attained
#print axioms exact_from_attained

end BB6.Agent50CryptidSiblings
