import TNFPilot
import SideCycle
import R1RF
import R1Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47R1Parent
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6Coverage.Agent50SideCycle
open BB6Coverage.Agent47R1Sweep BB6.Agent47R1Certificate

inductive Growth where
  | zBD (d : Bool)
  | zRA
  | oBD (d : Bool)
  | oLC
  | la_re (la : Bool)
  | zRB_RF (f : Bool)
  | oRF

def Growth.action : Growth → Move
  | .zBD d => zeroBD d
  | .zRA => zeroRA
  | .oBD d => oneBD d
  | .oLC => oneLC
  | .la_re la => pumpAction la
  | .zRB_RF f => actRB f
  | .oRF => oneRF

theorem Growth.defined (g : Growth) : ∀ n, ∃ z, BB6Coverage.Agent50Zipper.zrun (tableWith g.action) n start = some z := by
  cases g with
  | zBD d => exact all_defined_variant (useD:=d)
  | zRA => exact all_defined_RA
  | oBD d => exact all_defined_BD d
  | oLC => exact all_defined_LC
  | la_re la => exact all_defined_LA_RE la
  | zRB_RF f => exact all_defined_RB_RF f
  | oRF => exact all_defined_RF

inductive SiblingWitness where
  | last (n : Nat)
  | cycle (entry period : Nat) (right : Bool) (boundary : Int)
  | growth (g : Growth)
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

/-- Execute on a finite zipper rather than a long function-update chain. -/
def zipQuery (p : PartialMachine) (n : Nat) : Option Slot :=
  (BB6Coverage.Agent50Zipper.zrun p n start).map (fun z => (z.q,z.l.headD false))

theorem zipQuery_sound (p : PartialMachine) (n : Nat) (s : Slot)
    (h : zipQuery p n = some s) :
    (knownRun p n).map readSlot = some s := by
  unfold zipQuery at h
  cases hz : BB6Coverage.Agent50Zipper.zrun p n start with
  | none => simp [hz] at h
  | some z =>
    have hr := BB6Coverage.Agent50Zipper.zrun_sound p (weightedTNFDefaultCompletion p)
      (weightedTNFDefaultCompletion_compatible p) n start z hz
    rw [initial_embed] at hr
    rw [weightedTNFKnownRun_eq_defaultRun,hr]
    simp only [hz,Option.map_some,BB6Coverage.Agent50Zipper.read_embed] at h ⊢
    exact h

def siblingOK (s : SiblingSpec) (mv : Move) : Bool :=
  let p := s.child mv
  match s.witness mv with
  | .last n =>
    decide (zipQuery p n = some s.lastSlot) &&
      (decide (p s.lastSlot = none) &&
        (restOK p s.lastSlot && weightOK p s.lastSlot n s.bound))
  | .cycle entry period right boundary =>
    decide (0 < period) && finiteSideCycleCheck p entry period right boundary
  | .growth g => partialEq p (tableWith g.action)
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
    have h : (zipQuery (s.child mv) n = some s.lastSlot) ∧
        s.child mv s.lastSlot = none ∧ restOK (s.child mv) s.lastSlot = true ∧
        weightOK (s.child mv) s.lastSlot n s.bound = true := by
      simpa only [siblingOK, he, Bool.and_eq_true, decide_eq_true_eq] using hc
    exact lastCertAt _ n s.lastSlot s.bound hr (zipQuery_sound _ _ _ h.1) h.2.1 h.2.2.1 h.2.2.2
  | cycle entry period right boundary =>
    have h : 0 < period ∧
        finiteSideCycleCheck (s.child mv) entry period right boundary = true := by
      simpa only [siblingOK,he,Bool.and_eq_true,decide_eq_true_eq] using hc
    exact .nonhalt hr (support6 _) hno
      (finiteSideCycleCheck_sound _ entry period right boundary h.1 h.2)
  | growth g =>
    have h : partialEq (s.child mv) (tableWith g.action) = true := by
      simpa only [siblingOK,he] using hc
    have heq := partialEq_sound _ _ h
    exact .nonhalt hr (support6 _) hno (by
      rw [heq]
      exact never_of_defined g.action g.defined)
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

def r1 : SiblingSpec where
  path := (scheduleAction oneRF).take 9
  hole := (5,true)
  splitAt := 52
  lastSlot := (3,true)
  bound := 7014
  special := ⟨true,false,5⟩
  witness := fun mv =>
    match mv.write,mv.right,mv.next.val with
    | false,false,0 => .last 56
    | false,false,1 => .growth (.zBD false)
    | false,false,2 => .last 225
    | false,false,3 => .growth (.zBD true)
    | false,false,4 => .last 193
    | false,false,5 => .last 3209
    | false,true,0 => .growth .zRA
    | false,true,1 => .growth (.zRB_RF false)
    | false,true,2 => .last 7011
    | false,true,3 => .last 53
    | false,true,4 => .growth (.la_re false)
    | false,true,5 => .growth (.zRB_RF true)
    | true,false,0 => .growth (.la_re true)
    | true,false,1 => .growth (.oBD false)
    | true,false,2 => .growth .oLC
    | true,false,3 => .growth (.oBD true)
    | true,false,4 => .last 227
    | true,false,5 => .known
    | true,true,0 => .cycle 2 54 false 5
    | true,true,1 => .last 191
    | true,true,2 => .last 54
    | true,true,3 => .last 53
    | true,true,4 => .cycle 51 2 true (-2)
    | true,true,5 => .growth .oRF
    | _,_,_ => .known

theorem r1_valid : ValidSpec r1 := by
  constructor <;> decide

theorem r1_reachable : FirstHolePath r1.parent 6 := spec_reachable r1 r1_valid

theorem attain_last (s : SiblingSpec) (v : ValidSpec s) (mv : Move) (n : Nat)
    (hw : s.witness mv = .last n) :
    ∃ m, compatible s.parent m ∧ HaltsAfter m n := by
  have hc := sibling_checked s v mv
  have h : (zipQuery (s.child mv) n = some s.lastSlot) ∧
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
  have hread := zipQuery_sound _ _ _ h.1
  cases hrun : knownRun (s.child mv) n with
  | none => simp [hrun] at hread
  | some c =>
    have hs : readSlot c = s.lastSlot := by simpa [hrun] using (zipQuery_sound _ _ _ h.1)
    apply first_hole_halts (s.child mv) n c hrun
    · simpa [hs] using h.2.1
    · simpa [hs] using hm

theorem r1_attained : ∃ m, compatible r1.parent m ∧ HaltsAfter m 7011 :=
  attain_last r1 r1_valid ⟨false,true,2⟩ 7011 rfl

/-- The fixed C0/E0 blank prefix allows an incoming delay of two
    for every completion, independently of the two unknown rows. -/
theorem r1_delay_two (m : Machine) (hm : compatible r1.parent m) :
    2 ∈ delays (zeroNext m) 0 := by
  have hz := firstOne_terminal r1.parent r1_valid.rootCheck m hm
  have hC := hm ((2 : Fin 6),false) (some ⟨false,false,4⟩)
    (show r1.parent (2,false) = some (some ⟨false,false,4⟩) by decide)
  have hE := hm ((4 : Fin 6),false) (some ⟨false,true,0⟩)
    (show r1.parent (4,false) = some (some ⟨false,true,0⟩) by decide)
  have hce : zeroNext m 2 = some 4 := by simp [zeroNext,hC]
  have hea : zeroNext m 4 = some 0 := by simp [zeroNext,hE]
  exact (mem_delays_iff hz).mpr ⟨2, TerminalPath.step hce (TerminalPath.step hea (TerminalPath.stop 0 hz))⟩

theorem exact_from_attained
    (cert : WeightedTNFCertificate r1.bound r1.parent 6) (B : Nat) :
    (∀ m, compatible r1.parent m → WeightedBound B m) ↔ 7014 ≤ B := by
  constructor
  · intro h
    obtain ⟨m,hm,hh⟩ := r1_attained
    have hb := h m hm 7011 2 hh (r1_delay_two m hm)
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (cert.sound m hm k d hk hd) hb

theorem raw_upper (cert : WeightedTNFCertificate r1.bound r1.parent 6)
    (m : Machine) (hm : compatible r1.parent m) (n : Nat)
    (hn : HaltsAfter m n) : n+1 ≤ 7012 := by
  have hb := cert.sound m hm n 2 hn (r1_delay_two m hm)
  change 2+n+1 ≤ 7014 at hb
  omega

#print axioms r1_valid
#print axioms r1_reachable
#print axioms r1_attained
#print axioms assemble
#print axioms exact_from_attained
end BB6.Agent47R1Parent
