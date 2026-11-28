import Raw54Base
import FastThreeHoleAudit
import PartialAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false

namespace BB6.Agent8Raw54.OneRDBankAudit
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit
open BB6Coverage.Agent50SideCycle BB6.Agent47PartialAudit

/-- A compact source-derived DFA. The raw destinations are reduced modulo d;
    the generated bank separately checks that every source code already lies
    in range, so this conversion is definitionally total. -/
structure FarSpec where
  rev : Bool
  d : Nat
  pos : 0 < d
  raw : List Nat

def FarSpec.dfa (s : FarSpec) : List (Fin s.d) :=
  s.raw.map fun n => ⟨n % s.d, Nat.mod_lt _ s.pos⟩

def farSpecCheck (p : PartialMachine) (s : FarSpec) : Bool :=
  match s.rev with
  | false => (FAR.fastTryDfa p ⟨0,s.pos⟩ s.dfa).isSome
  | true => (FAR.fastTryDfa (FAR.reflectPartial p) ⟨0,s.pos⟩ s.dfa).isSome

private theorem fromTry {d : Nat} (p : PartialMachine) (start : Fin d)
    (dfa : List (Fin d))
    (h : (FAR.fastTryDfa p start dfa).isSome = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  cases hz : FAR.fastTryDfa p start dfa with
  | none => simp [hz] at h
  | some cert => exact cert.2.1.sound p cert.2.2 m hm

theorem farSpecCheck_sound (p : PartialMachine) (s : FarSpec)
    (h : farSpecCheck p s = true) (m : Machine) (hm : compatible p m) :
    NeverHalts m := by
  cases hr : s.rev with
  | false =>
      have ht : (FAR.fastTryDfa p ⟨0,s.pos⟩ s.dfa).isSome = true := by
        simpa [farSpecCheck,hr] using h
      exact fromTry p ⟨0,s.pos⟩ s.dfa ht m hm
  | true =>
      have ht :
          (FAR.fastTryDfa (FAR.reflectPartial p) ⟨0,s.pos⟩ s.dfa).isSome = true := by
        simpa [farSpecCheck,hr] using h
      exact FAR.reflectNever m
        (fromTry (FAR.reflectPartial p) ⟨0,s.pos⟩ s.dfa ht
          (reflectTable m) (FAR.reflectCompatible p m hm))

/-- Compact partial audit: FAR leaves carry only an index into a checked DFA
    bank. Unresolved leaves are retained exactly. -/
inductive BankAudit where
  | unresolved
  | last (n : Nat) (s : Slot)
  | cycle (entry period : Nat) (right : Bool) (boundary : Int)
  | far (bankIndex : Nat)
  | split (n : Nat) (s : Slot) (kids : Move → BankAudit)

def bankCheck (bank : List FarSpec) (B : Nat) (p : PartialMachine) :
    BankAudit → Bool
  | .unresolved => true
  | .last n s => queryOK B p n s && restOK p s
  | .cycle e k r b => decide (0 < k) && fastSideCycleCheck p e k r b
  | .far i =>
      match bank[i]? with
      | none => false
      | some spec => farSpecCheck p spec
  | .split n s kids => queryOK B p n s &&
      allMoves (fun mv => bankCheck bank B (refine p s (some mv)) (kids mv))
termination_by structural t => t

def bankResiduals (p : PartialMachine) : BankAudit →
    List (List Move × PartialMachine)
  | .unresolved => [([],p)]
  | .last _ _ => []
  | .cycle _ _ _ _ => []
  | .far _ => []
  | .split _ s kids => auditMoves.flatMap fun mv =>
      (bankResiduals (refine p s (some mv)) (kids mv)).map fun e =>
        (mv :: e.1, e.2)
termination_by structural t => t

def byBankMove (xs : List BankAudit) (mv : Move) : BankAudit :=
  xs[12*mv.write.toNat+6*mv.right.toNat+mv.next.val]?.getD .unresolved

/-- Soundness of the compact bank audit. Discovery, tree construction, and
    bank selection remain untrusted; this theorem makes only a successful
    Lean check authoritative. -/
theorem bankSound (bank : List FarSpec) (B : Nat) (p : PartialMachine)
    (t : BankAudit)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (h : bankCheck bank B p t = true) :
    ∀ m, compatible p m → WeightedBound B m ∨
      ∃ e ∈ bankResiduals p t, compatible e.2 m := by
  induction t generalizing p with
  | unresolved =>
      intro m hm
      exact Or.inr ⟨([],p), by simp [bankResiduals], hm⟩
  | last n s =>
      intro m hm
      have hc : fastCheck B p (.last n s) = true := by
        simpa only [bankCheck, fastCheck] using h
      exact Or.inl ((certifiedFast B p (.last n s) hf hno hc).sound m hm)
  | cycle e k r b =>
      intro m hm
      have hc : fastCheck B p (.cycle e k r b) = true := by
        simpa only [bankCheck, fastCheck] using h
      exact Or.inl ((certifiedFast B p (.cycle e k r b) hf hno hc).sound m hm)
  | far i =>
      intro m hm
      cases hb : bank[i]? with
      | none => simp [bankCheck,hb] at h
      | some spec =>
          have hs : farSpecCheck p spec = true := by
            simpa only [bankCheck,hb] using h
          exact Or.inl (weighted_never B m (farSpecCheck_sound p spec hs m hm))
  | split n s kids ih =>
      have hv : queryOK B p n s = true ∧
          allMoves (fun mv => bankCheck bank B (refine p s (some mv)) (kids mv)) = true := by
        simpa only [bankCheck, Bool.and_eq_true] using h
      obtain ⟨hread,hhole,hw⟩ := queryOK_sound hv.1
      intro m hm
      cases ht : m s with
      | none =>
          cases hr : knownRun p n with
          | none => simp [hr] at hread
          | some c =>
              have hs : readSlot c = s := by simpa [hr] using hread
              have hc : compatible (refine p s none) m := by
                simpa [ht] using compatible_refine p m s hm
              exact Or.inl (first_hole_weighted_halt B p n c hf hr
                (by simpa [hs] using hhole)
                (by simpa [hs] using weightOK_sound p s n B hw) m
                (by simpa [hs] using hc))
      | some mv =>
          have hc : compatible (refine p s (some mv)) m := by
            simpa [ht] using compatible_refine p m s hm
          have hchild := allMoves_sound _ hv.2 mv
          have hf' := refine_preserves_firstOne p s (some mv) hhole hf
          have hn' := weightedTNFNoAssignedHalt_refine p s mv hno
          rcases ih mv (refine p s (some mv)) hf' hn' hchild m hc with
            hb | ⟨e,he,hec⟩
          · exact Or.inl hb
          · exact Or.inr ⟨(mv :: e.1,e.2), List.mem_flatMap.mpr
              ⟨mv, auditMoves_complete mv,
                List.mem_map.mpr ⟨e,he,rfl⟩⟩, hec⟩

#print axioms farSpecCheck_sound
#print axioms bankSound
end BB6.Agent8Raw54.OneRDBankAudit
