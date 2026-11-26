import DirectAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3PrefixAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6Coverage.Agent10ZipAudit
open BB6.Agent3PackedCycle BB6Coverage.Agent13PackedZipper BB6.Agent3SparseAudit

theorem runH_add (p : PartialMachine) (n k : Nat) (z : H) :
    runH p (n+k) z = (runH p n z).bind (runH p k) := by
  induction n generalizing z with
  | zero => simp [runH]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [runH]
    cases stepH p z with
    | none => rfl
    | some t => exact ih t

theorem runH_refine {p : PartialMachine} {s : Slot} {t : Transition}
    (hs : p s = none) (n : Nat) (a b : H) (h : runH p n a = some b) :
    runH (refine p s t) n a = some b := by
  induction n generalizing a with
  | zero => exact h
  | succ n ih =>
    simp only [runH] at h ⊢
    unfold stepH at h ⊢
    cases he : p (readP a.p) with
    | none => simp [he] at h
    | some tr =>
      cases tr with
      | none => simp [he] at h
      | some mv =>
        have hne : readP a.p ≠ s := by
          intro e
          rw [e,hs] at he
          contradiction
        simp only [refine,hne,ite_false,he,Option.bind_some,id_eq,Option.map_some] at h ⊢
        exact ih _ h

theorem runH_p (p : PartialMachine) (n : Nat) (z : H) :
    (runH p n z).map H.p = runP p n z.p := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [runH,runP,stepH,stepP]
    cases h : (p (readP z.p)).bind id with
    | none => rfl
    | some mv => exact ih (moveH mv z)

def runFrom (p : PartialMachine) (k : Nat) (z : H) (n : Nat) : Option H :=
  if k ≤ n then runH p (n-k) z else runH p n startH

theorem runFrom_eq (p : PartialMachine) (k : Nat) (z : H)
    (h : runH p k startH = some z) (n : Nat) :
    runFrom p k z n = runH p n startH := by
  unfold runFrom
  split
  next hkn =>
    rw [show n = k+(n-k) by omega,runH_add,h]
    simp
  next => rfl

def queryHere (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : H) : Bool :=
  decide (readP z.p = s) && (decide (p s = none) && weightOK p s n B)

theorem queryHere_sound {B p n s z}
    (h : runH p n startH = some z) (hq : queryHere B p n s z = true) :
    packedQueryOK B p n s = true := by
  have hp := runH_p p n startH
  rw [h] at hp
  have hread : readRunP p n = some (readP z.p) := by
    unfold readRunP
    change (runP p n startH.p).map readP = _
    rw [← hp]
    rfl
  simpa only [packedQueryOK,hread,queryHere,Option.some.injEq] using hq

def cycleFrom (p : PartialMachine) (k : Nat) (z : H)
    (e period : Nat) (right : Bool) (boundary : Int) : Bool :=
  match runFrom p k z e with
  | none => false
  | some c => match windowH p right boundary period c with
    | none => false
    | some d => tailH right boundary c d

theorem cycleFrom_eq (p : PartialMachine) (k : Nat) (z : H)
    (h : runH p k startH = some z) (e period : Nat) (right : Bool) (boundary : Int) :
    cycleFrom p k z e period right boundary = cycleH p e period right boundary := by
  simp only [cycleFrom,cycleH,runFrom_eq p k z h]
  rfl

/-- Reuse the exact successful parent prefix for every refinement.
    All certificate times retain their original absolute interpretation. -/
def prefixCheck (B : Nat) (p : PartialMachine) (k : Nat) (z : H) :
    (t : SparseAudit) → Bool
  | .last n s => match runFrom p k z n with
    | none => false
    | some c => queryHere B p n s c && restOK p s
  | .cycle e period r b => decide (0 < period) && cycleFrom p k z e period r b
  | .far rev _ C S => FAR.Direct.check C S (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => match runFrom p k z n with
    | none => false
    | some c => queryHere B p n s c &&
        allMoves (fun mv => prefixCheck B (refine p s (some mv)) n c (kids mv))
termination_by structural t => t

theorem prefixCheck_sparse (B : Nat) (p : PartialMachine) (k : Nat) (z : H)
    (t : SparseAudit) (hpre : runH p k startH = some z)
    (h : prefixCheck B p k z t = true) : sparseCheck B p t = true := by
  induction t generalizing p k z with
  | last n s =>
    simp only [prefixCheck,runFrom_eq p k z hpre] at h
    cases hr : runH p n startH with
    | none => simp [hr] at h
    | some c =>
      have hv : queryHere B p n s c = true ∧ restOK p s = true := by
        simpa [hr,Bool.and_eq_true] using h
      simp only [sparseCheck,Bool.and_eq_true]
      exact ⟨queryHere_sound hr hv.1,hv.2⟩
  | cycle e period r b =>
    simpa only [prefixCheck,sparseCheck,cycleFrom_eq p k z hpre] using h
  | far rev d C S =>
    exact FAR.Direct.check_sparse C S _ h
  | proven q safe => exact h
  | split n s kids ih =>
    simp only [prefixCheck,runFrom_eq p k z hpre] at h
    cases hr : runH p n startH with
    | none => simp [hr] at h
    | some c =>
      have hv : queryHere B p n s c = true ∧
          allMoves (fun mv => prefixCheck B (refine p s (some mv)) n c (kids mv)) = true := by
        simpa [hr,Bool.and_eq_true] using h
      have hq := queryHere_sound hr hv.1
      have hs := (packedQueryOK_sound hq).2.1
      simp only [sparseCheck,Bool.and_eq_true]
      refine ⟨hq,allMoves_of _ ?_⟩
      intro mv
      exact ih mv _ n c (runH_refine hs n startH c hr) (allMoves_sound _ hv.2 mv)

theorem prefixRoot_sparse (B : Nat) (p : PartialMachine) (t : SparseAudit)
    (h : prefixCheck B p 0 startH t = true) : sparseCheck B p t = true :=
  prefixCheck_sparse B p 0 startH t rfl h

#print axioms prefixRoot_sparse
end BB6.Agent3PrefixAudit
