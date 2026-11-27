import PackedAudit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent48PackedPrefix
open BB6Coverage BB6Coverage.Agent13PackedZipper BB6.Agent3PackedCycle
open BB6.Agent31ThreeHole BB6.Agent3PackedAudit BB6.Agent13BlankDelay
open BB6.Agent8TNFPath BB6.Agent50TNFPilot BB6Coverage.Agent10ZipAudit

theorem runH_project (p : PartialMachine) (n : Nat) (z : H) :
    (runH p n z).map H.p = runP p n z.p := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    cases h : (p (readP z.p)).bind id with
    | none => simp [runH,runP,stepH,stepP,h]
    | some mv => simpa only [runH,runP,stepH,stepP,h,Option.map_some,Option.bind_some,moveH] using ih (moveH mv z)

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

theorem refineStepH (p : PartialMachine) (s : Slot) (mv : Move)
    (hu : p s = none) (z d : H) (h : stepH p z = some d) :
    stepH (refine p s (some mv)) z = some d := by
  unfold stepH at h ⊢
  by_cases he : readP z.p = s
  · rw [he,hu] at h
    simp at h
  · simpa only [refine,he,ite_false] using h

theorem refineRunH (p : PartialMachine) (s : Slot) (mv : Move)
    (hu : p s = none) (n : Nat) (z d : H)
    (h : runH p n z = some d) : runH (refine p s (some mv)) n z = some d := by
  induction n generalizing z with
  | zero => exact h
  | succ n ih =>
    cases hs : stepH p z with
    | none => simp [runH,hs] at h
    | some c =>
      have ht : runH p n c = some d := by simpa only [runH,hs,Option.bind_some] using h
      have hr := refineStepH p s mv hu z c hs
      simpa only [runH,hr,Option.bind_some] using ih c ht

def advanceH (p : PartialMachine) (t : Nat) (z : H) (n : Nat) : Option H :=
  if t ≤ n then runH p (n-t) z else runH p n startH

theorem advanceH_eq (p : PartialMachine) (t : Nat) (z : H)
    (h : runH p t startH = some z) (n : Nat) :
    advanceH p t z n = runH p n startH := by
  unfold advanceH
  split
  · rename_i hle
    rw [show n=t+(n-t) by omega,runH_add,h]
    simp only [Nat.add_sub_cancel_left,Option.bind_some]
  · rfl

def queryAtH (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : H) : Bool :=
  decide (readP z.p = s) && (decide (p s = none) && weightOK p s n B)

theorem queryAtH_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : H)
    (h : runH p n startH = some z) : queryAtH B p n s z = packedQueryOK B p n s := by
  have hp : runP p n startP = some z.p := by
    have h' := runH_project p n startH
    rw [h] at h'
    simpa only [Option.map_some,startH] using h'.symm
  simp only [queryAtH,packedQueryOK,readRunP,hp,Option.map_some,Option.some.injEq]

theorem queryAtH_hole (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : H)
    (h : queryAtH B p n s z = true) : p s = none := by
  simp only [queryAtH,Bool.and_eq_true,decide_eq_true_eq] at h
  exact h.2.1

theorem queryFail (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (h : runH p n startH = none) : packedQueryOK B p n s = false := by
  have hp : runP p n startP = none := by
    have h' := runH_project p n startH
    rw [h] at h'
    simpa only [Option.map_none,startH] using h'.symm
  simp [packedQueryOK,readRunP,hp]

def cycleAtH (p : PartialMachine) (t : Nat) (z : H) (entry period : Nat)
    (right : Bool) (boundary : Int) : Bool :=
  match advanceH p t z entry with
  | none => false
  | some c => match windowH p right boundary period c with
    | none => false
    | some d => tailH right boundary c d

theorem cycleAtH_eq (p : PartialMachine) (t : Nat) (z : H) (entry period : Nat)
    (right : Bool) (boundary : Int) (h : runH p t startH = some z) :
    cycleAtH p t z entry period right boundary = cycleH p entry period right boundary := by
  rw [cycleAtH,cycleH,advanceH_eq p t z h]
  rfl

/-- Reuse the exact prefix, restarting if a cycle entry predates it. -/
def checkAtH (B : Nat) (p : PartialMachine) (t : Nat) (z : H) : (a : Audit) → Bool
  | .last n s => match advanceH p t z n with
    | none => false
    | some c => queryAtH B p n s c && restOK p s
  | .cycle e k r b => decide (0 < k) && cycleAtH p t z e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => match advanceH p t z n with
    | none => false
    | some c => queryAtH B p n s c &&
        allMoves (fun mv => checkAtH B (refine p s (some mv)) n c (kids mv))
termination_by structural a => a

theorem checkAtH_eq (B : Nat) (p : PartialMachine) (a : Audit)
    (t : Nat) (z : H) (h : runH p t startH = some z) :
    checkAtH B p t z a = packedCheck B p a := by
  induction a generalizing p t z with
  | last n s =>
    rw [checkAtH,packedCheck,advanceH_eq p t z h]
    cases hr : runH p n startH with
    | none => simp [queryFail B p n s hr]
    | some c => simp only [queryAtH_eq B p n s c hr]
  | cycle e k r b =>
    simp only [checkAtH,packedCheck,cycleAtH_eq p t z e k r b h]
  | far rev d C => rfl
  | proven q safe => rfl
  | split n s kids ih =>
    rw [checkAtH,packedCheck,advanceH_eq p t z h]
    cases hr : runH p n startH with
    | none => simp [queryFail B p n s hr]
    | some c =>
      simp only [queryAtH_eq B p n s c hr]
      by_cases hq : packedQueryOK B p n s = true
      · have hq' : queryAtH B p n s c = true := (queryAtH_eq B p n s c hr).trans hq
        have hu := queryAtH_hole B p n s c hq'
        simp only [hq,Bool.true_and]
        apply congrArg allMoves
        funext mv
        exact ih mv (refine p s (some mv)) n c (refineRunH p s mv hu n startH c hr)
      · have hf : packedQueryOK B p n s = false := Bool.eq_false_iff.mpr hq
        simp only [hf,Bool.false_and]

def packedPrefixCheck (B : Nat) (p : PartialMachine) (a : Audit) : Bool :=
  checkAtH B p 0 startH a

theorem packedPrefixCheck_eq (B : Nat) (p : PartialMachine) (a : Audit) :
    packedPrefixCheck B p a = packedCheck B p a := checkAtH_eq B p a 0 startH rfl

#print axioms runH_project
#print axioms refineRunH
#print axioms packedPrefixCheck_eq
end BB6.Agent48PackedPrefix
