import Raw58LF1Prefix
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4LF1Sweep
open BB6Coverage Agent31Pump

-- Keep the invariant 2^n prefix in a natural counter. Any other leading
-- word, including the two exceptional prefix shapes, is handled exactly.
def strip2 : List Nat → Nat × List Nat
  | 2::ws => let t := strip2 ws; (t.1+1,t.2)
  | w => (0,w)

theorem strip2_sound (w : List Nat) :
    List.replicate (strip2 w).1 2 ++ (strip2 w).2 = w := by
  induction w with
  | nil => rfl
  | cons a ws ih =>
    match a with
    | 0 => rfl
    | 1 => rfl
    | 2 =>
      change List.replicate ((strip2 ws).1+1) 2 ++ (strip2 ws).2 = 2::ws
      rw [List.replicate_succ,List.cons_append,ih]
    | a+3 => rfl

inductive CResult where
  | back (cost : Nat) (pre : Nat) (suffix : List Nat)
  | hole (cost : Nat)
  deriving DecidableEq, Repr

def CResult.expand : CResult → Result
  | .back c n w => .back c (List.replicate n 2 ++ w)
  | .hole c => .hole c

def CResult.add (n : Nat) : CResult → CResult
  | .back c p w => .back (n+c) p w
  | .hole c => .hole (n+c)

theorem expand_add (o : CResult) (n : Nat) : (o.add n).expand = o.expand.add n := by cases o <;> rfl

def cLift (v : V) (n : Nat) : Result → CResult
  | .back c w => let t := strip2 w; .back (c+n*(cost010 v+3)) (n+t.1) t.2
  | .hole c => .hole (c+n*cost010 v)

theorem cLift_sound (v : V) (n : Nat) (o : Result) : (cLift v n o).expand = liftPrefix v n o := by
  cases o with
  | hole c => simp only [cLift,CResult.expand,liftPrefix,old2,Result.add]; congr 1; omega
  | back c w =>
    simp only [cLift,CResult.expand,liftPrefix,old2,Result.add]
    rw [← List.replicate_append_replicate,List.append_assoc,strip2_sound]
    congr 1
    cases v <;> simp [cost010] <;> omega

theorem liftPrefix_zero (v : V) (o : Result) : liftPrefix v 0 o = o := by
  cases o <;> simp [liftPrefix,old2,Result.add]

def cSection (v : V) (n : Nat) (w : List Nat) : CResult :=
  match w with
  | (a+1)::ws => cLift v n (evalSection v ((a+1)::ws))
  | w => cLift v 0 (evalSection v (List.replicate n 2 ++ w))

theorem cSection_eq (v : V) (n : Nat) (w : List Nat) :
    (cSection v n w).expand = evalSection v (List.replicate n 2 ++ w) := by
  match w with
  | [] => simp only [cSection,cLift_sound,liftPrefix_zero]
  | 0::ws => simp only [cSection,cLift_sound,liftPrefix_zero]
  | (a+1)::ws => rw [cSection,cLift_sound,evalSection_prefix]

def cSections (v : V) : Nat → Nat → List Nat → CResult
  | 0,p,w => .back 0 p w
  | n+1,p,w => match cSection v p w with
    | .hole c => .hole c
    | .back c p' w' => (cSections v n p' w').add c

theorem cSections_eq (v : V) (n p : Nat) (w : List Nat) :
    (cSections v n p w).expand = evalSections v n (List.replicate p 2 ++ w) := by
  induction n generalizing p w with
  | zero => rfl
  | succ n ih =>
    rw [evalSections,← cSection_eq v p w]
    cases he : cSection v p w with
    | hole c => simp only [cSections,he,CResult.expand]
    | back c p' w' =>
      rw [cSections,he]
      change ((cSections v n p' w').add c).expand = (evalSections v n (List.replicate p' 2 ++ w')).add c
      rw [expand_add,ih]

def blankCompressed (v : V) (n : Nat) : CResult := (cSections v n 1 [1]).add 12

theorem blankCompressed_eq (v : V) (n : Nat) : (blankCompressed v n).expand = blankEval v n := by
  simp only [blankCompressed,blankEval,expand_add,cSections_eq]
  rfl

theorem blankCompressed_sound (v : V) (n : Nat) : Valid v ⟨0,[],[]⟩ (blankCompressed v n).expand := by
  rw [blankCompressed_eq]; exact blankEval_sound v n

#print axioms blankCompressed_sound
end BB6Coverage.Agent4LF1Sweep
