import Agent46CounterCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.Raw13Coupled6RBTriple
open BB6Coverage Agent31Pump Auto Counter
inductive Variant where | a | b | c deriving DecidableEq
def p (v : Variant) : PartialMachine := match v with
  | .a => fun s => match s.1.val,s.2 with
      | 0,false => some (some ⟨true,true,1⟩)
      | 0,true => some (some ⟨true,false,3⟩)
      | 1,false => some (some ⟨true,true,2⟩)
      | 1,true => none
      | 2,false => some (some ⟨true,false,0⟩)
      | 2,true => some (some ⟨true,true,4⟩)
      | 3,false => some (some ⟨false,true,5⟩)
      | 3,true => some (some ⟨false,false,0⟩)
      | 4,false => some (some ⟨true,true,5⟩)
      | 4,true => some (some ⟨false,true,1⟩)
      | 5,false => some (some ⟨true,true,2⟩)
      | 5,true => some (some ⟨false,false,3⟩)
      | _,_ => none
  | .b => fun s => match s.1.val,s.2 with
      | 0,false => some (some ⟨true,true,1⟩)
      | 0,true => some (some ⟨true,false,3⟩)
      | 1,false => some (some ⟨true,true,2⟩)
      | 1,true => some (some ⟨false,false,3⟩)
      | 2,false => some (some ⟨true,false,0⟩)
      | 2,true => some (some ⟨true,true,4⟩)
      | 3,false => some (some ⟨false,true,5⟩)
      | 3,true => some (some ⟨false,false,0⟩)
      | 4,false => some (some ⟨true,true,1⟩)
      | 4,true => some (some ⟨false,true,1⟩)
      | 5,false => none
      | 5,true => some (some ⟨true,true,2⟩)
      | _,_ => none
  | .c => fun s => match s.1.val,s.2 with
      | 0,false => some (some ⟨true,true,1⟩)
      | 0,true => some (some ⟨true,false,3⟩)
      | 1,false => some (some ⟨true,true,2⟩)
      | 1,true => some (some ⟨false,false,3⟩)
      | 2,false => some (some ⟨true,false,0⟩)
      | 2,true => some (some ⟨true,true,4⟩)
      | 3,false => some (some ⟨true,true,5⟩)
      | 3,true => some (some ⟨false,false,0⟩)
      | 4,false => some (some ⟨true,true,1⟩)
      | 4,true => some (some ⟨false,true,1⟩)
      | 5,false => none
      | 5,true => some (some ⟨false,false,4⟩)
      | _,_ => none
def Z : List Bool := [true,false,true,false,true,false]
def O : List Bool := [true,false,true,false,true,true]
def U : List Bool := [true,true,true,true,true,true]
def L : List Bool := [true,true,false,true,true,true,true,true,true,true,true,false]
def low0 : List Bool := [false,false,false]
def low1 : List Bool := [false,false,true]
def F (r : List Bool) : Z0 := ⟨2,L,r⟩
def root (k n : Nat) : Z0 := ⟨2,[false] ++ List.replicate k true ++ rep U n ++ [false,true,true,true,true,true,true,true,true,false],[]⟩
def Reach (v : Variant) (x y : Z0) : Prop := ∃ t, run0 (p v) t x = some y
theorem reachRefl (v : Variant) (x : Z0) : Reach v x x := ⟨0,rfl⟩
theorem reachTrans {v : Variant} {x y z : Z0} (h : Reach v x y) (g : Reach v y z) : Reach v x z := by
  obtain ⟨t,ht⟩ := h
  obtain ⟨u,hu⟩ := g
  exact ⟨t+u,join0 ht hu⟩
private def oddInc0F : PZ := ⟨2,(.lit [true,true,false,true,true,true,true,true,true,true,true,false]),(.lit [true,false,true,false,true,false])⟩
private def oddInc0G : PZ := ⟨2,(.lit [true,true,false,true,true,true,true,true,true,true,true,false]),(.lit [true,false,true,false,true,true])⟩
private def oddInc0M (v : Variant) : Macro := if v = .b then ⟨(List.replicate 28 .step),0,28⟩ else ⟨(List.replicate 32 .step),0,32⟩
private theorem oddInc0Check (v : Variant) : checkOpen (p v) oddInc0F oddInc0G (oddInc0M v) = true := by cases v <;> decide
private theorem oddInc0Sound (v : Variant) (n : Nat) (R : List Bool) : ∃ t, 0<t ∧ run0 (p v) t ((OpenRight.attachZ oddInc0F R).eval n) = some ((OpenRight.attachZ oddInc0G R).eval n) :=
  ⟨_,open_sound (p v) _ _ _ (oddInc0Check v) n R⟩
private def oddIncSF : PZ := ⟨2,(.lit [true,true,false,true,true,true,true,true,true,true,true,false]),(.periodic [true,false,true,false,true,true] [true,false,true,false,true,true] (.lit [true,false,true,false,true,false]))⟩
private def oddIncSG : PZ := ⟨2,(.lit [true,true,false,true,true,true,true,true,true,true,true,false]),(.periodic [true,false,true,false,true,false] [true,false,true,false,true,false] (.lit [true,false,true,false,true,true]))⟩
private def oddIncSM (v : Variant) : Macro := if v = .b then ⟨([.right [true] [true,false,true,false,true,true] [true,false,true,false,true,true] [true,true,true,true,true,true] (.lit [true,false,true,true,true,true,true,true,true,true,false]) (.lit [true,false,true,false,true,false]) 14] ++
    List.replicate 29 .step ++
    [.left [true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [true,false,true,true,true,true,true,true,true,true,false]) (.lit [true]) 6] ++
    List.replicate 19 .step),20,48⟩ else ⟨([.right [true] [true,false,true,false,true,true] [true,false,true,false,true,true] [true,true,true,true,true,true] (.lit [true,false,true,true,true,true,true,true,true,true,false]) (.lit [true,false,true,false,true,false]) 14] ++
    List.replicate 29 .step ++
    [.left [true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [true,false,true,true,true,true,true,true,true,true,false]) (.lit [true]) 6] ++
    List.replicate 23 .step),20,52⟩
private theorem oddIncSCheck (v : Variant) : checkOpen (p v) oddIncSF oddIncSG (oddIncSM v) = true := by cases v <;> decide
private theorem oddIncSSound (v : Variant) (n : Nat) (R : List Bool) : ∃ t, 0<t ∧ run0 (p v) t ((OpenRight.attachZ oddIncSF R).eval n) = some ((OpenRight.attachZ oddIncSG R).eval n) :=
  ⟨_,open_sound (p v) _ _ _ (oddIncSCheck v) n R⟩
private def evenInc0F : PZ := ⟨2,(.lit [true,true,false,true,true,true,true,true,true,true,true,false]),(.lit [false,false,false])⟩
private def evenInc0G : PZ := ⟨2,(.lit [true,true,false,true,true,true,true,true,true,true,true,false]),(.lit [false,false,true])⟩
private def evenInc0M (v : Variant) : Macro := if v = .b then ⟨(List.replicate 76 .step),0,76⟩ else ⟨(List.replicate 84 .step),0,84⟩
private theorem evenInc0Check (v : Variant) : checkOpen (p v) evenInc0F evenInc0G (evenInc0M v) = true := by cases v <;> decide
private theorem evenInc0Sound (v : Variant) (n : Nat) (R : List Bool) : ∃ t, 0<t ∧ run0 (p v) t ((OpenRight.attachZ evenInc0F R).eval n) = some ((OpenRight.attachZ evenInc0G R).eval n) :=
  ⟨_,open_sound (p v) _ _ _ (evenInc0Check v) n R⟩
private def evenCarry0F : PZ := ⟨2,(.lit [true,true,false,true,true,true,true,true,true,true,true,false]),(.lit [false,false,true,true,false,true,false,true,false])⟩
private def evenCarry0G : PZ := ⟨2,(.lit [true,true,false,true,true,true,true,true,true,true,true,false]),(.lit [false,false,false,true,false,true,false,true,true])⟩
private def evenCarry0M (v : Variant) : Macro := if v = .b then ⟨(List.replicate 96 .step),0,96⟩ else ⟨(List.replicate 104 .step),0,104⟩
private theorem evenCarry0Check (v : Variant) : checkOpen (p v) evenCarry0F evenCarry0G (evenCarry0M v) = true := by cases v <;> decide
private theorem evenCarry0Sound (v : Variant) (n : Nat) (R : List Bool) : ∃ t, 0<t ∧ run0 (p v) t ((OpenRight.attachZ evenCarry0F R).eval n) = some ((OpenRight.attachZ evenCarry0G R).eval n) :=
  ⟨_,open_sound (p v) _ _ _ (evenCarry0Check v) n R⟩
private def evenCarrySF : PZ := ⟨2,(.lit [true,true,false,true,true,true,true,true,true,true,true,false]),(.periodic [false,false,true,true,false,true,false,true,true] [true,false,true,false,true,true] (.lit [true,false,true,false,true,false]))⟩
private def evenCarrySG : PZ := ⟨2,(.lit [true,true,false,true,true,true,true,true,true,true,true,false]),(.periodic [false,false,false,true,false,true,false,true,false] [true,false,true,false,true,false] (.lit [true,false,true,false,true,true]))⟩
private def evenCarrySM (v : Variant) : Macro := if v = .b then ⟨([.right [true] [false,false,true,true,false,true,false,true,true] [true,false,true,false,true,true] [true,true,true,true,true,true] (.lit [true,false,true,true,true,true,true,true,true,true,false]) (.lit [true,false,true,false,true,false]) 14] ++
    List.replicate 32 .step ++
    [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [true,false,true,true,true,true,true,true,true,true,false]) (.lit [true]) 6] ++
    List.replicate 84 .step),20,116⟩ else ⟨([.right [true] [false,false,true,true,false,true,false,true,true] [true,false,true,false,true,true] [true,true,true,true,true,true] (.lit [true,false,true,true,true,true,true,true,true,true,false]) (.lit [true,false,true,false,true,false]) 14] ++
    List.replicate 32 .step ++
    [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [true,false,true,true,true,true,true,true,true,true,false]) (.lit [true]) 6] ++
    List.replicate 92 .step),20,124⟩
private theorem evenCarrySCheck (v : Variant) : checkOpen (p v) evenCarrySF evenCarrySG (evenCarrySM v) = true := by cases v <;> decide
private theorem evenCarrySSound (v : Variant) (n : Nat) (R : List Bool) : ∃ t, 0<t ∧ run0 (p v) t ((OpenRight.attachZ evenCarrySF R).eval n) = some ((OpenRight.attachZ evenCarrySG R).eval n) :=
  ⟨_,open_sound (p v) _ _ _ (evenCarrySCheck v) n R⟩
private def oddInitF : PZ := ⟨2,(.periodic [false,true,true,true,true,true,true,true] [true,true,true,true,true,true] (.lit [false,true,true,true,true,true,true,true,true,false])),(.lit [])⟩
private def oddInitG : PZ := ⟨2,(.lit [true,true,false,true,true,true,true,true,true,true,true,false]),(.periodic [] [true,false,true,false,true,false] (.lit [true,false,true,false,true,true]))⟩
private def oddInitM (v : Variant) : Macro := if v = .b then ⟨(List.replicate 1 .step ++
    [.left [true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [false,true,true,true,true,true,true,true,true,false]) (.lit [true]) 6] ++
    List.replicate 13 .step),6,14⟩ else ⟨(List.replicate 1 .step ++
    [.left [true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [false,true,true,true,true,true,true,true,true,false]) (.lit [true]) 6] ++
    List.replicate 17 .step),6,18⟩
private theorem oddInitCheck (v : Variant) : checkClosed (p v) oddInitF oddInitG (oddInitM v) = true := by cases v <;> decide
private theorem oddInitSound (v : Variant) (n : Nat) : ∃ t, 0<t ∧ run0 (p v) t (oddInitF.eval n) = some (oddInitG.eval n) :=
  ⟨_,closed_sound (p v) _ _ _ (oddInitCheck v) n⟩
private def evenInitF : PZ := ⟨2,(.periodic [false,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true] (.lit [false,true,true,true,true,true,true,true,true,false])),(.lit [])⟩
private def evenInitG : PZ := ⟨2,(.lit [true,true,false,true,true,true,true,true,true,true,true,false]),(.periodic [false,false,false] [true,false,true,false,true,false] (.lit [true,false,true,false,true,true]))⟩
private def evenInitM (v : Variant) : Macro := if v = .b then ⟨(List.replicate 1 .step ++
    [.left [true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [false,true,true,true,true,true,true,true,true,false]) (.lit [true]) 6] ++
    List.replicate 78 .step),6,79⟩ else ⟨(List.replicate 1 .step ++
    [.left [true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [false,true,true,true,true,true,true,true,true,false]) (.lit [true]) 6] ++
    List.replicate 86 .step),6,87⟩
private theorem evenInitCheck (v : Variant) : checkClosed (p v) evenInitF evenInitG (evenInitM v) = true := by cases v <;> decide
private theorem evenInitSound (v : Variant) (n : Nat) : ∃ t, 0<t ∧ run0 (p v) t (evenInitF.eval n) = some (evenInitG.eval n) :=
  ⟨_,closed_sound (p v) _ _ _ (evenInitCheck v) n⟩
private def oddOverF : PZ := ⟨2,(.lit [true,true,false,true,true,true,true,true,true,true,true,false]),(.periodic [true,false,true,false,true,true] [true,false,true,false,true,true] (.lit []))⟩
private def oddOverG : PZ := ⟨2,(.periodic [false,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true] (.lit [false,true,true,true,true,true,true,true,true,false])),(.lit [])⟩
private def oddOverM (v : Variant) : Macro := ⟨([.right [true] [true,false,true,false,true,true] [true,false,true,false,true,true] [true,true,true,true,true,true] (.lit [true,false,true,true,true,true,true,true,true,true,false]) (.lit []) 14] ++
    List.replicate 17 .step),14,17⟩
private theorem oddOverCheck (v : Variant) : checkClosed (p v) oddOverF oddOverG (oddOverM v) = true := by cases v <;> decide
private theorem oddOverSound (v : Variant) (n : Nat) : ∃ t, 0<t ∧ run0 (p v) t (oddOverF.eval n) = some (oddOverG.eval n) :=
  ⟨_,closed_sound (p v) _ _ _ (oddOverCheck v) n⟩
private def evenOverF : PZ := ⟨2,(.lit [true,true,false,true,true,true,true,true,true,true,true,false]),(.periodic [false,false,true,true,false,true,false,true,true] [true,false,true,false,true,true] (.lit []))⟩
private def evenOverG : PZ := ⟨2,(.periodic [false,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true] (.lit [false,true,true,true,true,true,true,true,true,false])),(.lit [])⟩
private def evenOverM (v : Variant) : Macro := ⟨([.right [true] [false,false,true,true,false,true,false,true,true] [true,false,true,false,true,true] [true,true,true,true,true,true] (.lit [true,false,true,true,true,true,true,true,true,true,false]) (.lit []) 14] ++
    List.replicate 20 .step),14,20⟩
private theorem evenOverCheck (v : Variant) : checkClosed (p v) evenOverF evenOverG (evenOverM v) = true := by cases v <;> decide
private theorem evenOverSound (v : Variant) (n : Nat) : ∃ t, 0<t ∧ run0 (p v) t (evenOverF.eval n) = some (evenOverG.eval n) :=
  ⟨_,closed_sound (p v) _ _ _ (evenOverCheck v) n⟩

theorem oddCarry (v : Variant) (n : Nat) (R : List Bool) :
    Reach v (F (rep O n ++ Z ++ R)) (F (rep Z n ++ O ++ R)) := by
  cases n with
  | zero =>
    obtain ⟨t,_,h⟩ := oddInc0Sound v 0 R
    exact ⟨t,by simpa [oddInc0F,oddInc0G,OpenRight.attachZ_eval,Word.eval,F,L,Z,O,rep] using h⟩
  | succ n =>
    obtain ⟨t,_,h⟩ := oddIncSSound v n R
    exact ⟨t,by simpa [oddIncSF,oddIncSG,OpenRight.attachZ_eval,Word.eval,F,L,Z,O,rep,List.append_assoc] using h⟩

theorem evenLow (v : Variant) (R : List Bool) : Reach v (F (low0 ++ R)) (F (low1 ++ R)) := by
  obtain ⟨t,_,h⟩ := evenInc0Sound v 0 R
  exact ⟨t,by simpa [evenInc0F,evenInc0G,OpenRight.attachZ_eval,Word.eval,F,L,low0,low1] using h⟩

theorem evenCarry (v : Variant) (n : Nat) (R : List Bool) :
    Reach v (F (low1 ++ rep O n ++ Z ++ R)) (F (low1 ++ rep Z n ++ O ++ R)) := by
  have h : Reach v (F (low1 ++ rep O n ++ Z ++ R)) (F (low0 ++ rep Z n ++ O ++ R)) := by
    cases n with
    | zero =>
      obtain ⟨t,_,h⟩ := evenCarry0Sound v 0 R
      exact ⟨t,by simpa [evenCarry0F,evenCarry0G,OpenRight.attachZ_eval,Word.eval,F,L,Z,O,low0,low1,rep,List.append_assoc] using h⟩
    | succ n =>
      obtain ⟨t,_,h⟩ := evenCarrySSound v n R
      exact ⟨t,by simpa [evenCarrySF,evenCarrySG,OpenRight.attachZ_eval,Word.eval,F,L,Z,O,low0,low1,rep,List.append_assoc] using h⟩
  exact reachTrans h (by simpa only [List.append_assoc] using evenLow v (rep Z n ++ O ++ R))

/-- Binary fill at any width, with an arbitrary untouched suffix. -/
theorem fill (v : Variant) (pre : List Bool)
    (carry : ∀ n R, Reach v (F (pre ++ rep O n ++ Z ++ R)) (F (pre ++ rep Z n ++ O ++ R)))
    (n : Nat) (R : List Bool) : Reach v (F (pre ++ rep Z n ++ R)) (F (pre ++ rep O n ++ R)) := by
  induction n generalizing R with
  | zero => simp only [rep]; exact reachRefl v _
  | succ n ih =>
    have h := ih (Z ++ R)
    have g := carry n R
    have k := ih (O ++ R)
    have h' : Reach v (F (pre ++ rep Z (n+1) ++ R)) (F (pre ++ rep O n ++ Z ++ R)) := by
      have e : rep Z (n+1) ++ R = rep Z n ++ (Z ++ R) := by
        rw [rep,← rep_snoc Z n,List.append_assoc]
      simpa only [List.append_assoc,← e] using h
    have k' : Reach v (F (pre ++ rep Z n ++ O ++ R)) (F (pre ++ rep O (n+1) ++ R)) := by
      simpa only [rep,List.append_assoc,← List.append_assoc (rep O n) O R,rep_snoc O n] using k
    exact reachTrans (reachTrans h' g) k'

theorem oddPhase (v : Variant) (n : Nat) : ∃ t, 0<t ∧ run0 (p v) t (root 7 n) = some (root 10 n) := by
  obtain ⟨a,ha,h⟩ := oddInitSound v n
  have h' : run0 (p v) a (root 7 n) = some (F (rep Z n ++ O)) := by
    simpa [oddInitF,oddInitG,PZ.eval,Word.eval,root,F,Z,O,U,L,List.append_assoc] using h
  obtain ⟨b,hb⟩ := fill v [] (by simpa only [List.nil_append] using oddCarry v) n O
  obtain ⟨c,hc,k⟩ := oddOverSound v n
  have k' : run0 (p v) c (F (rep O n ++ O)) = some (root 10 n) := by
    simpa [oddOverF,oddOverG,PZ.eval,Word.eval,root,F,Z,O,U,L,rep,List.append_assoc,rep_snoc] using k
  simp only [List.nil_append] at hb
  exact ⟨a+b+c,by omega,join0 (join0 h' hb) k'⟩

theorem evenPhase (v : Variant) (n : Nat) : ∃ t, 0<t ∧ run0 (p v) t (root 10 n) = some (root 7 (n+1)) := by
  obtain ⟨a,ha,h⟩ := evenInitSound v n
  have h' : run0 (p v) a (root 10 n) = some (F (low0 ++ rep Z n ++ O)) := by
    simpa [evenInitF,evenInitG,PZ.eval,Word.eval,root,F,Z,O,U,L,low0,List.append_assoc] using h
  obtain ⟨b,hb⟩ := evenLow v (rep Z n ++ O)
  obtain ⟨c,hc⟩ := fill v low1 (evenCarry v) n O
  obtain ⟨d,hd,k⟩ := evenOverSound v n
  have k' : run0 (p v) d (F (low1 ++ rep O n ++ O)) = some (root 7 (n+1)) := by
    simpa [evenOverF,evenOverG,PZ.eval,Word.eval,root,F,Z,O,U,L,low1,rep,List.append_assoc,rep_snoc] using k
  exact ⟨a+b+c+d,by omega,join0 (join0 (join0 h' (by simpa only [List.append_assoc] using hb)) hc) k'⟩

def entry (v : Variant) : Nat := if v = .b then 257 else 289

theorem seed (v : Variant) : run0 (p v) (entry v) ⟨0,[],[]⟩ = some (root 7 0) := by cases v <;> decide

theorem growth (v : Variant) (n : Nat) : ∃ t, 0<t ∧ run0 (p v) t (root 7 n) = some (root 7 (n+1)) := by
  obtain ⟨a,ha,h⟩ := oddPhase v n
  obtain ⟨b,hb,g⟩ := evenPhase v n
  exact ⟨a+b,by omega,join0 h g⟩

noncomputable def cost (v : Variant) (n : Nat) : Nat := Classical.choose (growth v n)

theorem never (v : Variant) (m : Machine) (hm : compatible (p v) m) : NeverHalts m :=
  never_of_growth (p v) (root 7) (entry v) (cost v) (seed v)
    (fun n => (Classical.choose_spec (growth v n)).1) (fun n => (Classical.choose_spec (growth v n)).2) m hm

#print axioms never
end BB6Coverage.Agent31Pump.Auto.Raw13Coupled6RBTriple
