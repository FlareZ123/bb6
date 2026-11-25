import Raw60LFUnaryCore
namespace BB6.Agent1Raw60LFSeparatorCounter
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,v,if v then 5 else 0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
abbrev B := Q 1
abbrev mark : List Bool := [true,true,true,false,true]
abbrev markOut : List Bool := [false,false,true,true,true]
def pairCost (v : Bool) := if v then 6 else 4
theorem umerge (a b : Nat) (R : List Bool) : U a++(U b++R)=U (a+b)++R := by
  rw [← List.append_assoc,List.replicate_append_replicate]
theorem pairSweep (v : Bool) (k : Nat) (L R : List Bool) : Reach (table v)
    (B (false::L) (U (2*k+1)++R)) (B (false::(U (2*k)++L)) (true::R)) := by
  induction k generalizing L with
  | zero => exact ⟨0,by rfl⟩
  | succ k ih =>
    have h1 : run0 (table v) (pairCost v) (B (false::L) (U (2*(k+1)+1)++R)) = some (B (false::true::true::L) (U (2*k+1)++R)) := by cases v <;> rfl
    have h2 := ih (true::true::L)
    have he : U (2*k)++true::true::L = U (2*(k+1))++L := by
      change U (2*k)++(U 2++L)=_
      rw [umerge]
      rfl
    rw [he] at h2
    exact reachTrans ⟨pairCost v,h1⟩ h2
inductive Word where
  | end0
  | end1
  | more (b : Bool) (k : Nat) (w : Word)
def rest : Word → List Bool
  | .end0 => []
  | .end1 => [false,true,true,false]
  | .more b k w => (if b then [false,true,true,false,false] else [false,false,false])++(U (2*k+1)++false::rest w)
def enc (w : Word) := false::rest w
def next : Word → Word
  | .end0 => .end1
  | .end1 => .more false 2 .end0
  | .more false k w => .more true k w
  | .more true k w => .more false (k+1) (next w)
theorem scan (v : Bool) (w : Word) (L : List Bool) : ∃ R, Reach (table v) (B (false::L) (rest w)) (F L R) ∧ false::false::R = enc (next w) := by
  induction w generalizing L with
  | end0 => exact ⟨[true,true,false],⟨9,by cases v <;> rfl⟩,rfl⟩
  | end1 =>
    have h1 : run0 (table v) 5 (B (false::L) (rest .end1)) = some (B (false::(mark++L)) []) := by cases v <;> rfl
    have h2 : run0 (table v) 9 (B (false::(mark++L)) []) = some (F (mark++L) [true,true,false]) := by cases v <;> rfl
    have h3 : run0 (table v) 5 (F (mark++L) [true,true,false]) = some (F L (markOut++[true,true,false])) := by cases v <;> rfl
    exact ⟨_,⟨19,join0 (join0 h1 h2) h3⟩,rfl⟩
  | more b k w ih =>
    cases b with
    | false =>
      have h1 : run0 (table v) 9 (B (false::L) (rest (.more false k w))) = some (F L (true::true::false::false::(U (2*k+1)++enc w))) := by cases v <;> rfl
      exact ⟨_,⟨9,h1⟩,rfl⟩
    | true =>
      have h1 : run0 (table v) 5 (B (false::L) (rest (.more true k w))) = some (B (false::(mark++L)) (U (2*k+1)++enc w)) := by cases v <;> rfl
      have h2 := pairSweep v k (mark++L) (enc w)
      have h3 : run0 (table v) 2 (B (false::(U (2*k)++(mark++L))) (true::enc w)) = some (B (false::false::true::(U (2*k)++(mark++L))) (rest w)) := by cases v <;> rfl
      obtain ⟨R,h4,he⟩ := ih (false::true::(U (2*k)++(mark++L)))
      have h5 : run0 (table v) 2 (F (false::true::(U (2*k)++(mark++L))) R) = some (F (U (2*k)++(mark++L)) (false::false::R)) := by cases v <;> rfl
      have h6 := sweep (table v) (by cases v <;> rfl) (2*k) (mark++L) (false::false::R)
      have h7 : run0 (table v) 5 (F (mark++L) (U (2*k)++false::false::R)) = some (F L (markOut++(U (2*k)++false::false::R))) := by cases v <;> rfl
      refine ⟨_,reachTrans ⟨5,h1⟩ (reachTrans h2 (reachTrans ⟨2,h3⟩ (reachTrans h4 (reachTrans ⟨2,h5⟩ (reachTrans ⟨_,h6⟩ ⟨5,h7⟩))))),?_⟩
      rw [he]
      rfl
def startCost (v : Bool) := if v then 10 else 8
def cfg (w : Word) := F [] (U 3++enc w)
theorem advance (v : Bool) (w : Word) : ∃ t, 0<t ∧ run0 (table v) t (cfg w) = some (cfg (next w)) := by
  have h1 : run0 (table v) (startCost v) (cfg w) = some (B (false::false::U 4) (rest w)) := by cases v <;> rfl
  obtain ⟨R,h,he⟩ := scan v w (false::U 4)
  obtain ⟨a,ha⟩ := h
  have h3 : run0 (table v) 5 (F (false::U 4) R) = some (F [] (U 3++false::false::R)) := by cases v <;> rfl
  rw [he] at h3
  exact ⟨_,by cases v <;> simp [startCost] <;> omega,join0 (join0 h1 ha) h3⟩
def words : Nat → Word
  | 0 => .end0
  | n+1 => next (words n)
def family (n : Nat) := cfg (words n)
theorem entry (v : Bool) : run0 (table v) 11 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl
theorem growth_exists (v : Bool) (n : Nat) : ∃ t, 0<t ∧ run0 (table v) t (family n) = some (family (n+1)) := advance v (words n)
noncomputable def cost (v : Bool) (n : Nat) : Nat := Classical.choose (growth_exists v n)
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 11 (cost v) (entry v) (fun n => (Classical.choose_spec (growth_exists v n)).1)
    (fun n => (Classical.choose_spec (growth_exists v n)).2) m hm
#print axioms never
namespace V980
def table := BB6.Agent1Raw60LFSeparatorCounter.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent1Raw60LFSeparatorCounter.never false m hm
end V980
namespace V982
def table := BB6.Agent1Raw60LFSeparatorCounter.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent1Raw60LFSeparatorCounter.never true m hm
end V982
end BB6.Agent1Raw60LFSeparatorCounter
