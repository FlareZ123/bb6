import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4Raw57LA274276
open BB6Coverage Agent31Pump Agent50Zipper
inductive V where | v274 | v276 deriving DecidableEq, Repr

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => none
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨decide (v = .v276),true,if v = .v276 then 1 else 0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

abbrev P : List Bool := [false,false,true,true]
abbrev Q : List Bool := [false,true,true]
inductive Frame where | short | long

def stack : List Frame → List Bool
 | [] => [false,true,true]
 | .short::fs => [false,true,true] ++ stack fs
 | .long::fs => [false,true,true,true] ++ stack fs

def out : List Frame → List Bool
 | [] => []
 | .short::fs => out fs ++ [false,false,true]
 | .long::fs => out fs ++ P

def cur (fs : List Frame) (W : List Bool) : Z0 := ⟨4,W.headD false :: true :: stack fs,W.tail⟩
def root (W : List Bool) : Z0 := ⟨0,[],[true,true] ++ W⟩
def Moves (v : V) (a b : Z0) : Prop := ∃ k, 0 < k ∧ run0 (table v) k a = some b

theorem moves_join {v a b c} (h : Moves v a b) (g : Moves v b c) : Moves v a c := by
  obtain ⟨n,hn,hr⟩ := h
  obtain ⟨k,hk,hs⟩ := g
  exact ⟨n+k,by omega,join0 hr hs⟩

def pCost (v : V) : Nat := if v = .v274 then 10 else 8
def qCost (_ : V) : Nat := 5

theorem init (v : V) (W : List Bool) : Moves v (root W) (cur [] W) := by
  refine ⟨7,by decide,?_⟩
  cases v <;> cases W <;> rfl

theorem scanP (v : V) (fs : List Frame) (W : List Bool) : Moves v (cur fs (P++W)) (cur (.long::fs) W) := by
  refine ⟨pCost v,by cases v <;> decide,?_⟩
  cases v <;> cases W <;> rfl

theorem scanQ (v : V) (fs : List Frame) (W : List Bool) : Moves v (cur fs (Q++W)) (cur (.short::fs) W) := by
  refine ⟨qCost v,by cases v <;> decide,?_⟩
  cases v <;> cases W <;> rfl

theorem leftS (v : V) (L R : List Bool) : run0 (table v) 5 ⟨0,[false,true,true]++L,true::R⟩ = some ⟨0,L,[true,true,false,false]++R⟩ := by cases v <;> rfl

theorem leftL (v : V) (L R : List Bool) : run0 (table v) 6 ⟨0,[false,true,true,true]++L,true::R⟩ = some ⟨0,L,[true,true,true,false,false]++R⟩ := by cases v <;> rfl

theorem drain (v : V) (fs : List Frame) (R : List Bool) : Moves v ⟨0,stack fs,true::R⟩ (root (out fs ++ [false,false] ++ R)) := by
  induction fs generalizing R with
  | nil => exact ⟨5,by decide,leftS v [] R⟩
  | cons f fs ih =>
    cases f
    · exact moves_join ⟨5,by decide,leftS v (stack fs) R⟩ (by simpa only [out,List.append_assoc,List.cons_append,List.nil_append,P,Q] using ih ([true,false,false]++R))
    · exact moves_join ⟨6,by decide,leftL v (stack fs) R⟩ (by simpa only [out,List.append_assoc,List.cons_append,List.nil_append,P,Q] using ih ([true,true,false,false]++R))

theorem term1 (v : V) (fs : List Frame) (R : List Bool) : Moves v (cur fs (true::R)) (root (out fs ++ [false,false,false] ++ R)) := by
  apply moves_join (b := ⟨0,stack fs,[true,false]++R⟩)
  · exact ⟨2,by decide,by cases v <;> rfl⟩
  · simpa only [List.append_assoc,List.cons_append,List.nil_append,P,Q] using drain v fs (false::R)

theorem term010 (v : V) (fs : List Frame) (R : List Bool) : Moves v (cur fs ([false,true,false]++R)) (root (out fs ++ [false,false,true,false,true] ++ R)) := by
  apply moves_join (b := ⟨0,stack fs,[true,true,false,true]++R⟩)
  · exact ⟨10,by decide,by cases v <;> rfl⟩
  · simpa only [List.append_assoc,List.cons_append,List.nil_append,P,Q] using drain v fs ([true,false,true]++R)

theorem term0010 (v : V) (fs : List Frame) (R : List Bool) : Moves v (cur fs ([false,false,true,false]++R)) (root (out fs ++ P ++ [false,true] ++ R)) := by
  apply moves_join (b := ⟨0,stack fs,[true,true,true,false,true]++R⟩)
  · exact ⟨pCost v+6,by omega,by cases v <;> rfl⟩
  · simpa only [List.append_assoc,List.cons_append,List.nil_append,P,Q] using drain v fs ([true,true,false,true]++R)

theorem term01 (v : V) (fs : List Frame) : Moves v (cur fs [false,true]) (root (out fs ++ [false,false,true,false,true])) := by
  apply moves_join (b := ⟨0,stack fs,[true,true,false,true]⟩)
  · exact ⟨10,by decide,by cases v <;> rfl⟩
  · simpa only [List.append_assoc,List.cons_append,List.nil_append,P,Q] using drain v fs [true,false,true]

theorem term001 (v : V) (fs : List Frame) : Moves v (cur fs [false,false,true]) (root (out fs ++ P ++ [false,true])) := by
  apply moves_join (b := ⟨0,stack fs,[true,true,true,false,true]⟩)
  · exact ⟨pCost v+6,by omega,by cases v <;> rfl⟩
  · simpa only [List.append_assoc,List.cons_append,List.nil_append,P,Q] using drain v fs [true,true,false,true]

mutual
inductive DWord where
 | empty | one | digit (b c : Bool) (tail : BWord)
inductive BWord where
 | empty | one | digit (b : Bool) (tail : DWord)
end
mutual
def dbits : DWord → List Bool
 | .empty => []
 | .one => [true]
 | .digit b c t => [b,c]++bbits t
def bbits : BWord → List Bool
 | .empty => []
 | .one => [true]
 | .digit b t => [b,!b]++dbits t
end

def overflow (v : V) : DWord := if v = .v274 then .digit false true (.digit true (.digit false true (.digit false .empty))) else .digit false false (.digit false (.digit false true .empty))
mutual
def incD (v : V) : DWord → DWord
 | .empty => .one
 | .one => overflow v
 | .digit false c t => .digit true c t
 | .digit true true t => .digit false false t
 | .digit true false t => carryB v t
def carryB (v : V) : BWord → DWord
 | .empty => overflow v
 | .one => .digit false true (.digit false .empty)
 | .digit true t => .digit false true (.digit false t)
 | .digit false t => .digit false true (.digit true (incD v t))
end

theorem termZero (v : V) (fs : List Frame) (W : List Bool) (h : W = [] ∨ W = [false]) : Moves v (cur fs W) (root (out fs ++ false::dbits (overflow v))) := by
  rcases h with rfl|rfl <;> cases v
  · change Moves .v274 _ (root (out fs++[false,false,true,true,false,false,true,false,true]))
    exact moves_join (b := ⟨0,stack fs,[true,true,true,false,false,true,false,true]⟩) ⟨34,by decide,by rfl⟩ (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using drain .v274 fs [true,true,false,false,true,false,true])
  · change Moves .v276 _ (root (out fs++[false,false,false,false,true,false,true]))
    exact moves_join (b := ⟨0,stack fs,[true,false,false,true,false,true]⟩) ⟨14,by decide,by rfl⟩ (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using drain .v276 fs [false,false,true,false,true])
  · change Moves .v274 _ (root (out fs++[false,false,true,true,false,false,true,false,true]))
    exact moves_join (b := ⟨0,stack fs,[true,true,true,false,false,true,false,true]⟩) ⟨34,by decide,by rfl⟩ (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using drain .v274 fs [true,true,false,false,true,false,true])
  · change Moves .v276 _ (root (out fs++[false,false,false,false,true,false,true]))
    exact moves_join (b := ⟨0,stack fs,[true,false,false,true,false,true]⟩) ⟨14,by decide,by rfl⟩ (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using drain .v276 fs [false,false,true,false,true])

mutual
theorem inc_sound (v : V) (fs : List Frame) (d : DWord) : Moves v (cur fs ([false,false,true]++dbits d)) (root (out fs++[false,false,true,true,false]++dbits (incD v d))) := by
  cases d with
  | empty => simpa only [dbits,incD,List.append_assoc,List.cons_append,List.nil_append,P] using term001 v fs
  | one => exact moves_join (scanP v fs []) (by simpa only [out,incD,dbits,List.append_assoc,List.cons_append,List.nil_append,P] using termZero v (.long::fs) [] (Or.inl rfl))
  | digit b c t =>
    cases b
    · simpa only [dbits,incD,List.append_assoc,List.cons_append,List.nil_append,P] using term0010 v fs (c::bbits t)
    · cases c
      · exact moves_join (scanP v fs (false::bbits t)) (by simpa only [dbits,incD,out,List.append_assoc,List.cons_append,List.nil_append,P] using carry_sound v (.long::fs) t)
      · exact moves_join (scanP v fs (true::bbits t)) (by simpa only [dbits,incD,out,List.append_assoc,List.cons_append,List.nil_append,P] using term1 v (.long::fs) (bbits t))
termination_by sizeOf d

theorem carry_sound (v : V) (fs : List Frame) (b : BWord) : Moves v (cur fs (false::bbits b)) (root (out fs++false::dbits (carryB v b))) := by
  cases b with
  | empty => exact termZero v fs [false] (Or.inr rfl)
  | one => simpa only [bbits,carryB,dbits,List.append_assoc,List.cons_append,List.nil_append,Bool.not_false,Bool.not_true] using term01 v fs
  | digit b d =>
    cases b
    · simpa only [bbits,carryB,dbits,List.append_assoc,List.cons_append,List.nil_append,Bool.not_false,Bool.not_true] using inc_sound v fs d
    · simpa only [bbits,carryB,dbits,List.append_assoc,List.cons_append,List.nil_append,Bool.not_false,Bool.not_true] using term010 v fs (dbits d)
termination_by sizeOf b
end

theorem firstPhase (v : V) (fs : List Frame) (d : DWord) : Moves v (cur fs ([false,true]++dbits d)) (root (out fs++[false,false,true,false]++dbits (incD v d))) := by
  cases d with
  | empty => simpa only [dbits,incD,List.append_assoc,List.cons_append,List.nil_append,Bool.not_false,Bool.not_true] using term01 v fs
  | one => exact moves_join (scanQ v fs []) (by simpa only [out,dbits,incD,List.append_assoc,List.cons_append,List.nil_append] using termZero v (.short::fs) [] (Or.inl rfl))
  | digit b c t =>
    cases b
    · simpa only [dbits,incD,List.append_assoc,List.cons_append,List.nil_append,Bool.not_false,Bool.not_true] using term010 v fs (c::bbits t)
    · cases c
      · exact moves_join (scanQ v fs (false::bbits t)) (by simpa only [dbits,incD,out,List.append_assoc,List.cons_append,List.nil_append] using carry_sound v (.short::fs) t)
      · exact moves_join (scanQ v fs (true::bbits t)) (by simpa only [dbits,incD,out,List.append_assoc,List.cons_append,List.nil_append] using term1 v (.short::fs) (bbits t))

theorem pref (v : V) (n : Nat) (fs : List Frame) (W W' : List Bool) (h : ∀ fs, Moves v (cur fs W) (root (out fs ++ W'))) : Moves v (cur fs (rep P n ++ W)) (root (out fs ++ rep P n ++ W')) := by
  induction n generalizing fs with
  | zero => simpa [rep] using h fs
  | succ n ih => exact moves_join (scanP v fs (rep P n++W)) (by simpa only [rep,out,List.append_assoc,List.cons_append,List.nil_append,P,Q] using ih (.long::fs))

theorem rootPref (v : V) (n : Nat) (W W' : List Bool) (h : ∀ fs, Moves v (cur fs W) (root (out fs ++ W'))) : Moves v (root (rep P n ++ W)) (root (rep P n ++ W')) := by
  exact moves_join (init v _) (by simpa only [out,List.nil_append] using pref v n [] W W' h)

def conf (n : Nat) (d : DWord) := root (rep P n ++ [false,true] ++ dbits d)

theorem grow (v : V) (n : Nat) (d : DWord) : Moves v (conf n d) (conf (n+1) (incD v d)) := by
  have hp : rep P (n+1) = rep P n++P := by rw [rep,rep_snoc]
  have h1 := rootPref v n ([false,true]++dbits d) ([false,false,true,false]++dbits (incD v d)) (by intro fs; simpa only [List.append_assoc] using firstPhase v fs d)
  have h2 := rootPref v n ([false,false,true,false]++dbits (incD v d)) (P++[false,true]++dbits (incD v d)) (by intro fs; simpa only [List.append_assoc] using term0010 v fs (dbits (incD v d)))
  exact moves_join (by simpa only [conf,List.append_assoc] using h1) (by simpa only [conf,hp,List.append_assoc] using h2)

def entryCost (_ : V) : Nat := 9

theorem entry (v : V) : run0 (table v) (entryCost v) ⟨0,[],[]⟩ = some (conf 0 .empty) := by cases v <;> rfl

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t, k ≤ t ∧ ∃ n h, run0 (table v) t ⟨0,[],[]⟩ = some (conf n h) := by
    intro k
    induction k with
    | zero => exact ⟨entryCost v,Nat.zero_le _,0,.empty,entry v⟩
    | succ k ih =>
      obtain ⟨t,ht,n,h,hr⟩ := ih
      obtain ⟨c,hc,hgrow⟩ := grow v n h
      exact ⟨t+c,by omega,n+1,incD v h,join0 hr hgrow⟩
  intro n
  obtain ⟨t,ht,k,h,hr⟩ := arbitrary n
  have hz : (zrun (table v) t start).map project = some (conf k h) := (run_project (table v) t start).trans hr
  cases he : zrun (table v) t start with
  | none => simp [he] at hz
  | some z =>
    have H := zrun_sound (table v) m hm t start z he
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases hn : run m n blank with
    | none => simp [hn] at H
    | some c => rfl
#print axioms never
end BB6Coverage.Agent4Raw57LA274276
