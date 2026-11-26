import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4Raw57LASeven
open BB6Coverage Agent31Pump Agent50Zipper
inductive V where | v270 | v404 | v407 | v443 | v474 | v475 | v486 deriving DecidableEq, Repr

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,if v = .v486 then 5 else 4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => if v = .v404 || v = .v407 then some (some ⟨false,true,5⟩) else if v = .v443 then some (some ⟨true,true,5⟩) else none
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨decide (v ≠ .v270 ∧ v ≠ .v486),true,if v = .v404 || v = .v407 || v = .v443 then 2 else 5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,decide (v = .v443 ∨ v = .v475),if v = .v407 then 4 else if v = .v443 || v = .v475 then 3 else if v = .v474 then 5 else 1⟩)
  | 5,true => if v = .v270 || v = .v486 then some (some ⟨false,false,0⟩) else if v = .v474 || v = .v475 then some (some ⟨true,true,2⟩) else none
  | _,_ => none

abbrev P : List Bool := [false,false,true]
abbrev Q : List Bool := [false,true,false,true]
inductive Frame where | short | long

def stack : List Frame → List Bool
 | [] => [false,true,true]
 | .short::fs => [false,true,true] ++ stack fs
 | .long::fs => [false,true,true,true] ++ stack fs

def out : List Frame → List Bool
 | [] => []
 | .short::fs => out fs ++ P
 | .long::fs => out fs ++ [false,false,true,true]

def cur (fs : List Frame) (W : List Bool) : Z0 := ⟨4,W.headD false :: true :: stack fs,W.tail⟩
def root (W : List Bool) : Z0 := ⟨0,[],[true,true] ++ W⟩
def Moves (v : V) (a b : Z0) : Prop := ∃ k, 0 < k ∧ run0 (table v) k a = some b

theorem moves_join {v a b c} (h : Moves v a b) (g : Moves v b c) : Moves v a c := by
  obtain ⟨n,hn,hr⟩ := h
  obtain ⟨k,hk,hs⟩ := g
  exact ⟨n+k,by omega,join0 hr hs⟩

def pCost (v : V) := if v = .v270 || v = .v474 || v = .v486 then 5 else 3
def qCost (v : V) := if v = .v443 || v = .v474 || v = .v475 then 4 else 6

theorem init (v : V) (W : List Bool) : Moves v (root W) (cur [] W) := by
  refine ⟨7,by decide,?_⟩
  cases v <;> cases W <;> rfl

theorem scanP (v : V) (fs : List Frame) (W : List Bool) : Moves v (cur fs (P++W)) (cur (.short::fs) W) := by
  refine ⟨pCost v,by cases v <;> decide,?_⟩
  cases v <;> cases W <;> rfl

theorem scanQ (v : V) (fs : List Frame) (W : List Bool) : Moves v (cur fs (Q++W)) (cur (.long::fs) W) := by
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

theorem term000 (v : V) (fs : List Frame) (R : List Bool) : Moves v (cur fs ([false,false,false]++R)) (root (out fs ++ [false,false,true,false,true] ++ R)) := by
  apply moves_join (b := ⟨0,stack fs,[true,true,false,true]++R⟩)
  · exact ⟨pCost v+5,by omega,by cases v <;> rfl⟩
  · simpa only [List.append_assoc,List.cons_append,List.nil_append,P,Q] using drain v fs ([true,false,true]++R)

theorem term0100 (v : V) (fs : List Frame) (R : List Bool) : Moves v (cur fs ([false,true,false,false]++R)) (root (out fs ++ [false,false,true,true,false,true] ++ R)) := by
  apply moves_join (b := ⟨0,stack fs,[true,true,true,false,true]++R⟩)
  · exact ⟨qCost v+6,by omega,by cases v <;> rfl⟩
  · simpa only [List.append_assoc,List.cons_append,List.nil_append,P,Q] using drain v fs ([true,true,false,true]++R)

theorem termEmpty (v : V) (fs : List Frame) (W : List Bool) (h : W = [] ∨ W = [false]) : Moves v (cur fs W) (root (out fs ++ [false,false,true,false,true])) := by
  apply moves_join (b := ⟨0,stack fs,[true,true,false,true]⟩)
  · rcases h with rfl|rfl <;> exact ⟨pCost v+5,by omega,by cases v <;> rfl⟩
  · simpa only [List.append_assoc,List.cons_append,List.nil_append,P,Q] using drain v fs [true,false,true]

inductive HWord where
 | nil | bit (b : Bool) | short (b c : Bool) (tail : HWord) | long (b c : Bool) (tail : HWord)
def bits : HWord → List Bool
 | .nil => []
 | .bit b => [b]
 | .short b c h => [b,false,c] ++ bits h
 | .long b c h => [b,true,false,c] ++ bits h

def hStep : HWord → HWord
 | .nil => .short true true .nil
 | .bit true => .bit false
 | .bit false => .short true true .nil
 | .short true c h => .short false c h
 | .short false false h => .short true true h
 | .short false true h => .short true false (hStep h)
 | .long true c h => .long false c h
 | .long false false h => .long true true h
 | .long false true h => .long true false (hStep h)

theorem h_sound (v : V) (h : HWord) (fs : List Frame) : Moves v (cur fs (bits h)) (root (out fs ++ [false,false] ++ bits (hStep h))) := by
  induction h generalizing fs with
  | nil => simpa only [bits,hStep,List.append_assoc,List.cons_append,List.nil_append,P,Q] using termEmpty v fs [] (Or.inl rfl)
  | bit b =>
    cases b
    · simpa only [bits,hStep,List.append_assoc,List.cons_append,List.nil_append,P,Q] using termEmpty v fs [false] (Or.inr rfl)
    · simpa only [bits,hStep,List.append_assoc,List.cons_append,List.nil_append,P,Q] using term1 v fs []
  | short b c h ih =>
    cases b
    · cases c
      · simpa only [bits,hStep,List.append_assoc,List.cons_append,List.nil_append,P,Q] using term000 v fs (bits h)
      · exact moves_join (scanP v fs (bits h)) (by simpa only [bits,hStep,out,List.append_assoc,List.cons_append,List.nil_append,P,Q] using ih (.short::fs))
    · simpa only [bits,hStep,List.append_assoc,List.cons_append,List.nil_append,P,Q] using term1 v fs ([false,c]++bits h)
  | long b c h ih =>
    cases b
    · cases c
      · simpa only [bits,hStep,List.append_assoc,List.cons_append,List.nil_append,P,Q] using term0100 v fs (bits h)
      · exact moves_join (scanQ v fs (bits h)) (by simpa only [bits,hStep,out,List.append_assoc,List.cons_append,List.nil_append,P,Q] using ih (.long::fs))
    · simpa only [bits,hStep,List.append_assoc,List.cons_append,List.nil_append,P,Q] using term1 v fs ([true,false,c]++bits h)

theorem pref (v : V) (n : Nat) (fs : List Frame) (W W' : List Bool) (h : ∀ fs, Moves v (cur fs W) (root (out fs ++ W'))) : Moves v (cur fs (rep P n ++ W)) (root (out fs ++ rep P n ++ W')) := by
  induction n generalizing fs with
  | zero => simpa [rep] using h fs
  | succ n ih => exact moves_join (scanP v fs (rep P n++W)) (by simpa only [rep,out,List.append_assoc,List.cons_append,List.nil_append,P,Q] using ih (.short::fs))

theorem rootPref (v : V) (n : Nat) (W W' : List Bool) (h : ∀ fs, Moves v (cur fs W) (root (out fs ++ W'))) : Moves v (root (rep P n ++ W)) (root (rep P n ++ W')) := by
  exact moves_join (init v _) (by simpa only [out,List.nil_append] using pref v n [] W W' h)

theorem triple (v : V) (n : Nat) (X W : List Bool) (h : ∀ fs, Moves v (cur fs W) (root (out fs ++ P ++ [true] ++ X))) : Moves v (root (rep P n ++ W)) (root (rep P (n+2) ++ [false,true] ++ X)) := by
  have hp (k : Nat) : rep P (k+1) = rep P k ++ P := by rw [rep,rep_snoc]
  have h1 := rootPref v n W (P++[true]++X) (by intro fs; simpa only [List.append_assoc,List.cons_append,List.nil_append,P,Q] using h fs)
  have h1' : Moves v (root (rep P n++W)) (root (rep P (n+1)++true::X)) := by simpa only [hp,List.append_assoc,List.cons_append,List.nil_append,P,Q] using h1
  have h2 := rootPref v (n+1) (true::X) ([false,false,false]++X) (by intro fs; simpa only [List.append_assoc,List.cons_append,List.nil_append,P,Q] using term1 v fs X)
  have h3 := rootPref v (n+1) ([false,false,false]++X) ([false,false,true,false,true]++X) (by intro fs; simpa only [List.append_assoc,List.cons_append,List.nil_append,P,Q] using term000 v fs X)
  have h3' : Moves v (root (rep P (n+1)++[false,false,false]++X)) (root (rep P (n+2)++[false,true]++X)) := by simpa only [hp (n+1),List.append_assoc,List.cons_append,List.nil_append,P,Q] using h3
  exact moves_join (moves_join h1' h2) (by simpa only [List.append_assoc,List.cons_append,List.nil_append,P,Q] using h3')

def conf (n : Nat) (h : HWord) := root (rep P n ++ Q ++ bits h)

theorem sixPhase (v : V) (n : Nat) (h : HWord) : Moves v (conf n h) (conf (n+4) (hStep h)) := by
  have h1 := triple v n ([false,false]++bits (hStep h)) (Q++bits h) (by
    intro fs
    exact moves_join (scanQ v fs (bits h)) (by simpa only [out,List.append_assoc,List.cons_append,List.nil_append,P,Q] using h_sound v h (.long::fs)))
  have h2 := triple v (n+2) ([false,true]++bits (hStep h)) ([false,true,false,false]++bits (hStep h)) (by
    intro fs
    simpa only [List.append_assoc,List.cons_append,List.nil_append,P,Q] using term0100 v fs (bits (hStep h)))
  exact moves_join (by simpa only [conf,List.append_assoc,List.cons_append,List.nil_append,P,Q] using h1) (by simpa only [conf,List.append_assoc,List.cons_append,List.nil_append,P,Q] using h2)

def entryCost : V → Nat
 | .v270 | .v486 => 89
 | .v404 | .v407 => 83
 | .v443 | .v475 => 81
 | .v474 => 87

theorem entry (v : V) : run0 (table v) (entryCost v) ⟨0,[],[]⟩ = some (conf 2 .nil) := by cases v <;> rfl

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t, k ≤ t ∧ ∃ n h, run0 (table v) t ⟨0,[],[]⟩ = some (conf n h) := by
    intro k
    induction k with
    | zero => exact ⟨entryCost v,Nat.zero_le _,2,.nil,entry v⟩
    | succ k ih =>
      obtain ⟨t,ht,n,h,hr⟩ := ih
      obtain ⟨c,hc,hgrow⟩ := sixPhase v n h
      exact ⟨t+c,by omega,n+4,hStep h,join0 hr hgrow⟩
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
end BB6Coverage.Agent4Raw57LASeven
