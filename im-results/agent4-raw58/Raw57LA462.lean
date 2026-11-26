import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4Raw57LA462
open BB6Coverage Agent31Pump Agent50Zipper
inductive V where | v462 deriving DecidableEq, Repr

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
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,true,3⟩)
  | 5,true => some (some ⟨false,true,4⟩)
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

def pCost (_ : V) : Nat := 3

theorem init (v : V) (W : List Bool) : Moves v (root W) (cur [] W) := by
  refine ⟨7,by decide,?_⟩
  cases v <;> cases W <;> rfl

theorem scanP (v : V) (fs : List Frame) (W : List Bool) : Moves v (cur fs (P++W)) (cur (.short::fs) W) := by
  refine ⟨pCost v,by cases v <;> decide,?_⟩
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

inductive TWord where | end1 | digit (b c : Bool) (tail : TWord)
def bits : TWord → List Bool
 | .end1 => [true]
 | .digit b c t => [b,c,false]++bits t

def inc : TWord → TWord
 | .end1 => .digit false true .end1
 | .digit false c t => .digit true c t
 | .digit true true t => .digit false false t
 | .digit true false t => .digit false true (inc t)

def dcur (L : List Bool) (t : TWord) : Z0 := ⟨3,(bits t).headD false::false::true::L,(bits t).tail⟩

theorem termD0 (v : V) (L : List Bool) (c : Bool) (t : TWord) : Moves v (dcur L (.digit false c t)) ⟨0,true::L,false::bits (.digit true c t)⟩ := by
  exact ⟨4,by decide,by cases v <;> cases c <;> rfl⟩

theorem termD11 (v : V) (L : List Bool) (t : TWord) : Moves v (dcur L (.digit true true t)) ⟨0,true::L,false::bits (.digit false false t)⟩ := by
  exact ⟨6,by decide,by cases v <;> rfl⟩

theorem termDend (v : V) (L : List Bool) : Moves v (dcur L .end1) ⟨0,true::L,false::bits (.digit false true .end1)⟩ := by
  exact ⟨12,by decide,by cases v <;> rfl⟩

theorem carryD (v : V) (L : List Bool) (t : TWord) : Moves v (dcur L (.digit true false t)) (dcur ([true,false,true]++L) t) := by
  exact ⟨3,by decide,by cases v <;> cases t <;> rfl⟩

theorem popD (v : V) (L R : List Bool) : Moves v ⟨0,[true,true,false]++true::L,false::R⟩ ⟨0,true::L,[false,false,true,false]++R⟩ := by
  exact ⟨5,by decide,by cases v <;> rfl⟩

theorem updateD (v : V) (L : List Bool) (t : TWord) : Moves v (dcur L t) ⟨0,true::L,false::bits (inc t)⟩ := by
  induction t generalizing L with
  | end1 => exact termDend v L
  | digit b c t ih =>
    cases b
    · exact termD0 v L c t
    · cases c
      · exact moves_join (moves_join (carryD v L t) (ih ([true,false,true]++L))) (popD v L (bits (inc t)))
      · exact termD11 v L t

inductive Tail where | empty | nonempty (t : TWord)
def tailBits : Tail → List Bool
 | .empty => []
 | .nonempty t => false::bits t

def tailInc : Tail → Tail
 | .empty => .nonempty .end1
 | .nonempty t => .nonempty (inc t)

theorem enterD (v : V) (fs : List Frame) (t : TWord) : Moves v (cur fs ([false,true,true,false]++bits t)) (dcur ([true,true,true]++stack fs) t) := by
  exact ⟨6,by decide,by cases v <;> cases t <;> rfl⟩

theorem pop4 (v : V) (fs : List Frame) (R : List Bool) : Moves v ⟨0,[true,true,true,true]++stack fs,R⟩ ⟨0,stack fs,[true,true,true,true]++R⟩ := by
  exact ⟨4,by decide,by cases v <;> rfl⟩

theorem termSpecial (v : V) (fs : List Frame) (t : Tail) : Moves v (cur fs ([false,true,true]++tailBits t)) (root (out fs++P++[true,true]++tailBits (tailInc t))) := by
  cases t with
  | empty =>
    have h1 : Moves v (cur fs [false,true,true]) ⟨0,stack fs,[true,true,true,true,false,true]⟩ := ⟨14,by decide,by cases v <;> rfl⟩
    exact moves_join h1 (by simpa only [tailBits,tailInc,bits,List.append_assoc,List.cons_append,List.nil_append,P] using drain v fs [true,true,true,false,true])
  | nonempty t =>
    have h1 := moves_join (enterD v fs t) (updateD v ([true,true,true]++stack fs) t)
    have h2 := moves_join h1 (pop4 v fs (false::bits (inc t)))
    exact moves_join h2 (by simpa only [tailBits,tailInc,List.append_assoc,List.cons_append,List.nil_append,P] using drain v fs ([true,true,true,false]++bits (inc t)))

def conf (n : Nat) (t : Tail) := root (rep P n ++ [false,true,true] ++ tailBits t)

theorem grow (v : V) (n : Nat) (t : Tail) : Moves v (conf n t) (conf (n+2) (tailInc t)) := by
  have h := triple v n (true::tailBits (tailInc t)) ([false,true,true]++tailBits t) (by intro fs; simpa only [List.append_assoc,List.cons_append,List.nil_append,P] using termSpecial v fs t)
  simpa only [conf,List.append_assoc,List.cons_append,List.nil_append] using h

def entryCost (_ : V) : Nat := 63

theorem entry (v : V) : run0 (table v) (entryCost v) ⟨0,[],[]⟩ = some (conf 2 .empty) := by cases v <;> rfl

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t, k ≤ t ∧ ∃ n h, run0 (table v) t ⟨0,[],[]⟩ = some (conf n h) := by
    intro k
    induction k with
    | zero => exact ⟨entryCost v,Nat.zero_le _,2,.empty,entry v⟩
    | succ k ih =>
      obtain ⟨t,ht,n,h,hr⟩ := ih
      obtain ⟨c,hc,hgrow⟩ := grow v n h
      exact ⟨t+c,by omega,n+2,tailInc h,join0 hr hgrow⟩
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
end BB6Coverage.Agent4Raw57LA462
