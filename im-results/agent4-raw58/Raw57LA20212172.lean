import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4Raw57LA20212172
open BB6Coverage Agent31Pump Agent50Zipper
inductive V where | v2021 | v2172 deriving DecidableEq, Repr

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨decide (v = .v2172),true,if v = .v2172 then 2 else 4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | _,_ => none
abbrev A : List Bool := [false,true,true,false,true,true]
abbrev B : List Bool := [false,true,false,false,true,true]
abbrev frame : List Bool := [true,true,false,true,true,false]
abbrev U : List Bool := [true,true]
inductive Word where | empty | end1 | a (tail : Word) | b (tail : Word)
def bits : Word → List Bool
 | .empty => []
 | .end1 => [false,true]
 | .a w => A++bits w
 | .b w => B++bits w

def inc : Word → Word
 | .empty => .end1
 | .end1 => .a .empty
 | .a w => .b w
 | .b w => .a (inc w)

def Moves (v : V) (a b : Z0) : Prop := ∃ k,0<k ∧ run0 (table v) k a = some b

theorem join {v a b c} (h : Moves v a b) (g : Moves v b c) : Moves v a c := by
 obtain ⟨n,hn,hr⟩ := h; obtain ⟨k,hk,hs⟩ := g
 exact ⟨n+k,by omega,join0 hr hs⟩

def root (n : Nat) (w : Word) : Z0 := ⟨0,[],rep U (n+1)++bits w⟩
def cur (L : List Bool) (w : Word) : Z0 := ⟨2,false::true::L,(bits w).tail⟩
def scanCost (v : V) := if v = .v2021 then 4 else 2

theorem init (v : V) (W : List Bool) : run0 (table v) 5 ⟨0,[],[true,true]++W⟩ = some ⟨2,[true,true,true],[true]++W⟩ := by cases v <;> rfl

theorem scanPair (v : V) (L R : List Bool) : run0 (table v) (scanCost v) ⟨2,true::L,U++R⟩ = some ⟨2,true::true::true::L,R⟩ := by cases v <;> rfl

theorem scanMany (v : V) (n : Nat) (R : List Bool) : run0 (table v) (scanCost v*n) ⟨2,[true,true,true],rep U n++R⟩ = some ⟨2,true::rep U n++[true,true],R⟩ := by
  simpa only [List.nil_append,List.append_assoc,List.cons_append,List.nil_append,U] using sweepR (table v) 2 [true] [] U U (scanCost v) (by intro L R; exact scanPair v L R) n [true,true] R

theorem scanEnd (v : V) (L : List Bool) (w : Word) : run0 (table v) (scanCost v) ⟨2,true::L,true::bits w⟩ = some (cur (true::L) w) := by cases v <;> cases w <;> rfl

theorem enter (v : V) (n : Nat) (w : Word) : Moves v (root n w) (cur (true::(rep U n++[true,true])) w) := by
  have h1 := init v (rep U n++bits w)
  have hrot := rotate true [true] n
  have h2 := scanMany v n (true::bits w)
  have h2' : run0 (table v) (scanCost v*n) ⟨2,[true,true,true],true::(rep U n++bits w)⟩ = some ⟨2,true::rep U n++[true,true],true::bits w⟩ := by
    rw [show true::(rep U n++bits w) = rep U n++true::bits w by simpa only [List.append_assoc,List.cons_append,List.nil_append,U] using congrArg (fun l => l++bits w) hrot]
    exact h2
  have h3 := scanEnd v (rep U n++[true,true]) w
  refine ⟨5+scanCost v*n+scanCost v,by omega,?_⟩
  have h := join0 (join0 h1 h2') h3
  exact h

theorem carry (v : V) (L : List Bool) (w : Word) : Moves v (cur L (.b w)) (cur ([true,false,true,true,false,true]++L) w) := by
  refine ⟨if v = .v2021 then 8 else 6,by cases v <;> decide,?_⟩
  cases v <;> cases w <;> rfl

theorem termA (v : V) (L : List Bool) (w : Word) : Moves v (cur L (.a w)) ⟨0,true::L,B++bits w⟩ := by
  exact ⟨7,by decide,by cases v <;> rfl⟩

theorem termEnd (v : V) (L : List Bool) : Moves v (cur L .end1) ⟨0,true::L,A⟩ := by
  exact ⟨15,by decide,by cases v <;> rfl⟩

theorem termEmpty (v : V) (L : List Bool) : Moves v (cur L .empty) ⟨0,true::L,[false,true]⟩ := by
  exact ⟨5,by decide,by cases v <;> rfl⟩

theorem popFrame (v : V) (L R : List Bool) : Moves v ⟨0,frame++true::L,R⟩ ⟨0,true::L,A++R⟩ := by
  exact ⟨10,by decide,by cases v <;> rfl⟩

theorem update (v : V) (L : List Bool) (w : Word) : Moves v (cur L w) ⟨0,true::L,bits (inc w)⟩ := by
  induction w generalizing L with
  | empty => exact termEmpty v L
  | end1 => exact termEnd v L
  | a w => exact termA v L w
  | b w ih =>
    have h1 := carry v L w
    have h2 := ih ([true,false,true,true,false,true]++L)
    have h3 := popFrame v L (bits (inc w))
    -- The cursor's fixed one is part of the frame; adjust the frame prefix.
    exact join (join h1 h2) h3

theorem popOne (v : V) (L R : List Bool) : run0 (table v) 1 ⟨0,true::L,R⟩ = some ⟨0,L,true::R⟩ := by cases v <;> rfl

theorem popAll (v : V) (n : Nat) (R : List Bool) : Moves v ⟨0,rep U (n+2),R⟩ ⟨0,[],rep U (n+2)++R⟩ := by
  refine ⟨2*(n+2),by omega,?_⟩
  simpa only [List.nil_append,List.append_nil] using sweepL (table v) 0 [] [] U U 2 (by intro L R; cases v <;> rfl) (n+2) [] R

theorem grow (v : V) (n : Nat) (w : Word) : Moves v (root n w) (root (n+1) (inc w)) := by
  have h := join (enter v n w) (update v (true::(rep U n++[true,true])) w)
  have he : true::true::(rep U n++[true,true]) = rep U (n+2) := by
    rw [show rep U n++[true,true] = rep U (n+1) by rw [rep,rep_snoc]]
    rfl
  rw [he] at h
  exact join h (popAll v n (bits (inc w)))

theorem entry (v : V) : run0 (table v) 9 ⟨0,[],[]⟩ = some (root 0 .end1) := by cases v <;> rfl

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t, k ≤ t ∧ ∃ w, run0 (table v) t ⟨0,[],[]⟩ = some (root k w) := by
    intro k; induction k with
    | zero => exact ⟨9,by decide,.end1,entry v⟩
    | succ k ih =>
      obtain ⟨t,ht,w,hr⟩ := ih
      obtain ⟨c,hc,hg⟩ := grow v k w
      exact ⟨t+c,by omega,inc w,join0 hr hg⟩
  intro n
  obtain ⟨t,ht,w,hr⟩ := arbitrary n
  have hz : (zrun (table v) t start).map project = some (root n w) := (run_project (table v) t start).trans hr
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
end BB6Coverage.Agent4Raw57LA20212172
