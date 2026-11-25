import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw107LAPairCounter
open BB6Coverage BB6Coverage.Agent31Pump
inductive V | a | b | c | d deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some (match v with
      | .a => ⟨false,false,0⟩
      | .b => ⟨false,false,2⟩
      | .c => ⟨true,false,1⟩
      | .d => ⟨true,false,3⟩))
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none
abbrev P := [false,true]
abbrev Q := [false,true,false,true]
abbrev W := [false,false,false,true]
abbrev H := [true,false,true]
abbrev J := [false,false,true]
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev B (L R : List Bool) : Z0 := ⟨1,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
def mark (b : Bool) : List Bool := [b,b]
def rwrd (k : Nat) (b : Bool) := [true]++rep P k++mark b
def bwrd (k : Nat) (b : Bool) := rep P k++mark b
def out (v : V) (n : Nat) (b : Bool) := if v=.a then (if n=0 then !b else b) else true

def Reach (v : V) (c d : Z0) : Prop := ∃ t : Nat, run0 (table v) t c = some d
theorem reach_zero (v : V) (c : Z0) : Reach v c c := ⟨0,rfl⟩
theorem reach_of {v c d t} (h : run0 (table v) t c = some d) : Reach v c d := ⟨t,h⟩
theorem join {v c d e} (h : Reach v c d) (h' : Reach v d e) : Reach v c e := by
  obtain ⟨t,ht⟩:=h; obtain ⟨u,hu⟩:=h'; exact ⟨t+u,join0 ht hu⟩

theorem rep_add (X : List Bool) (n m : Nat) : rep X n++rep X m=rep X (n+m) := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.append_assoc,ih,show n+1+m=n+m+1 by omega]
theorem even_pairs (n : Nat) : rep P (2*n) = rep Q n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2*(n+1)=2*n+1+1 by omega]; simp only [rep,ih]; rfl

theorem start (v : V) (L R : List Bool) : run0 (table v) 4 (B (J++L) (Q++R)) = some (F (H++Q++L) R) := by cases v <;> rfl
theorem f_one (v : V) (L R : List Bool) : run0 (table v) 4 (F (H++L) (Q++R)) = some (F (H++W++L) R) := by cases v <;> rfl
theorem f_many (v : V) (n : Nat) (L R : List Bool) : run0 (table v) (4*n) (F (H++L) (rep Q n++R)) = some (F (H++rep W n++L) R) := by
  simpa only [List.nil_append] using sweepR (table v) 5 H [] Q W 4 (f_one v) n L R

def turnCost (v : V) (b : Bool) : Nat := if b then (match v with | .a => 11 | .b => 13 | .c => 9 | .d => 11) else 13
theorem f_turn (v : V) (b : Bool) (L : List Bool) : run0 (table v) (turnCost v b) (F (H++L) (mark b)) = some (A L (rwrd 1 (out v 0 b))) := by cases v <;> cases b <;> rfl

theorem a_pair (v : V) (L R : List Bool) : run0 (table v) 4 (A (P++L) (true::R)) = some (A L (true::(P++R))) := by cases v <;> rfl
theorem a_two (v : V) (k : Nat) (b : Bool) (L : List Bool) : Reach v (A (Q++L) (rwrd k b)) (A L (rwrd (k+2) b)) := by
  have h1 := a_pair v (P++L) (rep P k++mark b)
  have h2 := a_pair v L (P++(rep P k++mark b))
  exact reach_of (join0 h1 h2)

theorem a_block (v : V) (j : Nat) (b : Bool) (L : List Bool) : run0 (table v) 3 (A (W++L) (rwrd (2*j+1) b)) = some (B (J++L) (bwrd (2*j+2) b)) := by
  unfold rwrd bwrd
  rw [show 2*j+2=(2*j+1)+1 by omega]
  cases v <;> rfl

theorem out_stable (v : V) (j : Nat) (b : Bool) (hj : 0<j) (hb : v=.a ∨ b=true) : out v j b=b := by
  unfold out; split
  · simp [show j≠0 by omega]
  · rcases hb with h|h
    · contradiction
    · exact h.symm

theorem out_twice (v : V) (b : Bool) : out v 0 (out v 0 b)= (if v=.a then b else true) := by cases v <;> cases b <;> rfl

theorem walk (v : V) (N : Nat) (small : ∀ j, j<N → ∀ b L, Reach v (B (J++L) (bwrd (2*j+2) b)) (A L (rwrd (2*j+3) (out v j b))))
    (j k : Nat) (b : Bool) (L : List Bool) (hj : 0<j) (hk : j+k≤N) (hb : v=.a ∨ b=true) :
    Reach v (A (rep W k++L) (rwrd (2*j+1) b)) (A L (rwrd (2*(j+k)+1) b)) := by
  induction k generalizing j with
  | zero => simpa only [rep,List.nil_append,Nat.add_zero] using reach_zero v (A L (rwrd (2*j+1) b))
  | succ k ih =>
    have h1 := reach_of (a_block v j b (rep W k++L))
    have h2 := small j (by omega) b (rep W k++L)
    rw [out_stable v j b hj hb,show 2*j+3=2*(j+1)+1 by omega] at h2
    have h3 := ih (j+1) (by omega) (by omega)
    have h := join (join h1 h2) h3
    simpa only [rep,List.append_assoc,show j+1+k=j+(k+1) by omega] using h

theorem beginB (v : V) (n : Nat) (b : Bool) (L : List Bool) : Reach v (B (J++L) (bwrd (2*n+2) b)) (A (rep W n++Q++L) (rwrd 1 (out v 0 b))) := by
  have h1 := reach_of (start v L (rep Q n++mark b))
  have h2 := reach_of (f_many v n (Q++L) (mark b))
  have h3 := reach_of (f_turn v b (rep W n++(Q++L)))
  have h := join (join h1 h2) h3
  unfold bwrd
  rw [show 2*n+2=2*n+1+1 by omega,rep,rep,even_pairs n]
  change Reach v (B (J++L) (Q++(rep Q n++mark b))) (A (rep W n++Q++L) (rwrd 1 (out v 0 b)))
  simpa only [List.append_assoc] using h

theorem clear (v : V) (n : Nat) (b : Bool) (L : List Bool) : Reach v (B (J++L) (bwrd (2*n+2) b)) (A L (rwrd (2*n+3) (out v n b))) := by
  induction n using Nat.strongRecOn generalizing b L with
  | ind n ih =>
    have h0 := beginB v n b L
    cases n with
    | zero => exact join h0 (a_two v 1 (out v 0 b) L)
    | succ n =>
      let bb := if v=.a then b else true
      have h1 := reach_of (a_block v 0 (out v 0 b) (rep W n++Q++L))
      have h2 := ih 0 (by omega) (out v 0 b) (rep W n++Q++L)
      rw [out_twice] at h2
      have h2a : Reach v (B (J++(rep W n++Q++L)) (bwrd 2 (out v 0 b))) (A (rep W n++(Q++L)) (rwrd 3 bb)) := by simpa only [List.append_assoc] using h2
      have hb : v=.a ∨ bb=true := by unfold bb; by_cases h:v=.a <;> simp [h]
      have h3 := walk v (n+1) (fun j hj => ih j hj) 1 n bb (Q++L) (by omega) (by omega) hb
      have h4 := a_two v (2*(1+n)+1) bb L
      have h := join (join (join (join h0 h1) h2a) h3) h4
      have ho : out v (n+1) b = bb := by simp [out,bb]
      simpa only [ho,show 2*(1+n)+1+2=2*(n+1)+3 by omega] using h

def family (n : Nat) := B [] (bwrd (2*n+3) true)
theorem entry (v : V) : run0 (table v) 37 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl
theorem outer_start (v : V) (R : List Bool) : run0 (table v) 4 (B [] (Q++R)) = some (F (H++P) R) := by cases v <;> rfl
theorem outer_turn (v : V) (L : List Bool) : run0 (table v) 9 (F (H++L) [false,true,true,true]) = some (A (W++L) [true,false,true]) := by cases v <;> rfl
theorem outer_first (v : V) (L : List Bool) : run0 (table v) 28 (A (W++L) [true,false,true]) = some (A L (rwrd 3 true)) := by cases v <;> rfl

theorem growthReach (v : V) (n : Nat) : Reach v (family n) (family (n+1)) := by
  have h1 := reach_of (outer_start v (rep Q n++[false,true,true,true]))
  have h2 := reach_of (f_many v n P [false,true,true,true])
  have h3 := reach_of (outer_turn v (rep W n++P))
  have h4 := reach_of (outer_first v (rep W n++P))
  have h5 := walk v (n+1) (fun j _ => clear v j) 1 n true P (by omega) (by omega) (Or.inr rfl)
  have h6 := reach_of (a_pair v [] (rep P (2*(1+n)+1)++mark true))
  have h7 : run0 (table v) 3 (A [] (rwrd (2*(1+n)+1+1) true)) = some (B [] (bwrd (2*(1+n)+1+2) true)) := by cases v <;> rfl
  have h := join (join (join (join (join (join h1 h2) h3) h4) h5) h6) (reach_of h7)
  have eq : bwrd (2*n+3) true = Q++(rep Q n++[false,true,true,true]) := by
    unfold bwrd
    rw [show 2*n+3=(2*n+2)+1 by omega,rep,← rep_snoc P (2*n+2),show 2*n+2=2*(n+1) by omega,even_pairs,rep]
    simp only [List.append_assoc]
    rfl
  unfold family
  rw [eq]
  simpa only [show 2*(1+n)+1+2=2*(n+1)+3 by omega] using h
noncomputable def cost (v : V) (n : Nat) : Nat := Classical.choose (growthReach v n)
theorem growth (v : V) (n : Nat) : run0 (table v) (cost v n) (family n) = some (family (n+1)) := Classical.choose_spec (growthReach v n)
theorem rep_len (n : Nat) : (rep P n).length=2*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.length_append,ih]; change 2+2*n=2*(n+1); omega
theorem family_len (n : Nat) : (family n).r.length = 4*n+8 := by
  unfold family bwrd mark; simp only [List.length_append,rep_len]; change 2*(2*n+3)+2=4*n+8; omega
theorem positive (v : V) (n : Nat) : 0<cost v n := by
  by_cases hz : cost v n=0
  · have hg := growth v n
    rw [hz,run0] at hg
    have he := congrArg (fun z : Z0 => z.r.length) (Option.some.inj hg)
    rw [family_len,family_len] at he
    omega
  · omega
theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 37 (cost v) (entry v) (positive v) (growth v) m hm
#print axioms clear
#print axioms growthReach
#print axioms never

namespace M93
abbrev table := _root_.BB6.Agent11Raw107LAPairCounter.table .a
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent11Raw107LAPairCounter.never .a m hm
end M93

namespace M94
abbrev table := _root_.BB6.Agent11Raw107LAPairCounter.table .b
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent11Raw107LAPairCounter.never .b m hm
end M94

namespace M97
abbrev table := _root_.BB6.Agent11Raw107LAPairCounter.table .c
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent11Raw107LAPairCounter.never .c m hm
end M97

namespace M98
abbrev table := _root_.BB6.Agent11Raw107LAPairCounter.table .d
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent11Raw107LAPairCounter.never .d m hm
end M98
end BB6.Agent11Raw107LAPairCounter
