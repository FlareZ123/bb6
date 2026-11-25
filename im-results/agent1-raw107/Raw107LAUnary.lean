import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw107LAUnary
open BB6Coverage BB6Coverage.Agent31Pump
inductive V | a | b | c deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some (match v with
      | .a => ⟨false,true,2⟩
      | .b => ⟨false,true,5⟩
      | .c => ⟨true,false,4⟩))
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none
abbrev P : List Bool := [false,true]
abbrev Q : List Bool := [false,true,false,true]
abbrev W : List Bool := [false,false,false,true]
abbrev H : List Bool := [true,false,true]
abbrev J : List Bool := [false,false,true]
abbrev K : List Bool := [true,true]
abbrev Z : List Bool := [false,false]
abbrev X : List Bool := [true,false]
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev B (L R : List Bool) : Z0 := ⟨1,L,R⟩
abbrev C (L R : List Bool) : Z0 := ⟨2,L,R⟩
abbrev D (L R : List Bool) : Z0 := ⟨3,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
def rwrd (k b : Nat) := [true]++rep P k++rep K b
def bwrd (k b : Nat) := rep P k++rep K b

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

def cCost (v : V) : Nat := match v with | .a => 2 | .b => 2 | .c => 6
theorem c_one (v : V) (L R : List Bool) : run0 (table v) (cCost v) (C (X++L) ([true]++K++R)) = some (C (X++Z++L) ([true]++R)) := by cases v <;> rfl
theorem c_many (v : V) (n : Nat) (L R : List Bool) : run0 (table v) (cCost v*n) (C (X++L) ([true]++rep K n++R)) = some (C (X++rep Z n++L) ([true]++R)) :=
  sweepR (table v) 2 X [true] K Z (cCost v) (c_one v) n L R

theorem c_end (v : V) (L : List Bool) : run0 (table v) (cCost v+1) (C (X++L) [true]) = some (D ([false,false,false,false,false]++L) []) := by cases v <;> rfl
theorem d_one (v : V) (L R : List Bool) : run0 (table v) 2 (D (Z++L) R) = some (D L (K++R)) := by cases v <;> rfl
theorem d_many (v : V) (n : Nat) (L R : List Bool) : run0 (table v) (2*n) (D (rep Z n++L) R) = some (D L (rep K n++R)) := by
  simpa only [List.nil_append] using sweepL (table v) 3 [] [] Z K 2 (d_one v) n L R

theorem d_end (v : V) (L R : List Bool) : run0 (table v) 7 (D ([true]++L) (K++K++R)) = some (A L ([true,false,true,true,true]++R)) := by cases v <;> rfl

theorem f_turn (v : V) (b : Nat) (L : List Bool) : Reach v (F (H++L) (rep K b)) (A L (rwrd 1 (b+1))) := by
  cases b with
  | zero => exact reach_of (show run0 (table v) 13 (F (H++L) []) = some (A L (rwrd 1 1)) by cases v <;> rfl)
  | succ n =>
    have h1 : run0 (table v) 1 (F (H++L) (K++rep K n)) = some (C (X++P++L) ([true]++rep K n)) := by cases v <;> rfl
    have h2 := c_many v n (P++L) []
    have h3 := c_end v (rep Z n++P++L)
    have hz : [false,false,false,false,false]++(rep Z n++P++L) = rep Z (n+3)++[true]++L := by
      have shift : ∀ k, rep Z k ++ [false] = [false] ++ rep Z k := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => simp only [rep,List.append_assoc,ih]; rfl
      rw [show n+3=n+1+1+1 by omega]
      simp only [rep,List.append_assoc]
      rw [show P=[false]++[true] by rfl,List.append_assoc,← List.append_assoc (rep Z n) [false] ([true]++L),shift n]
      rfl
    have h12 : Reach v (F (H++L) (rep K (n+1))) (C (X++rep Z n++P++L) [true]) := by
      apply join (reach_of h1)
      exact reach_of (by simpa only [List.append_assoc,List.append_nil] using h2)
    have h123 := join h12 (reach_of h3)
    rw [hz] at h123
    have h4 := d_many v (n+3) ([true]++L) []
    have h4' : Reach v (D (rep Z (n+3)++[true]++L) []) (D ([true]++L) (rep K (n+3))) := reach_of (by simpa only [List.append_assoc,List.append_nil] using h4)
    have h5 := d_end v L (rep K (n+1))
    have h5' : Reach v (D ([true]++L) (rep K (n+3))) (A L (rwrd 1 (n+2))) := by
      apply reach_of (t := 7)
      simp only [rwrd,rep,List.append_assoc,List.nil_append]
      exact h5
    exact join (join h123 h4') h5'

theorem a_pair (v : V) (L R : List Bool) : run0 (table v) 4 (A (P++L) (true::R)) = some (A L (true::(P++R))) := by cases v <;> rfl
theorem a_two (v : V) (k b : Nat) (L : List Bool) : Reach v (A (Q++L) (rwrd k b)) (A L (rwrd (k+2) b)) := by
  have h1 := a_pair v (P++L) (rep P k++rep K b)
  have h2 := a_pair v L (P++(rep P k++rep K b))
  exact reach_of (join0 h1 h2)

theorem a_block (v : V) (j b : Nat) (L : List Bool) : run0 (table v) 3 (A (W++L) (rwrd (2*j+1) b)) = some (B (J++L) (bwrd (2*j+2) b)) := by
  unfold rwrd bwrd
  rw [show 2*j+2=(2*j+1)+1 by omega]
  cases v <;> rfl

theorem pow_pos (j : Nat) : 0 < 2^j := Nat.pow_pos (by decide)

theorem walk (v : V) (N : Nat)
    (small : ∀ j, j<N → ∀ b L, Reach v (B (J++L) (bwrd (2*j+2) b)) (A L (rwrd (2*j+3) (b+2^j))))
    (j k b : Nat) (L : List Bool) (hk : j+k≤N) :
    Reach v (A (rep W k++L) (rwrd (2*j+1) (b+(2^j-1))))
      (A L (rwrd (2*(j+k)+1) (b+(2^(j+k)-1)))) := by
  induction k generalizing j with
  | zero => simpa only [rep,List.nil_append,Nat.add_zero] using reach_zero v (A L (rwrd (2*j+1) (b+(2^j-1))))
  | succ k ih =>
    have h1 := reach_of (a_block v j (b+(2^j-1)) (rep W k++L))
    have h2 := small j (by omega) (b+(2^j-1)) (rep W k++L)
    have hp := pow_pos j
    rw [show b+(2^j-1)+2^j=b+(2^(j+1)-1) by rw [Nat.pow_succ]; omega,show 2*j+3=2*(j+1)+1 by omega] at h2
    have h3 := ih (j+1) (by omega)
    have h := join (join h1 h2) h3
    simpa only [rep,List.append_assoc,show j+1+k=j+(k+1) by omega] using h

theorem beginB (v : V) (n b : Nat) (L : List Bool) : Reach v (B (J++L) (bwrd (2*n+2) b)) (A (rep W n++Q++L) (rwrd 1 (b+1))) := by
  have h1 := reach_of (start v L (rep Q n++rep K b))
  have h2 := reach_of (f_many v n (Q++L) (rep K b))
  have h3 := f_turn v b (rep W n++(Q++L))
  have h := join (join h1 h2) h3
  unfold bwrd
  rw [show 2*n+2=2*n+1+1 by omega,rep,rep,even_pairs n]
  change Reach v (B (J++L) (Q++(rep Q n++rep K b))) (A (rep W n++Q++L) (rwrd 1 (b+1)))
  simpa only [List.append_assoc] using h

theorem clear (v : V) (n b : Nat) (L : List Bool) : Reach v (B (J++L) (bwrd (2*n+2) b)) (A L (rwrd (2*n+3) (b+2^n))) := by
  induction n using Nat.strongRecOn generalizing b L with
  | ind n ih =>
    have h0 := beginB v n b L
    have h1 := walk v n (fun j hj => ih j hj) 0 n (b+1) (Q++L) (by omega)
    simp only [Nat.zero_add,Nat.mul_zero,Nat.pow_zero,Nat.sub_self,Nat.add_zero] at h1
    have hp := pow_pos n
    rw [show b+1+(2^n-1)=b+2^n by omega] at h1
    have h1' : Reach v (A (rep W n++Q++L) (rwrd 1 (b+1))) (A (Q++L) (rwrd (2*n+1) (b+2^n))) := by simpa only [List.append_assoc] using h1
    have h2 := a_two v (2*n+1) (b+2^n) L
    exact join (join h0 h1') h2

theorem outer_start (v : V) (R : List Bool) : run0 (table v) 4 (B [] (Q++R)) = some (F (H++P) R) := by cases v <;> rfl
theorem outer_turn (v : V) (L R : List Bool) : run0 (table v) 9 (F (H++L) (P++K++R)) = some (A (W++L) ([true]++P++R)) := by cases v <;> rfl

theorem outer (v : V) (n b : Nat) : Reach v (B [] (bwrd (2*n+3) (b+1))) (B [] (bwrd (2*(n+1)+3) (b+(2^(n+1)-1)))) := by
  have h1 := reach_of (outer_start v (rep Q n++(P++rep K (b+1))))
  have h2 := reach_of (f_many v n P (P++rep K (b+1)))
  have h3 := reach_of (outer_turn v (rep W n++P) (rep K b))
  have h12 : Reach v (B [] (Q++rep Q n++P++rep K (b+1))) (F (H++rep W n++P) (P++K++rep K b)) := by
    simpa only [List.append_assoc,rep] using join h1 h2
  have h123 := join h12 h3
  have h4 := walk v (n+1) (fun j _ => clear v j) 0 (n+1) b P (by omega)
  simp only [Nat.zero_add,Nat.mul_zero,Nat.pow_zero,Nat.sub_self,Nat.add_zero] at h4
  have h4' : Reach v (A (W++(rep W n++P)) (rwrd 1 b)) (A P (rwrd (2*(n+1)+1) (b+(2^(n+1)-1)))) := by simpa only [rep,List.append_assoc] using h4
  have h5 := reach_of (a_pair v [] (rep P (2*(n+1)+1)++rep K (b+(2^(n+1)-1))))
  have h6 : run0 (table v) 3 (A [] (rwrd (2*(n+1)+1+1) (b+(2^(n+1)-1)))) = some (B [] (bwrd (2*(n+1)+1+2) (b+(2^(n+1)-1)))) := by cases v <;> rfl
  have h := join (join (join h123 h4') h5) (reach_of h6)
  have eq : bwrd (2*n+3) (b+1) = Q++rep Q n++P++rep K (b+1) := by
    unfold bwrd
    rw [show 2*n+3=(2*n+2)+1 by omega,rep,← rep_snoc P (2*n+2),show 2*n+2=2*(n+1) by omega,even_pairs,rep]
  rw [eq]
  exact h

def tailK : Nat → Nat
  | 0 => 0
  | n+1 => tailK n+(2^(n+1)-2)
def family (n : Nat) := B [] (bwrd (2*n+3) (tailK n+1))
theorem entry (v : V) : run0 (table v) 37 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl
theorem growthReach (v : V) (n : Nat) : Reach v (family n) (family (n+1)) := by
  have h := outer v n (tailK n)
  have hp := pow_pos n
  have hq : 2≤2^(n+1) := by rw [Nat.pow_succ]; omega
  simpa only [family,tailK,show tailK n+(2^(n+1)-2)+1=tailK n+(2^(n+1)-1) by omega] using h
noncomputable def cost (v : V) (n : Nat) : Nat := Classical.choose (growthReach v n)
theorem growth (v : V) (n : Nat) : run0 (table v) (cost v n) (family n) = some (family (n+1)) := Classical.choose_spec (growthReach v n)
theorem rep_len (p : List Bool) (n : Nat) : (rep p n).length=p.length*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.length_append,ih,Nat.mul_succ]; omega
theorem family_len (n : Nat) : (family n).r.length = 4*n+6+2*(tailK n+1) := by
  unfold family bwrd; simp only [List.length_append,rep_len]; change 2*(2*n+3)+2*(tailK n+1)=4*n+6+2*(tailK n+1); omega
theorem positive (v : V) (n : Nat) : 0<cost v n := by
  by_cases hz : cost v n=0
  · have hg := growth v n
    rw [hz,run0] at hg
    have he := congrArg (fun z : Z0 => z.r.length) (Option.some.inj hg)
    rw [family_len,family_len,tailK] at he
    omega
  · omega
theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 37 (cost v) (entry v) (positive v) (growth v) m hm
#print axioms f_turn
#print axioms clear
#print axioms outer
#print axioms growthReach
#print axioms positive
#print axioms never

namespace M95
abbrev table := _root_.BB6.Agent1Raw107LAUnary.table .a
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw107LAUnary.never .a m hm
end M95
namespace M96
abbrev table := _root_.BB6.Agent1Raw107LAUnary.table .b
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw107LAUnary.never .b m hm
end M96
namespace M99
abbrev table := _root_.BB6.Agent1Raw107LAUnary.table .c
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw107LAUnary.never .c m hm
end M99
end BB6.Agent1Raw107LAUnary
