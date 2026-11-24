import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Recursive.R79M748
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB---_1RC1LE_0RD0RF_1LD1RE_1LF0LB_1LA0LA
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
abbrev O (n : Nat) := List.replicate n true
abbrev P (n : Nat) := rep [false,true] n
def B (L R : List Bool) : Z0 := ⟨1,L,R⟩
def Reaches (a b : Z0) : Prop := ∃ t, run0 table t a = some b
theorem trans {a b c : Z0} : Reaches a b → Reaches b c → Reaches a c := by
  rintro ⟨t,h⟩ ⟨u,g⟩
  exact ⟨t+u,join0 h g⟩
theorem p_add (a b : Nat) : P (a+b) = P a ++ P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega];simp [rep,ih,List.append_assoc]
theorem bRight (L R : List Bool) : run0 table 10 (B (false::L) (P 2++R)) = some (B (false::(O 4++L)) R) := by rfl
theorem bLeft (L R : List Bool) : run0 table 2 (B (O 2++L) R) = some (B L (P 1++R)) := by rfl
theorem sweepRight (k m : Nat) (R : List Bool) : Reaches (B (false::O m) (P (2*k)++R)) (B (false::O (4*k+m)) R) := by
  induction k generalizing m with
  | zero => exact ⟨0,by simp [run0,rep]⟩
  | succ k ih =>
    have h1 := bRight (O m) (P (2*k)++R)
    have h2 := ih (4+m)
    rw [show 4*k+(4+m)=4*(k+1)+m by omega] at h2
    have h3 : run0 table 10 (B (false::O m) (P (2*(k+1))++R)) = some (B (false::O (4+m)) (P (2*k)++R)) := by
      rw [show 2*(k+1)=2+2*k by omega,p_add,List.append_assoc]
      simpa only [List.replicate_append_replicate] using h1
    exact trans ⟨10,h3⟩ h2
theorem sweepLeft (k m n : Nat) : Reaches (B (O (2*k+m)) (P n)) (B (O m) (P (k+n))) := by
  induction k generalizing n with
  | zero => exact ⟨0,by simp [run0]⟩
  | succ k ih =>
    have h1 := bLeft (O (2*k+m)) (P n)
    have h2 := ih (1+n)
    rw [show k+(1+n)=k+1+n by omega] at h2
    have h3 : run0 table 2 (B (O (2*(k+1)+m)) (P n)) = some (B (O (2*k+m)) (P (1+n))) := by
      rw [show 2*(k+1)+m=2+(2*k+m) by omega]
      rw [p_add]
      simpa only [List.replicate_append_replicate] using h1
    exact trans ⟨2,h3⟩ h2
theorem firstEven (k : Nat) : Reaches (B [] (P (2*(k+1)))) (B [true] (P (2*(k+1)+1))) := by
  have h1 : run0 table 10 (B [] (P (2*(k+1)))) = some (B (false::O 4) (P (2*k))) := by
    rw [show 2*(k+1)=2+2*k by omega,p_add]
    rfl
  have h2 := sweepRight k 4 []
  simp only [List.append_nil] at h2
  have h3 : run0 table 6 (B (false::O (4*k+4)) []) = some (B (O (4*k+5)) (P 1)) := by rfl
  have h4 := sweepLeft (2*k+2) 1 1
  rw [show 2*(2*k+2)+1=4*k+5 by omega,show 2*k+2+1=2*(k+1)+1 by omega] at h4
  exact trans ⟨10,h1⟩ (trans h2 (trans ⟨6,h3⟩ h4))
theorem firstOdd (k : Nat) : Reaches (B [] (P (2*k+1))) (B [true] (P (2*k+2))) := by
  cases k with
  | zero => exact ⟨14,rfl⟩
  | succ k =>
    have h1 : run0 table 10 (B [] (P (2*(k+1)+1))) = some (B (false::O 4) (P (2*k+1))) := by
      rw [show 2*(k+1)+1=2+(2*k+1) by omega,p_add];rfl
    have h2 := sweepRight k 4 (P 1)
    rw [← p_add] at h2
    have h3 : run0 table 10 (B (false::O (4*k+4)) (P 1)) = some (B (O (4*k+9)) []) := by rfl
    have h4 := sweepLeft (2*k+4) 1 0
    rw [show 2*(2*k+4)+1=4*k+9 by omega,show 2*k+4+0=2*(k+1)+2 by omega] at h4
    exact trans ⟨10,h1⟩ (trans h2 (trans ⟨10,h3⟩ h4))
theorem first (n : Nat) (hn : 0<n) : Reaches (B [] (P n)) (B [true] (P (n+1))) := by
  by_cases h : n%2=0
  · obtain ⟨k,hk⟩ : ∃ k, n=2*(k+1) := ⟨n/2-1,by omega⟩
    rw [hk]; exact firstEven k
  · obtain ⟨k,hk⟩ : ∃ k,n=2*k+1 := ⟨n/2,by omega⟩
    rw [hk]; exact firstOdd k
theorem mid (n : Nat) : run0 table 18 (B [true] (P (n+1))) = some (B (false::O 3) (P (n+2))) := by rfl
theorem secondEven (k : Nat) : Reaches (B (false::O 3) (P (2*k))) (B [] (P (2*k+3))) := by
  have h1 := sweepRight k 3 []
  simp only [List.append_nil] at h1
  have h2 : run0 table 6 (B (false::O (4*k+3)) []) = some (B (O (4*k+4)) (P 1)) := by rfl
  have h3 := sweepLeft (2*k+2) 0 1
  rw [show 2*(2*k+2)+0=4*k+4 by omega,show 2*k+2+1=2*k+3 by omega] at h3
  exact trans h1 (trans ⟨6,h2⟩ h3)
theorem secondOdd (k : Nat) : Reaches (B (false::O 3) (P (2*k+1))) (B [] (P (2*k+4))) := by
  have h1 := sweepRight k 3 (P 1)
  rw [← p_add] at h1
  have h2 : run0 table 10 (B (false::O (4*k+3)) (P 1)) = some (B (O (4*k+8)) []) := by rfl
  have h3 := sweepLeft (2*k+4) 0 0
  rw [show 2*(2*k+4)+0=4*k+8 by omega,show 2*k+4+0=2*k+4 by omega] at h3
  exact trans h1 (trans ⟨10,h2⟩ h3)
theorem second (n : Nat) : Reaches (B (false::O 3) (P n)) (B [] (P (n+3))) := by
  by_cases h : n%2=0
  · obtain ⟨k,hk⟩ : ∃ k,n=2*k := ⟨n/2,by omega⟩
    rw [hk]; exact secondEven k
  · obtain ⟨k,hk⟩ : ∃ k,n=2*k+1 := ⟨n/2,by omega⟩
    rw [hk,show 2*k+1+3=2*k+4 by omega]; exact secondOdd k
theorem epoch (n : Nat) (hn : 0<n) : ∃ t, 0<t ∧ run0 table t (B [] (P n)) = some (B [] (P (n+5))) := by
  obtain ⟨u,h1⟩ := first n hn
  have h2 := mid n
  obtain ⟨v,h3⟩ := second (n+2)
  rw [show n+2+3=n+5 by omega] at h3
  exact ⟨u+18+v,by omega,join0 (join0 h1 h2) h3⟩
def family (n : Nat) : Z0 := B [] (P (2+5*n))
theorem entry : run0 table 9 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem family_step (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  have h := epoch (2+5*n) (by omega)
  rw [show 2+5*n+5=2+5*(n+1) by omega] at h
  exact h
noncomputable def cost (n : Nat) : Nat := (family_step n).choose
theorem cost_pos (n : Nat) : 0 < cost n := (family_step n).choose_spec.1
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := (family_step n).choose_spec.2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 9 cost entry cost_pos growth m hm
#print axioms never
end BB6.Agent10Recursive.R79M748

namespace BB6.Agent10Recursive.R79M740
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB---_1RC1LE_0RD0RC_1LD1RE_1LF0LB_1LB0LA
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
abbrev O (n : Nat) := List.replicate n true
abbrev Z (n : Nat) := List.replicate n false
abbrev Q (n : Nat) := rep [true,false,false] n
def R (a b : Nat) : List Bool := O a++[false,true,false]++O b
def B (L : List Bool) (a b : Nat) : Z0 := ⟨1,L,R a b⟩
def C (L R : List Bool) : Z0 := ⟨2,L,R⟩
def D (L R : List Bool) : Z0 := ⟨3,L,R⟩
def Reaches (a b : Z0) : Prop := ∃ t, run0 table t a = some b
theorem trans {a b c : Z0} : Reaches a b → Reaches b c → Reaches a c := by
  rintro ⟨t,h⟩ ⟨u,g⟩
  exact ⟨t+u,join0 h g⟩
theorem rep_single (b : Bool) (n : Nat) : rep [b] n = List.replicate n b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,ih,List.singleton_append,List.replicate_succ]
theorem cOne (L R : List Bool) : run0 table 1 (C (true::L) (true::R)) = some (C (true::false::L) R) := by rfl
theorem dZero (L R : List Bool) : run0 table 1 (D (false::L) R) = some (D L (true::R)) := by rfl
theorem first (a b : Nat) (L : List Bool) : Reaches (B (false::L) a b) (C (false::(Z a++true::L)) (true::false::O b)) := by
  cases a with
  | zero => exact ⟨1,rfl⟩
  | succ a =>
    have h1 : run0 table 1 (B (false::L) (a+1) b) = some (C (true::true::L) (R a b)) := by rfl
    have h2 := sweepR table 2 [true] [] [true] [false] 1 cOne a (true::L) ([false,true,false]++O b)
    change run0 table (1*a) (C (true::true::L) (rep [true] a++([false,true,false]++O b))) = some (C (true::(rep [false] a++true::L)) (false::true::false::O b)) at h2
    simp only [rep_single,Nat.one_mul] at h2
    have h3 : run0 table 1 (C (true::(Z a++true::L)) (false::true::false::O b)) = some (C (false::(Z (a+1)++true::L)) (true::false::O b)) := by rfl
    simp only [R,List.append_assoc] at h1
    exact ⟨1+a+1,join0 (join0 h1 h2) h3⟩
theorem unary (b : Nat) (X : List Bool) : Reaches (⟨1,false::true::X,O (b+1)⟩ : Z0) (B X 0 (b+2)) := by
  have h1 : run0 table 1 ⟨1,false::true::X,O (b+1)⟩ = some (C (true::true::true::X) (O b)) := by rfl
  have h2 := sweepR table 2 [true] [] [true] [false] 1 cOne b (true::true::X) []
  change run0 table (1*b) (C (true::true::true::X) (rep [true] b++[])) = some (C (true::(rep [false] b++true::true::X)) []) at h2
  simp only [rep_single,Nat.one_mul,List.append_nil] at h2
  have h3 : run0 table 2 (C (true::(Z b++true::true::X)) []) = some (D (Z (b+3)++true::true::X) []) := by rfl
  have h4 := sweepL table 3 [] [] [false] [true] 1 dZero (b+3) (true::true::X) []
  change run0 table (1*(b+3)) (D (rep [false] (b+3)++true::true::X) []) = some (D (true::true::X) (rep [true] (b+3)++[])) at h4
  simp only [rep_single,Nat.one_mul,List.append_nil] at h4
  have h5 : run0 table 4 (D (true::true::X) (O (b+3))) = some (B X 0 (b+2)) := by rfl
  exact ⟨_,join0 (join0 (join0 (join0 h1 h2) h3) h4) h5⟩
theorem flip (a b : Nat) (L : List Bool) : Reaches (B (false::L) a b) (B (Z a++true::L) 0 (b+2)) := by
  have h1 := first a b L
  have h2 : run0 table 5 (C (false::(Z a++true::L)) (true::false::O b)) = some (⟨1,false::true::(Z a++true::L),O (b+1)⟩ : Z0) := by rfl
  exact trans h1 (trans ⟨5,h2⟩ (unary b (Z a++true::L)))
theorem carryOne (a b : Nat) (L : List Bool) : run0 table 3 (B ([true,false,false]++L) a b) = some (B L (a+3) b) := by rfl
theorem carry (k a b : Nat) (L : List Bool) : Reaches (B (Q k++L) a b) (B L (a+3*k) b) := by
  induction k generalizing a with
  | zero => exact ⟨0,by simp [rep,run0]⟩
  | succ k ih =>
    have h1 := carryOne a b (Q k++L)
    have h2 := ih (a+3)
    rw [show a+3+3*k=a+3*(k+1) by omega] at h2
    exact trans ⟨3,h1⟩ h2
def gain : Nat → Nat
  | 0 => 0
  | k+1 => 2*gain k+2
theorem count (k b : Nat) (L : List Bool) : Reaches (B (Z (3*k)++L) 0 b) (B (Q k++L) 0 (b+gain k)) := by
  induction k generalizing b L with
  | zero => exact ⟨0,rfl⟩
  | succ k ih =>
    have h1 := ih b ([false,false,false]++L)
    have h2 := carry k 0 (b+gain k) ([false,false,false]++L)
    simp only [Nat.zero_add] at h2
    have h3 := flip (3*k) (b+gain k) (false::false::L)
    have h4 := ih (b+gain k+2) ([true,false,false]++L)
    rw [show b+gain k+2+gain k=b+gain (k+1) by rw [gain];omega] at h4
    have he1 : Z (3*(k+1))++L = Z (3*k)++([false,false,false]++L) := by
      rw [show 3*(k+1)=3*k+3 by omega]
      change Z (3*k+3)++L = Z (3*k)++(Z 3++L)
      rw [← List.append_assoc,List.replicate_append_replicate]
    have he2 : Q k++([true,false,false]++L) = Q (k+1)++L := by
      rw [← List.append_assoc,rep_snoc];rfl
    rw [he1,← he2]
    exact trans h1 (trans h2 (trans h3 h4))
theorem enter (a b : Nat) : Reaches (B [] a b) (B (Z a++[true]) 0 (b+2)) := by
  obtain ⟨t,h⟩ := flip a b []
  cases t with
  | zero =>
    simp [run0,B] at h
    have hh := congrArg List.length h.1
    cases a <;> simp at hh <;> simp [List.replicate_succ] at h
  | succ t =>
    exact ⟨t+1,h⟩
theorem finish (a b : Nat) : run0 table 3 (B [true] a b) = some (B [] (a+3) b) := by rfl
theorem epoch (k b : Nat) : ∃ t, 0<t ∧ run0 table t (B [] (3*k) b) = some (B [] (3*(k+1)) (b+2+gain k)) := by
  obtain ⟨t,h1⟩ := enter (3*k) b
  have h2 := count k (b+2) [true]
  have h3 := carry k 0 (b+2+gain k) [true]
  simp only [Nat.zero_add] at h3
  have h4 := finish (3*k) (b+2+gain k)
  rw [show 3*k+3=3*(k+1) by omega] at h4
  obtain ⟨u,h⟩ := trans ⟨t,h1⟩ (trans h2 h3)
  exact ⟨u+3,by omega,join0 h h4⟩
def family (n : Nat) : Z0 := B [] (3*(n+1)) (gain (n+1)+1)
theorem gain_closed (k : Nat) : gain k+2 = 2^(k+1) := by
  induction k with
  | zero => decide
  | succ k ih => rw [gain,Nat.pow_succ];omega
theorem entry : run0 table 30 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem family_step (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  have h := epoch (n+1) (gain (n+1)+1)
  rw [show gain (n+1)+1+2+gain (n+1)=gain (n+1+1)+1 by have hh : gain (n+1+1) = 2*gain (n+1)+2 := rfl;omega] at h
  exact h
noncomputable def cost (n : Nat) : Nat := (family_step n).choose
theorem cost_pos (n : Nat) : 0 < cost n := (family_step n).choose_spec.1
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := (family_step n).choose_spec.2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 30 cost entry cost_pos growth m hm
#print axioms never
end BB6.Agent10Recursive.R79M740
