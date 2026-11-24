import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Recursive.R67M438
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB---_1RC1LB_0RD0RC_1LD1RE_0LF0LB_0LA0LE
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none
abbrev O (n : Nat) := List.replicate n true
abbrev Z (n : Nat) := List.replicate n false
def R (n : Nat) : List Bool := O (n+2)++[false,true,false]
def B (L : List Bool) (n : Nat) : Z0 := ⟨1,L,R n⟩
def Reaches (a b : Z0) : Prop := ∃ t, run0 table t a = some b
theorem trans {a b c : Z0} : Reaches a b → Reaches b c → Reaches a c := by
  rintro ⟨t,h⟩ ⟨u,g⟩
  exact ⟨t+u,join0 h g⟩
theorem rep_single (b : Bool) (n : Nat) : rep [b] n = List.replicate n b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,ih,List.singleton_append,List.replicate_succ]
theorem Cstep (L R : List Bool) : run0 table 1 ⟨2,[true]++L,[true]++R⟩ = some ⟨2,[true]++[false]++L,R⟩ := by rfl
theorem start (n : Nat) (L : List Bool) : run0 table (1+(n+1)+16) (B (false::L) n) = some (B (Z n++true::L) 0) := by
  have h1 : run0 table 1 (B (false::L) n) = some ⟨2,true::true::L,O (n+1)++[false,true,false]⟩ := by rfl
  have h2 := sweepR table 2 [true] [] [true] [false] 1 Cstep (n+1) (true::L) [false,true,false]
  simp only [List.nil_append,rep_single,Nat.one_mul] at h2
  have h3 : run0 table 16 ⟨2,true::(Z (n+1)++true::L),[false,true,false]⟩ = some (B (Z n++true::L) 0) := by rfl
  exact join0 (join0 h1 h2) h3
theorem zeros (k j : Nat) (L : List Bool)
    (prev : ∀ i, i < j+k → ∀ X, Reaches (B (false::X) i) (B X (i+1))) :
    Reaches (B (Z k++L) j) (B L (j+k)) := by
  induction k generalizing j with
  | zero => exact ⟨0,rfl⟩
  | succ k ih =>
    have h1 := prev j (by omega) (Z k++L)
    have h2 := ih (j+1) (fun i hi => prev i (by omega))
    rw [show j+1+k=j+(k+1) by omega] at h2
    exact trans h1 h2
theorem allB (n : Nat) (L : List Bool) : Reaches (B (false::L) n) (B L (n+1)) := by
  induction n using Nat.strongRecOn generalizing L with
  | ind n ih =>
    have h1 : Reaches (B (false::L) n) (B (Z n++true::L) 0) := ⟨_,start n L⟩
    have h2 := zeros n 0 (true::L) (fun i hi X => ih i (by omega) X)
    simp only [Nat.zero_add] at h2
    have h3 : Reaches (B (true::L) n) (B L (n+1)) := ⟨1,rfl⟩
    exact trans h1 (trans h2 h3)
def family (n : Nat) : Z0 := B [] (n+1)
theorem entry : run0 table 28 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth_exists (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  obtain ⟨t,h⟩ := allB (n+1) []
  cases t with
  | zero => simp [run0,B] at h
  | succ t =>
    refine ⟨t+1,by omega,?_⟩
    exact h
noncomputable def cost (n : Nat) : Nat := (growth_exists n).choose
theorem cost_pos (n : Nat) : 0 < cost n := (growth_exists n).choose_spec.1
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := (growth_exists n).choose_spec.2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 28 cost entry cost_pos growth m hm
#print axioms never
end BB6.Agent10Recursive.R67M438

namespace BB6.Agent10Recursive.R67M1088
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB---_1RC1LB_0RD1LE_1LD1RE_0RF0LB_---0RC
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none
abbrev O (n : Nat) := List.replicate n true
abbrev Z (n : Nat) := List.replicate n false
abbrev P (n : Nat) := rep [true,false] n
abbrev Q (n : Nat) := rep [false,false,false,true] n
def R (n m : Nat) : List Bool := P n ++ O m
def B (L R : List Bool) : Z0 := ⟨1,L,R⟩
def C (L R : List Bool) : Z0 := ⟨2,L,R⟩
def Reaches (a b : Z0) : Prop := ∃ t, run0 table t a = some b
theorem trans {a b c : Z0} : Reaches a b → Reaches b c → Reaches a c := by
  rintro ⟨t,h⟩ ⟨u,g⟩
  exact ⟨t+u,join0 h g⟩
theorem rep_single (b : Bool) (n : Nat) : rep [b] n = List.replicate n b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,ih,List.singleton_append,List.replicate_succ]
theorem cquad (L R : List Bool) : run0 table 4 (C (false::L) ([true,false,true,false]++R)) = some (C (Q 1++false::L) R) := by rfl
theorem cquads (n : Nat) (L R : List Bool) : Reaches (C (false::L) (P (2*n)++R)) (C (Q n++false::L) R) := by
  induction n generalizing L with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    have h1 := cquad L (P (2*n)++R)
    obtain ⟨t,h2⟩ := ih ([false,false,true]++false::L)
    have h := join0 h1 h2
    refine ⟨4+t,?_⟩
    change run0 table (4+t) (C (false::L) (P (2*n+2)++R)) = some (C (Q (n+1)++false::L) R)
    have he : Q n ++ [false,false,false,true] = Q (n+1) := rep_snoc _ n
    change run0 table (4+t) (C (false::L) (P (2*n+2)++R)) = some (C (Q n++([false,false,false,true]++false::L)) R) at h
    rw [← List.append_assoc,he] at h
    exact h
theorem cOne (L R : List Bool) : run0 table 3 ⟨2,[true,false]++L,[true]++R⟩ = some ⟨2,[true,false]++[false]++L,R⟩ := by rfl
theorem dZero (L R : List Bool) : run0 table 1 ⟨3,[false]++L,R⟩ = some ⟨3,L,[true]++R⟩ := by rfl
theorem clearTail (m : Nat) (L : List Bool) : Reaches (C ([true,false,false,true]++false::L) (O m)) (B (false::L) (R 1 (m+4))) := by
  have h1 := sweepR table 2 [true,false] [] [true] [false] 3 cOne m (false::true::false::L) []
  simp only [rep_single,List.nil_append,List.append_nil] at h1
  have h2 : run0 table 3 ⟨2,[true,false]++Z m++false::true::false::L,[]⟩ = some (C (Z (m+4)++true::false::L) []) := by
    have he : Z m++false::true::false::L = Z (m+1)++true::false::L := by
      change Z m++(Z 1++true::false::L)=_
      rw [← List.append_assoc,List.replicate_append_replicate]
    change run0 table 3 ⟨2,true::false::(Z m++false::true::false::L),[]⟩ = _
    rw [he]
    rfl
  have h3 : run0 table 2 (C (Z (m+4)++true::false::L) []) = some ⟨3,Z (m+4)++true::false::L,[true]⟩ := by rfl
  have h4 := sweepL table 3 [] [] [false] [true] 1 dZero (m+4) (true::false::L) [true]
  simp only [rep_single,List.nil_append,Nat.one_mul] at h4
  have h5 : run0 table 3 ⟨3,true::false::L,O (m+4)++[true]⟩ = some (B (false::L) (R 1 (m+4))) := by
    have he : O (m+4)++[true] = O (m+5) := by
      change O (m+4)++O 1 = O (m+5)
      rw [List.replicate_append_replicate]
    rw [he]
    rfl
  exact ⟨_,join0 (join0 (join0 (join0 h1 h2) h3) h4) h5⟩
theorem cOdd (k m : Nat) (L : List Bool) : Reaches (C (false::L) (R (2*k+1) (m+2))) (B (Q k++false::L) (R 1 (m+4))) := by
  have h1 := cquads k L (P 1++O (m+2))
  have he : P (2*k)++P 1 = P (2*k+1) := by
    exact rep_snoc [true,false] (2*k)
  simp only [← List.append_assoc,he] at h1
  have h2 : run0 table 4 (C (Q k++false::L) (P 1++O (m+2))) = some (C ([true,false,false,true]++Q k++false::L) (O m)) := by
    cases k <;> rfl
  have h3 : Reaches (C ([true,false,false,true]++Q k++false::L) (O m)) (B (Q k++false::L) (R 1 (m+4))) := by
    cases k with
    | zero => exact clearTail m L
    | succ k => exact clearTail m ([false,false,true]++Q k++false::L)
  exact trans h1 (trans ⟨4,h2⟩ h3)
theorem bPair (k m : Nat) (L : List Bool) : Reaches (B ([false,true]++L) (R (k+1) m)) (B L (R (k+2) m)) := ⟨4,rfl⟩
def G : Nat → Nat
  | 0 => 2
  | n+1 => 2*G n
def gain (j : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => G j + gain (j+1) k
theorem gain_sum (j k : Nat) : gain j k + G j = G (j+k) := by
  induction k generalizing j with
  | zero => simp [gain]
  | succ k ih =>
    have h := ih (j+1)
    rw [G] at h
    rw [gain,show j+(k+1)=j+1+k by omega,← h]
    omega
theorem process (k j m : Nat) (L : List Bool)
    (prev : ∀ i, i < j+k → ∀ u X, Reaches (B (Q 1++X) (R (2*i+1) (u+2))) (B X (R (2*i+3) (u+2+G i)))) :
    Reaches (B (Q k++L) (R (2*j+1) (m+2))) (B L (R (2*(j+k)+1) (m+2+gain j k))) := by
  induction k generalizing j m with
  | zero => exact ⟨0,rfl⟩
  | succ k ih =>
    have h1 := prev j (by omega) m (Q k++L)
    have h2 := ih (j+1) (m+G j) (fun i hi => prev i (by omega))
    rw [show 2*(j+1)+1=2*j+3 by omega,show m+G j+2=m+2+G j by omega,
      show 2*(j+1+k)+1=2*(j+(k+1))+1 by omega,
      show m+2+G j+gain (j+1) k=m+2+gain j (k+1) by simp only [gain];omega] at h2
    exact trans h1 h2
theorem blockMacro (k m : Nat) (L : List Bool) : Reaches (B (Q 1++L) (R (2*k+1) (m+2))) (B L (R (2*k+3) (m+2+G k))) := by
  induction k using Nat.strongRecOn generalizing m L with
  | ind k ih =>
    have h1 : run0 table 4 (B (Q 1++L) (R (2*k+1) (m+2))) = some (C ([false,true,false,true]++L) (R (2*k+1) (m+2))) := by rfl
    have h2 := cOdd k m ([true,false,true]++L)
    have h3 := process k 0 (m+2) ([false,true,false,true]++L) (fun i hi u X => ih i (by omega) u X)
    simp only [Nat.mul_zero,Nat.zero_add] at h3
    have h4 := bPair (2*k) (m+2+2+gain 0 k) ([false,true]++L)
    have h5 := bPair (2*k+1) (m+2+2+gain 0 k) L
    have H := trans ⟨4,h1⟩ (trans h2 (trans h3 (trans h4 h5)))
    have hg := gain_sum 0 k
    simp only [G,Nat.zero_add] at hg
    rw [show m+2+2+gain 0 k=m+2+G k by omega] at H
    exact H
theorem g_ge_two (k : Nat) : 2 ≤ G k := by
  induction k with
  | zero => decide
  | succ k ih => rw [G]; omega
def nextMass (n m : Nat) := m + (G (n+1)-4)
theorem epoch (n m : Nat) : ∃ t, 0<t ∧ run0 table t (B [] (R (2*(n+1)) (m+4))) = some (B [] (R (2*(n+2)) (nextMass n m+4))) := by
  have h1 : run0 table 4 (B [] (R (2*(n+1)) (m+4))) = some (C [false,true] (R (2*(n+1)) (m+4))) := by rfl
  have h2 := cquads (n+1) [true] (O (m+4))
  have h3 : run0 table 4 (C (Q (n+1)++[false,true]) (O (m+4))) = some (B (Q (n+1)++[false,true]) (R 1 (m+2))) := by rfl
  have h4 := process (n+1) 0 m [false,true] (fun i _ u X => blockMacro i u X)
  simp only [Nat.mul_zero,Nat.zero_add] at h4
  have h5 := bPair (2*(n+1)) (m+2+gain 0 (n+1)) []
  have h := trans h2 (trans ⟨4,h3⟩ (trans h4 h5))
  have hg : gain 0 (n+1)+2 = G (n+1) := by
    simpa only [show G 0 = 2 by rfl,Nat.zero_add] using gain_sum 0 (n+1)
  have hge := g_ge_two n
  have he : 4 ≤ G (n+1) := by rw [G]; omega
  have heq : m+2+gain 0 (n+1)=nextMass n m+4 := by
    unfold nextMass
    omega
  rw [show 2*(n+1)+2 = 2*(n+2) by omega,heq] at h
  obtain ⟨t,ht⟩ := h
  exact ⟨4+t,by omega,join0 h1 ht⟩
def mass : Nat → Nat
  | 0 => 0
  | n+1 => nextMass n (mass n)
def family (n : Nat) : Z0 := B [] (R (2*(n+1)) (mass n+4))
theorem entry : run0 table 41 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem family_step (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := epoch n (mass n)
noncomputable def cost (n : Nat) : Nat := (family_step n).choose
theorem cost_pos (n : Nat) : 0 < cost n := (family_step n).choose_spec.1
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := (family_step n).choose_spec.2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 41 cost entry cost_pos growth m hm
#print axioms never
end BB6.Agent10Recursive.R67M1088
