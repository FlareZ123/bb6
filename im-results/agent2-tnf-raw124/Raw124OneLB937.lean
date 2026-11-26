import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw124OneLB937
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  ([some (some ⟨true,true,1⟩), none,
    some (some ⟨true,true,2⟩), some (some ⟨false,false,5⟩),
    some (some ⟨false,true,3⟩), some (some ⟨false,true,0⟩),
    some (some ⟨true,false,3⟩), some (some ⟨true,true,4⟩),
    some (some ⟨true,true,3⟩), some (some ⟨true,false,5⟩),
    some (some ⟨true,true,4⟩), some (some ⟨true,false,1⟩)] : List (Option Transition))[2*s.1.val+s.2.toNat]?.getD none

private def O : List Bool := [true,true]
private def P : List Bool := [true,false]
private def Q : List Bool := [true,false,true,true]
private def S : List Bool := [false,true,false,true]
private def T : List Bool := [false,true]
private def U : List Bool := [true,true,true]
private def B (l r : List Bool) : Z0 := ⟨1,l,r⟩
private def C (l r : List Bool) : Z0 := ⟨2,l,r⟩
private def D (l r : List Bool) : Z0 := ⟨3,l,r⟩

private theorem prepOne (L R : List Bool) :
    run0 table 8 (C (O++L) (S++R)) = some (C (O++Q++L) R) := by rfl
private theorem prep (k : Nat) :
    run0 table (8*k) (C O (rep S k++[false,true,true,true])) =
    some (C (O++rep Q k) [false,true,true,true]) := by
  simpa only [C,List.nil_append,List.append_nil] using
    sweepR table 2 O [] S Q 8 prepOne k [] [false,true,true,true]
private theorem turn (L : List Bool) :
    run0 table 30 (C (O++L) [false,true,true,true]) =
    some (B (rep O 3++L) U) := by rfl
private theorem popOne (L R : List Bool) :
    run0 table 2 (B (O++L) R) = some (B L (P++R)) := by rfl
private theorem pop (n : Nat) (L R : List Bool) :
    run0 table (2*n) (B (rep O n++L) R) = some (B L (rep P n++R)) := by
  simpa only [B,List.nil_append] using sweepL table 1 [] [] O P 2 popOne n L R
private theorem rightOne (L R : List Bool) :
    run0 table 2 (D (U++L) (T++R)) = some (D (U++O++L) R) := by rfl
private theorem right (n : Nat) (L R : List Bool) :
    run0 table (2*n) (D (U++L) (rep T n++R)) = some (D (U++rep O n++L) R) := by
  simpa only [D,List.nil_append] using sweepR table 3 U [] T O 2 rightOne n L R
private theorem rep_add (W : List Bool) (n m : Nat) : rep W (n+m) = rep W n ++ rep W m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m=n+m+1 by omega, rep, ih, rep, List.append_assoc]
private theorem rotate (n : Nat) : rep P n ++ U = true :: (rep T n ++ O) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.append_assoc,ih]; rfl
private theorem middle (n : Nat) (L : List Bool) :
    run0 table (4*n+6) (B (rep O n++Q++L) U) = some (B (rep O (n+2)++L) U) := by
  have h1 := pop n (Q++L) U
  rw [rotate] at h1
  have h2 : run0 table 3 (B (Q++L) (true::(rep T n++O))) =
      some (D (U++O++L) (rep T n++O)) := by rfl
  have h3 := right n (O++L) O
  have h4 : run0 table 3 (D (U++rep O n++(O++L)) O) =
      some (B (rep O (n+2)++L) U) := by
    have he : rep O (n+2) = O ++ rep O n ++ O := by
      rw [show n+2=n+1+1 by omega,rep_add (m:=1)]; rfl
    rw [he]; simp only [List.append_assoc]; rfl
  have h := join0 (join0 (join0 h1 h2) h3) h4
  rw [show 2*n+3+2*n+3=4*n+6 by omega] at h
  simpa only [List.append_assoc] using h
private theorem middleMany (n k : Nat) :
    run0 table (k*(4*n+6)+4*k*(k-1)) (B (rep O n++rep Q k) U) =
    some (B (rep O (n+2*k)) U) := by
  induction k generalizing n with
  | zero => simp [rep,run0]
  | succ k ih =>
    have h1 := middle n (rep Q k)
    have h2 := ih (n+2)
    have h := join0 h1 h2
    rw [show n+2+2*k=n+2*(k+1) by omega] at h
    have he : 4*n+6+(k*(4*(n+2)+6)+4*k*(k-1)) = (k+1)*(4*n+6)+4*(k+1)*k := by
      cases k with
      | zero => simp
      | succ k => simp only [Nat.succ_sub_one]; simp [Nat.add_mul,Nat.mul_add]; omega
    rw [he] at h
    simpa only [rep,List.append_assoc,Nat.add_sub_cancel] using h

def family (k : Nat) : Z0 := B [] (rep P (2*k+1)++U)
def cost (k : Nat) : Nat := 4*k*k+26*k+37
private theorem start (k : Nat) : run0 table 1 (family k) = some (C O (rep S k++[false,true,true,true])) := by
  have h : ∀ k, rep P (2*k+1)++U = true::(rep S k++[false,true,true,true]) := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [show 2*(k+1)+1=2*k+1+2 by omega, Nat.add_comm (2*k+1) 2, rep_add]; change (rep P 2 ++ rep P (2*k+1)) ++ U = _; rw [List.append_assoc,ih]; rfl
  unfold family; rw [h]; rfl

theorem root : run0 table 16 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  have h1 := join0 (join0 (start k) (prep k)) (turn (rep Q k))
  have h2 := middleMany 3 k
  have h3 := pop (3+2*k) [] U
  simp only [List.append_nil] at h3
  have h := join0 (join0 h1 h2) h3
  have ht : 1+8*k+30+(k*(4*3+6)+4*k*(k-1))+2*(3+2*k)=cost k := by
    unfold cost; cases k with
    | zero => decide
    | succ k => simp only [Nat.succ_sub_one]; simp [Nat.add_mul,Nat.mul_add]; omega
  rw [ht] at h
  unfold family
  rw [show 2*(k+1)+1=3+2*k by omega]
  change run0 table (cost k) (family k) = _
  exact h

theorem never_source (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 16 cost root (by intro k; unfold cost; omega) growth m hm
#print axioms root
#print axioms growth
#print axioms never_source
end BB6.Agent2Raw124OneLB937
