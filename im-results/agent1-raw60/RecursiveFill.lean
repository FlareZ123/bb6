import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1RecursiveFill
open BB6Coverage BB6Coverage.Agent31Pump
abbrev U (n : Nat) := List.replicate n true
abbrev Z (n : Nat) := List.replicate n false
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev Q (q : Fin 6) (L R : List Bool) : Z0 := ⟨q,L,R⟩

theorem merge (a b : Nat) (x : Bool) (L : List Bool) :
    List.replicate a x ++ (List.replicate b x ++ L) = List.replicate (a+b) x ++ L := by
  rw [← List.append_assoc,List.replicate_append_replicate]

theorem manyL (p : PartialMachine) (q : Fin 6) (s : Nat) (x y : Bool)
    (h : ∀ L R, run0 p s (Q q (List.replicate s x++L) R) = some (Q q L (List.replicate s y++R)))
    (n : Nat) (L R : List Bool) :
    run0 p (s*n) (Q q (List.replicate (s*n) x++L) R) = some (Q q L (List.replicate (s*n) y++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have H := join0 (h (List.replicate (s*n) x++L) R) (ih (List.replicate s y++R))
    rw [merge,merge,show s+s*n=s*(n+1) by simp [Nat.mul_succ,Nat.add_comm],show s*n+s=s*(n+1) by simp [Nat.mul_succ]] at H
    exact H

theorem manyR (p : PartialMachine) (q : Fin 6) (s : Nat) (c x y : Bool)
    (h : ∀ L R, run0 p s (Q q (c::L) (List.replicate s x++R)) = some (Q q (c::(List.replicate s y++L)) R))
    (n : Nat) (L R : List Bool) :
    run0 p (s*n) (Q q (c::L) (List.replicate (s*n) x++R)) = some (Q q (c::(List.replicate (s*n) y++L)) R) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have H := join0 (h L (List.replicate (s*n) x++R)) (ih (List.replicate s y++L))
    rw [merge,merge,show s+s*n=s*(n+1) by simp [Nat.mul_succ,Nat.add_comm],show s*n+s=s*(n+1) by simp [Nat.mul_succ]] at H
    exact H

def K (s r n : Nat) := s*n+r

def T (s r base turn : Nat) : Nat → Nat
  | 0 => base
  | n+1 => 2*T s r base turn n + K s r n+1+turn

theorem clearA (p : PartialMachine) (q : Fin 6) (s r : Nat)
    (entry : ∀ L R, run0 p (r+1) (A (U (r+1)++L) R) = some (Q q L (U r++false::R)))
    (loop : ∀ L R, run0 p s (Q q (U s++L) R) = some (Q q L (U s++R)))
    (n : Nat) (L R : List Bool) :
    run0 p (K s r n+1) (A (U (K s r n+1)++L) R) = some (Q q L (U (K s r n)++false::R)) := by
  have H := join0 (entry (U (s*n)++L) R) (manyL p q s true true loop n L (U r++false::R))
  rw [merge,merge] at H
  unfold K
  rw [show r+1+s*n=s*n+r+1 by omega] at H
  exact H

theorem fill (p : PartialMachine) (q : Fin 6) (s r base turn : Nat) (hs : 0 < s)
    (hbase : ∀ b L R, run0 p base (Q q (false::L) (U r++b::R)) = some (A (b::(U r++false::L)) R))
    (hclear : ∀ n L R, run0 p (K s r n+1) (A (U (K s r n+1)++L) R) = some (Q q L (U (K s r n)++false::R)))
    (hturn : ∀ b L R, run0 p turn (A (false::L) (U (s-1)++b::R)) = some (A (b::(U s++L)) R))
    (n : Nat) (b : Bool) (L R : List Bool) :
    run0 p (T s r base turn n) (Q q (false::L) (U (K s r n)++b::R)) = some (A (b::(U (K s r n)++false::L)) R) := by
  induction n generalizing b L R with
  | zero => simpa [K,T] using hbase b L R
  | succ n ih =>
    have h1 := ih true L (U (s-1)++b::R)
    have h2 := hclear n (false::L) (U (s-1)++b::R)
    have h3 := ih false L (U (s-1)++b::R)
    have h4 := hturn b (U (K s r n)++false::L) R
    have he : true::(U (K s r n)++false::L) = U (K s r n+1)++false::L := by rfl
    rw [he] at h1
    have H := join0 (join0 (join0 h1 h2) h3) h4
    have ha : true::(U (s-1)++b::R) = U s++b::R := by
      have h : s-1+1=s := by omega
      rw [← h]
      rfl
    rw [ha,merge,merge] at H
    have hk : K s r (n+1)=K s r n+s := by unfold K; rw [Nat.mul_succ]; omega
    rw [show s+K s r n=K s r n+s by omega,← hk] at H
    rw [show T s r base turn n+(K s r n+1)+T s r base turn n+turn=T s r base turn (n+1) by simp only [T]; omega] at H
    exact H

theorem fillBlank (p : PartialMachine) (q : Fin 6) (s r base turn : Nat) (hs : 0 < s)
    (hbase : ∀ b L R, run0 p base (Q q (false::L) (U r++b::R)) = some (A (b::(U r++false::L)) R))
    (hbaseBlank : ∀ L, run0 p base (Q q (false::L) (U r)) = some (A (false::(U r++false::L)) []))
    (hclear : ∀ n L R, run0 p (K s r n+1) (A (U (K s r n+1)++L) R) = some (Q q L (U (K s r n)++false::R)))
    (hturn : ∀ b L R, run0 p turn (A (false::L) (U (s-1)++b::R)) = some (A (b::(U s++L)) R))
    (hturnBlank : ∀ L, run0 p turn (A (false::L) (U (s-1))) = some (A (false::(U s++L)) []))
    (n : Nat) (L : List Bool) :
    run0 p (T s r base turn n) (Q q (false::L) (U (K s r n))) = some (A (false::(U (K s r n)++false::L)) []) := by
  cases n with
  | zero => simpa [K,T] using hbaseBlank L
  | succ n =>
    have h1 := fill p q s r base turn hs hbase hclear hturn n true L (U (s-1))
    have h2 := hclear n (false::L) (U (s-1))
    have h3 := fill p q s r base turn hs hbase hclear hturn n false L (U (s-1))
    have h4 := hturnBlank (U (K s r n)++false::L)
    have he : true::(U (K s r n)++false::L) = U (K s r n+1)++false::L := by rfl
    rw [he] at h1
    have H := join0 (join0 (join0 h1 h2) h3) h4
    have ha : true::U (s-1) = U s := by
      have h : s-1+1=s := by omega
      rw [← h]
      rfl
    rw [ha,List.replicate_append_replicate,merge] at H
    have hk : K s r (n+1)=K s r n+s := by unfold K; rw [Nat.mul_succ]; omega
    rw [show s+K s r n=K s r n+s by omega,← hk] at H
    rw [show T s r base turn n+(K s r n+1)+T s r base turn n+turn=T s r base turn (n+1) by simp only [T]; omega] at H
    exact H

#print axioms fill
#print axioms fillBlank
end BB6.Agent1RecursiveFill
