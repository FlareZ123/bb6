import Raw14086C
import Raw14042Bank
import Raw140ERExit
namespace Raw14086
open BB6BlockFAR Raw140Orbit Raw140Extra Raw14086Local Raw140Double Raw14086Arithmetic
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
attribute [local irreducible] boundary run

abbrev ATail := Raw140ERSuffix.Tail
abbrev aword := Raw140ERSuffix.tailWord
abbrev an := Raw140ERSuffix.rho
abbrev ac := Raw14042Bank.extra
abbrev AB := Raw14042Bank.B
abbrev TA := Raw14042Bank.T

def arank : ATail → Nat
  | .t542 => 0 | .t152 => 1 | .t1121 => 2 | .t5215 => 3 | .t1155 => 4 | .t11511 => 5

theorem arank_lt (s : ATail) : arank s < 6 := by cases s <;> decide
theorem arank_next (s : ATail) : arank (an s) = next (arank s) := by cases s <;> decide
theorem ac_rank (s : ATail) : ac s = Raw14086Arithmetic.carry (arank s) := by cases s <;> decide
theorem abalance (s : ATail) : 6*ac s+arank (an s)=arank s+1 := by cases s <;> decide

def aTurn (k : Nat) (s : ATail) : Nat × ATail :=
  match k with
  | 0 => (0,s)
  | k+1 => (ac s+(aTurn k (an s)).1,(aTurn k (an s)).2)

theorem aTurn_balance (k : Nat) (s : ATail) : 6*(aTurn k s).1+arank (aTurn k s).2=k+arank s := by
  induction k generalizing s with
  | zero => simp [aTurn]
  | succ k ih =>
    have h := ih (an s)
    have h' := abalance s
    change 6*(ac s+(aTurn k (an s)).1)+arank (aTurn k (an s)).2=k+1+arank s
    omega

def bw (n : Nat) : List Bool :=
  match n with
  | 0 => []
  | n+1 => false::true::true::bw n

theorem bw_sound (n : Nat) : Raw140ERSweep.oddword (bw n) = AB n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bw,Raw140ERSweep.oddword,Bool.false_eq_true,ite_false,ite_true,ih,Raw14042Bank.bank_cons]

theorem ow3 (m : Nat) : Raw140ERSweep.oddword (List.replicate m true)=U 3 m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [List.replicate_succ,Raw140ERSweep.oddword,ite_true,ih,U]

theorem carry_word (s : ATail) : Raw140ERSweep.oddword (Raw140ERSuffix.carry s)=AB (ac s) := by
  cases s <;> rfl

theorem ab_add (n m : Nat) : AB (n+m)=AB n ++ AB m := by
  induction m with
  | zero => simp [AB,Raw140VariantTransfer.bank]
  | succ m ih =>
    change AB (n+m) ++ [S 1,S 3,S 3] = AB n ++ (AB m ++ [S 1,S 3,S 3])
    simp only [ih,List.append_assoc]

theorem bankStep (n m : Nat) (X : List Sym) (s : ATail) :
    Reach base
      (boundary 4 true (S 1::(AB n ++ U 3 m ++ S 5::X)) (aword s))
      (boundary 4 true (S 1::(AB (n+ac s) ++ U 3 (m+1) ++ X)) (aword (an s))) := by
  let W := bw n ++ List.replicate m true
  have h := Raw140ERSuffix.advance W X s
  have hw : Raw140ERSweep.oddword W=AB n ++ U 3 m := by
    simp only [W,Raw140ERSuffix.oddword_append,bw_sound,ow3]
  rw [hw,carry_word] at h
  have h' : AB (ac s) ++ AB n = AB (n+ac s) := by rw [← ab_add,Nat.add_comm]
  have he : AB (ac s) ++ (AB n ++ (U 3 m ++ S 3::X)) = AB (n+ac s) ++ (U 3 (m+1) ++ X) := by
    rw [← List.append_assoc (AB (ac s)),h']
    congr 1
    exact merge 3 m 1 X
  refine ⟨22*W.length+Raw140ERSuffix.cost s,?_⟩
  simpa only [List.append_assoc,he] using h

theorem bankIter (k n m : Nat) (X : List Sym) (s : ATail) :
    Reach base (boundary 4 true (S 1::(AB n ++ U 3 m ++ U 5 k ++ X)) (aword s))
      (boundary 4 true (S 1::(AB (n+(aTurn k s).1) ++ U 3 (m+k) ++ X)) (aword (aTurn k s).2)) := by
  induction k generalizing n m s with
  | zero =>
    simpa only [aTurn,Nat.add_zero,U,List.replicate_zero,List.append_nil,List.nil_append] using Reach.refl base _
  | succ k ih =>
    have h0 := bankStep n m (U 5 k ++ X) s
    have h1 := ih (n+ac s) (m+1) (an s)
    simp only [List.append_assoc] at h0 h1
    simpa only [aTurn,U,List.replicate_succ,List.cons_append,List.append_assoc,Nat.add_assoc,
      show m+1+k=m+(k+1) by omega] using Reach.trans h0 h1

-- A generic bank exit retaining the homogeneous context, rather than using
-- the final 42-specific defect absorption.
theorem exitFront (j n : Nat) (X Y : List Sym) :
    Reach base
      (boundary 4 false (U 3 (j+1) ++ AB (n+1) ++ X) Y)
      (boundary 4 true (S 3::S 3::S 3::X) (S 1::(TA n ++ U 1 j ++ Y))) := by
  have h0 := Raw140ERSuffix.prepareCarry j (S 3::S 3::(AB n ++ X)) Y
  have h1 := Raw14042Bank.pumpAny n X (U 1 j ++ Y)
  have h := join h0 h1
  refine ⟨5+3*(j+1)+21*n,?_⟩
  simpa only [Raw14042Bank.bank_cons,U,List.replicate_succ,List.cons_append,List.append_assoc,List.nil_append] using h

theorem exitAny (n : Nat) (X : List Sym) (s : ATail) :
    Reach base
      (boundary 4 true (S 1::(AB (n+1) ++ X)) (aword s))
      (boundary 4 true (S 3::S 3::S 3::X) (S 1::(TA (n+ac s) ++ aword (an s)))) := by
  cases s with
  | t542 =>
    have h0 := Raw140ERSuffixLocal.prep542 (AB (n+1) ++ X)
    have h1 := exitFront 1 n X [S 5,S 2]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h1
    simpa only [Raw14042Bank.extra,aword,an,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,Nat.add_zero,List.append_assoc] using Reach.trans (⟨_,h0⟩ : Reach base _ _) h1
  | t152 =>
    have h0 := Raw140ERSuffixLocal.prep152 (AB (n+1) ++ X)
    have h1 := exitFront 1 n X [S 1,S 2,S 1]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h1
    simpa only [Raw14042Bank.extra,aword,an,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,Nat.add_zero,List.append_assoc] using Reach.trans (⟨_,h0⟩ : Reach base _ _) h1
  | t1121 =>
    have h0 := Raw140ERSuffixLocal.prep1121 (AB (n+1) ++ X)
    have h1 := exitFront 0 n X [S 5,S 2,S 1,S 5]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h1
    simpa only [Raw14042Bank.extra,aword,an,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,Nat.add_zero,List.append_assoc] using Reach.trans (⟨_,h0⟩ : Reach base _ _) h1
  | t5215 =>
    have h0 := Raw140ERSuffixLocal.prep5215 (AB (n+1) ++ X)
    have h1 := exitFront 0 n X [S 1,S 1,S 5,S 5]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h1
    simpa only [Raw14042Bank.extra,aword,an,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,Nat.add_zero,List.append_assoc] using Reach.trans (⟨_,h0⟩ : Reach base _ _) h1
  | t1155 =>
    have h0 := Raw140ERSuffixLocal.prep1155 (AB (n+1) ++ X)
    have h1 := exitFront 2 n X [S 5,S 1,S 1]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h1
    simpa only [Raw14042Bank.extra,aword,an,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,Nat.add_zero,List.append_assoc] using Reach.trans (⟨_,h0⟩ : Reach base _ _) h1
  | t11511 =>
    have h0 := Raw140ERSuffixLocal.prep11511 (AB (n+1) ++ X)
    have h1 := exitFront 2 n X [S 5,S 5,S 4,S 2]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h1
    simpa only [Raw14042Bank.extra,aword,an,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,Raw14042Bank.trip_snoc,List.append_assoc,List.cons_append,List.nil_append] using
      Reach.trans (⟨_,h0⟩ : Reach base _ _) h1

theorem aPumpAll (n p : Nat) (Y : List Sym) (hp : 24 ≤ p) :
    R (boundary 0 true (U 3 p ++ [S 2]) (TA n ++ Y))
      (boundary 0 true (U 3 (p+5*n) ++ [S 2]) Y) := by
  induction n generalizing p with
  | zero => exact Reach.refl M86 _
  | succ n ih =>
    have h0 : R (boundary 0 true (U 3 p ++ [S 2]) (TA (n+1) ++ Y))
        (boundary 0 true (U 3 (p+5) ++ [S 2]) (TA n ++ Y)) := by
      simpa only [TA,Raw140VariantTransfer.trip,List.cons_append,
        show p-24+24=p by omega,show p-24+29=p+5 by omega] using rr (aPump (p-24) (TA n ++ Y))
    simpa only [show p+5+5*n=p+5*(n+1) by omega] using Reach.trans h0 (ih (p+5) (by omega))

theorem terminalA (p : Nat) (s : ATail) (hp : 24 ≤ p) :
    R (boundary 0 true (U 3 p ++ [S 2]) (aword s)) (cfg (termA p (arank s))) := by
  cases s
  · simpa only [aword,Raw140ERSuffix.tailWord,arank,termA,cfg,A2,show p-24+24=p by omega,show p-24+26=p+2 by omega] using rr (a542 (p := p-24))
  · simpa only [aword,Raw140ERSuffix.tailWord,arank,termA,cfg,A0,show p-24+24=p by omega,show p-24+29=p+5 by omega] using rr (a152 (p-24))
  · simpa only [aword,Raw140ERSuffix.tailWord,arank,termA,cfg,A0,show p-24+24=p by omega,show p-24+29=p+5 by omega] using rr (a1121 (p-24))
  · simpa only [aword,Raw140ERSuffix.tailWord,arank,termA,cfg,B0,show p-24+24=p by omega,show p-24+30=p+6 by omega] using rr (a5215 (p-24))
  · simpa only [aword,Raw140ERSuffix.tailWord,arank,termA,cfg,A0,show p-24+24=p by omega,show p-24+30=p+6 by omega] using rr (a1155 (p-24))
  · simpa only [aword,Raw140ERSuffix.tailWord,arank,termA,cfg,B0,show p-24+24=p by omega,show p-24+33=p+9 by omega] using rr (a11511 (p-24))

theorem drainA (p n : Nat) (s : ATail) (hp : 24 ≤ p) :
    R (boundary 0 true (U 3 p ++ [S 2]) (TA n ++ aword s)) (cfg (termA (p+5*n) (arank s))) :=
  Reach.trans (aPumpAll n p _ hp) (terminalA _ s (by omega))

theorem onePumpAll (p j b : Nat) (Y : List Sym) (hp : 3 ≤ p) :
    R (boundary 0 true (U 3 p ++ [S 2]) (S 0::(U 1 (2*j+b) ++ Y)))
      (boundary 0 true (U 3 (p+4*j) ++ [S 2]) (S 0::(U 1 b ++ Y))) := by
  induction j generalizing p with
  | zero => simpa only [Nat.mul_zero,Nat.zero_add,Nat.add_zero] using Reach.refl M86 _
  | succ j ih =>
    have h0 : R (boundary 0 true (U 3 p ++ [S 2]) (S 0::(U 1 (2*(j+1)+b) ++ Y)))
        (boundary 0 true (U 3 (p+4) ++ [S 2]) (S 0::(U 1 (2*j+b) ++ Y))) := by
      simpa only [show p-3+3=p by omega,show p-3+7=p+4 by omega,
        show 2*(j+1)+b=(2*j+b)+1+1 by omega,
        U,List.replicate_succ,List.cons_append,List.append_assoc] using rr (oddPump (p-3) (U 1 (2*j+b) ++ Y))
    simpa only [show p+4+4*j=p+4*(j+1) by omega] using Reach.trans h0 (ih (p+4) (by omega))

theorem bFront (p : Nat) (hp : 24 ≤ p) :
    Plus (B0 p) (boundary 4 true (U 3 (p+2))
      (S 1::(TA ((aTurn (p-4) .t152).1+ac (aTurn (p-4) .t152).2-1) ++ aword (an (aTurn (p-4) .t152).2)))) := by
  let n := (aTurn (p-4) .t152).1
  let s := (aTurn (p-4) .t152).2
  have hb := aTurn_balance (p-4) .t152
  have hlt := arank_lt s
  have hb' : 6*n+arank s=p-3 := by
    simpa only [n,s,arank,show p-4+1=p-3 by omega] using hb
  have hn3 : 3 ≤ n := by omega
  have h0 : Plus (B0 p) (boundary 4 true (S 1::(U 3 3 ++ U 5 (p-4))) (aword .t152)) := by
    simpa only [B0,aword,Raw140ERSuffix.tailWord,show p-24+24=p by omega,show p-24+20=p-4 by omega,
      U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] using positive (bSeed (p := p-24)) (by omega)
  have h1 := lift (bankIter (p-4) 0 3 [] .t152)
  have h1' : R (boundary 4 true (S 1::(U 3 3 ++ U 5 (p-4))) (aword .t152))
      (boundary 4 true (S 1::(AB n ++ U 3 (p-1))) (aword s)) := by
    simpa only [n,s,AB,Raw140VariantTransfer.bank,List.nil_append,List.append_nil,Nat.zero_add,
      show 3+(p-4)=p-1 by omega] using h1
  have h2 := lift (exitAny (n-1) (U 3 (p-1)) s)
  have h2' : R (boundary 4 true (S 1::(AB n ++ U 3 (p-1))) (aword s))
      (boundary 4 true (U 3 (p+2)) (S 1::(TA (n+ac s-1) ++ aword (an s)))) := by
    simpa only [show n-1+1=n by omega,show n-1+ac s=n+ac s-1 by omega,
      show p+2=(p-1)+1+1+1 by omega,U,List.replicate_succ,List.cons_append] using h2
  exact Plus.transR (Plus.transR h0 h1') h2'

-- Both homogeneous exits retain at least 24 threes; the even exit must
-- first transform the whole surviving carry bank through the common ER rule.
theorem b0Return (p : Nat) (hp : 24 ≤ p) : Plus (B0 p) (cfg (ret .b0 p)) := by
  let n := (aTurn (p-4) .t152).1
  let s := (aTurn (p-4) .t152).2
  let z := n+ac s-1
  let t := an s
  have hbal := aTurn_balance (p-4) .t152
  have hbal' : 6*n+arank s=p-3 := by
    simpa only [n,s,arank,show p-4+1=p-3 by omega] using hbal
  have hlt := arank_lt s
  have hn : n=(p-3)/6 := by omega
  have hs : arank s=(p-3)%6 := by omega
  have hz : z≥2 := by dsimp [z]; omega
  let Y := TA z ++ aword t
  have h0 : Plus (B0 p) (boundary 4 true (U 3 (p+2)) (S 1::Y)) := by
    simpa only [n,s,z,t,Y] using bFront p hp
  have h1 : R (boundary 4 true (U 3 (p+2)) (S 1::Y))
      (boundary 4 true [S 2] (U 1 (p+2) ++ S 5::Y)) := by
    simpa only [show p+2-24+24=p+2 by omega] using rr (oddInit (p+2-24) Y)
  have h2 : R (boundary 4 true [S 2] (U 1 (p+2) ++ S 5::Y))
      (boundary 0 true (U 3 3 ++ [S 2]) (S 0::(U 1 p ++ S 5::Y))) := by
    have hpL : U 1 p = S 1::U 1 (p-1) := by
      conv => lhs; rw [show p=(p-1)+1 by omega]
      rfl
    simpa only [show p+2=(p-1)+1+1+1 by omega,hpL,
      U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using
      rr (oddStart (U 1 (p-1) ++ S 5::Y))
  have h := Plus.transR (Plus.transR h0 h1) h2
  by_cases ho : p%2=1
  · let j := (p-1)/2
    have h3 := onePumpAll 3 j 1 (S 5::Y) (by omega)
    have h3' : R (boundary 0 true (U 3 3 ++ [S 2]) (S 0::(U 1 p ++ S 5::Y)))
        (boundary 0 true (U 3 (2*p+1) ++ [S 2]) (S 0::S 1::S 5::Y)) := by
      simpa only [j,show 2*((p-1)/2)+1=p by omega,show 3+4*((p-1)/2)=2*p+1 by omega,
        U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using h3
    have h4 : R (boundary 0 true (U 3 (2*p+1) ++ [S 2]) (S 0::S 1::S 5::Y))
        (boundary 0 true (U 3 (2*p+6) ++ [S 2]) Y) := by
      simpa only [show 2*p+1-24+24=2*p+1 by omega,show 2*p+1-24+29=2*p+6 by omega] using rr (oddLow (2*p+1-24) Y)
    have h5 := drainA (2*p+6) z t (by omega)
    have h' := Plus.transR (Plus.transR (Plus.transR h h3') h4) h5
    simpa only [ret,ho,ite_true,z,t,arank_next,ac_rank,hn,hs] using h'
  · let j := p/2
    let m := 2*p+3
    have h3 := onePumpAll 3 j 0 (S 5::Y) (by omega)
    have h3' : R (boundary 0 true (U 3 3 ++ [S 2]) (S 0::(U 1 p ++ S 5::Y)))
        (boundary 0 true (U 3 m ++ [S 2]) (S 0::S 5::Y)) := by
      simpa only [j,m,show 2*(p/2)+0=p by omega,show 3+4*(p/2)=2*p+3 by omega,
        U,List.replicate_zero,List.nil_append] using h3
    have h4 : R (boundary 0 true (U 3 m ++ [S 2]) (S 0::S 5::Y))
        (boundary 4 true (S 1::(U 3 (m+1) ++ [S 2])) Y) := by
      simpa only [m,show 2*p+3-24+24=2*p+3 by omega,show 2*p+3-24+25=2*p+3+1 by omega] using rr (evenLow (p := m-24) Y)
    have h5 := rr (Raw140VariantTransfer.erMany M86 ext z (U 3 (m+1) ++ [S 2]) (aword t))
    have h6 := lift (Raw140ERExit.exitBank (z-2) (m+1) t)
    have h6' : R (boundary 4 true (S 1::(AB z ++ U 3 (m+1) ++ [S 2])) (aword t))
        (boundary 0 true (U 3 (2*p+15) ++ [S 2]) (TA (z+ac t-2) ++ aword (an t))) := by
      have hb : Raw140ERExit.trip133 (z-2+2) = AB z := by
        rw [show z-2+2=z by omega]
        induction z with
        | zero => rfl
        | succ z ih => simp only [Raw140ERExit.trip133,Raw14042Bank.bank_cons,ih]
      have ht : ∀ k, Raw140ERExit.trip115 k = TA k := by intro k; induction k with
        | zero => rfl
        | succ k ih => simp only [Raw140ERExit.trip115,TA,Raw140VariantTransfer.trip,ih]
      have heq : Raw140ERExit.extra t=ac t := by cases t <;> rfl
      simpa only [hb,ht,heq,show z-2+ac t=z+ac t-2 by omega,m,
        show 2*p+3+1+11=2*p+15 by omega,List.append_assoc] using h6
    have h7 := drainA (2*p+15) (z+ac t-2) (an t) (by omega)
    simp only [Y,List.append_assoc] at h4 h5 h6'
    have h' := Plus.transR (Plus.transR (Plus.transR (Plus.transR (Plus.transR h h3') h4) h5) h6') h7
    simpa only [ret,ho,ite_false,z,t,arank_next,ac_rank,hn,hs] using h'

#print axioms bankIter
#print axioms exitAny
#print axioms b0Return
end Raw14086
