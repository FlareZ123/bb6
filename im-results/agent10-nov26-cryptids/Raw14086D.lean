import Raw14086Local
import Raw14086Arithmetic
import Raw140DoubleCore
namespace Raw14086
open BB6BlockFAR Raw140Orbit Raw140Extra Raw14086Local Raw140Double Raw14086Arithmetic
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

def A0 (p : Nat) : Prim := boundary 0 true (U 3 p ++ [S 2]) []
def A2 (p : Nat) : Prim := boundary 0 true (U 3 p ++ [S 2]) [S 2]
def B0 (p : Nat) : Prim := boundary 1 true (U 5 p) []
def cfg (c : Cfg) : Prim := match c with
  | (.a0,p) => A0 p | (.a2,p) => A2 p | (.b0,p) => B0 p
abbrev R := Reach M86
theorem ext : Extends M86 := fill_extends _ _
theorem rr {k : Nat} {a b : Prim} (h : run M86 k a = some b) : R a b := ⟨k,h⟩
theorem rb {k : Nat} {a b : Prim} (h : run base k a = some b) : R a b := Reach.ext ext ⟨k,h⟩
theorem lift {a b : Prim} (h : Reach base a b) : R a b := Reach.ext ext h
abbrev TB (n : Nat) := word (trips n)

theorem tb_succ (n : Nat) : TB (n+1) = S 6::S 4::S 4::TB n := rfl

theorem bPumpAll (n p : Nat) (Y : List Sym) (hp : 24 ≤ p) :
    R (boundary 1 true (U 5 p) (TB n ++ Y)) (boundary 1 true (U 5 (p+5*n)) Y) := by
  induction n generalizing p with
  | zero => simpa [TB,trips,word] using Reach.refl M86 (boundary 1 true (U 5 p) Y)
  | succ n ih =>
    have h0 := rr (bPump (p-24) (TB n ++ Y))
    have h1 : R (boundary 1 true (U 5 p) (TB (n+1) ++ Y))
        (boundary 1 true (U 5 (p+5)) (TB n ++ Y)) := by
      simpa only [tb_succ,List.cons_append, show p-24+24=p by omega,
        show p-24+29=p+5 by omega] using h0
    have h2 := ih (p+5) (by omega)
    simpa only [show p+5+5*n=p+5*(n+1) by omega] using Reach.trans h1 h2

theorem terminalB (p : Nat) (s : Raw140Double.Tail) (hp : 24 ≤ p) :
    R (boundary 1 true (U 5 p) (Raw140Double.tailWord s))
      (cfg (termB p (Raw140Double.rank s))) := by
  cases s
  · simpa only [Raw140Double.tailWord,Raw140Double.rank,termB,cfg,B0,
      show p-24+24=p by omega,show p-24+26=p+2 by omega] using rr (b62 (p := p-24))
  · simpa only [Raw140Double.tailWord,Raw140Double.rank,termB,cfg,A2,
      show p-24+24=p by omega,show p-24+26=p+2 by omega] using rr (b64 (p-24))
  · simpa only [Raw140Double.tailWord,Raw140Double.rank,termB,cfg,A0,
      show p-24+24=p by omega,show p-24+27=p+3 by omega] using rr (b6221 (p-24))
  · simpa only [Raw140Double.tailWord,Raw140Double.rank,termB,cfg,B0,
      show p-24+24=p by omega,show p-24+30=p+6 by omega] using rr (b6421 (p-24))
  · simpa only [Raw140Double.tailWord,Raw140Double.rank,termB,cfg,B0,
      show p-24+24=p by omega,show p-24+30=p+6 by omega] using rr (b6405 (p-24))
  · simpa only [Raw140Double.tailWord,Raw140Double.rank,termB,cfg,A2,
      show p-24+24=p by omega,show p-24+28=p+4 by omega] using rr (b62542 (p-24))

theorem drainB (p n : Nat) (s : Raw140Double.Tail) (hp : 24 ≤ p) :
    R (boundary 1 true (U 5 p) (TB n ++ Raw140Double.tailWord s))
      (cfg (termB (p+5*n) (Raw140Double.rank s))) :=
  Reach.trans (bPumpAll n p _ hp) (terminalB _ s (by omega))

theorem rank_rho (s : Raw140Double.Tail) : Raw140Double.rank (Raw140Double.rho s) = next (Raw140Double.rank s) := by cases s <;> decide
theorem carry_rank (s : Raw140Double.Tail) : Raw140Double.carry s = Raw14086Arithmetic.carry (Raw140Double.rank s) := by cases s <;> decide

def D (k : Nat) : Prim := boundary 3 false (U 6 k ++ [S 4]) (U 4 8 ++ [S 6,S 2])

theorem dFront (k : Nat) : R (D k)
    (E 1 (k+7) (TB (turn k .s62).1 ++ Raw140Double.tailWord (turn k .s62).2)) := by
  have h0 := lift (dIter k [S 4] (List.replicate 8 false) .s62)
  have h1 : R (D k) (boundary 3 false [S 4]
    (U 4 (k+8) ++ TB (turn k .s62).1 ++ Raw140Double.tailWord (turn k .s62).2)) := by
    simpa only [D,word_append,word_four,List.append_assoc,merge,Raw140Double.tailWord] using h0
  have h2 := lift (dEndE (k+7) (TB (turn k .s62).1 ++ Raw140Double.tailWord (turn k .s62).2))
  have h3 : R (boundary 3 false [S 4]
    (U 4 (k+8) ++ TB (turn k .s62).1 ++ Raw140Double.tailWord (turn k .s62).2))
      (E 1 (k+7) (TB (turn k .s62).1 ++ Raw140Double.tailWord (turn k .s62).2)) := by
    simpa only [List.append_assoc,show k+7+1=k+8 by omega] using h2
  exact Reach.trans h1 h3

theorem dEvenPhase (h n : Nat) (s : Raw140Double.Tail) (hh : 28 ≤ h) (ho : h%2=1) :
    R (E 1 (h-1) (TB n ++ Raw140Double.tailWord s))
      (cfg (termB (2*h+2+5*n) (Raw140Double.rank s))) := by
  let j := (h-1)/2
  have hj : 2*j=h-1 := by dsimp [j]; omega
  have hm : 1+4*j+3=2*h+2 := by omega
  have h0 := lift (eEven j 1 (TB n ++ Raw140Double.tailWord s))
  rw [hj,hm] at h0
  exact Reach.trans h0 (drainB _ n s (by omega))

theorem dOddPhase (h n : Nat) (s : Raw140Double.Tail) (hh : 28 ≤ h) (he : h%2=0) (hn : 3 ≤ n) :
    R (E 1 (h-1) (TB n ++ Raw140Double.tailWord s))
      (cfg (termB (2*h+11+5*(n+Raw140Double.carry s-2)) (Raw140Double.rank (Raw140Double.rho s)))) := by
  let j := (h-2)/2
  have hj : 2*j+1=h-1 := by dsimp [j]; omega
  have hm : 1+4*j=2*h-3 := by omega
  have h0 := lift (eIter j 1 1 (TB n ++ Raw140Double.tailWord s))
  rw [hj,hm] at h0
  have h1 := lift (eOddLast (2*h-3) (false::trips (n-1)) s)
  have h1' : R (E (2*h-3) 1 (TB n ++ Raw140Double.tailWord s))
      (boundary 3 false [] (U 4 (2*h+4) ++ TB (n-1+Raw140Double.carry s) ++ Raw140Double.tailWord (Raw140Double.rho s))) := by
    have hN : TB n = S 6::S 4::S 4::TB (n-1) := by
      conv => lhs; rw [show n=(n-1)+1 by omega]
      exact tb_succ _
    rw [hN, show 2*h+4=(2*h-3+6)+1 by omega]
    simpa only [word, Bool.false_eq_true,ite_false,List.cons_append,List.append_assoc,
      ← word_append,← trips_add,rep_cons,U,List.replicate_succ] using h1
  let z := n+Raw140Double.carry s-2
  have hz : n-1+Raw140Double.carry s=z+1 := by dsimp [z]; omega
  rw [hz,tb_succ] at h1'
  have h2 := rb (convert2 (2*h+4) (S 4::S 4::(TB z ++ Raw140Double.tailWord (Raw140Double.rho s))))
  have h3 := rr (bFour (2*h+7-24) (TB z ++ Raw140Double.tailWord (Raw140Double.rho s)))
  have h3' : R (boundary 1 true (U 5 (2*h+7)) (S 4::S 4::(TB z ++ Raw140Double.tailWord (Raw140Double.rho s))))
      (boundary 1 true (U 5 (2*h+11)) (TB z ++ Raw140Double.tailWord (Raw140Double.rho s))) := by
    simpa only [show 2*h+7-24+24=2*h+7 by omega,show 2*h+7-24+28=2*h+11 by omega] using h3
  simp only [List.cons_append,List.append_assoc,show 2*h+4+3=2*h+7 by omega] at h1' h2 h3'
  have h := Reach.trans (Reach.trans h0 h1') (Reach.trans h2 h3')
  exact Reach.trans h (drainB _ z _ (by omega))

theorem dReturn_sound (k : Nat) (hk : 20 ≤ k) : R (D k) (cfg (dReturn k)) := by
  let t := (turn k .s62).2
  let n := (turn k .s62).1
  have hbal := turn_balance k .s62
  have hlt := rank_lt t
  have hbal' : 6*n+Raw140Double.rank t=k := by simpa only [n,t,Raw140Double.rank,Nat.add_zero] using hbal
  have hn : n=k/6 := by omega
  have hs : Raw140Double.rank t=k%6 := by omega
  have hn3 : 3 ≤ n := by omega
  have h0 := dFront k
  change R (D k) (E 1 (k+7) (TB n ++ Raw140Double.tailWord t)) at h0
  by_cases hpar : (k+8)%2=1
  · have h1 := dEvenPhase (k+8) n t (by omega) hpar
    rw [show k+8-1=k+7 by omega] at h1
    have h := Reach.trans h0 h1
    simpa only [dReturn,hpar,ite_true,hn,hs] using h
  · have h1 := dOddPhase (k+8) n t (by omega) (by omega) hn3
    rw [show k+8-1=k+7 by omega] at h1
    have h := Reach.trans h0 h1
    simpa only [dReturn,hpar,ite_false,rank_rho,carry_rank,hn,hs] using h

def Plus (a b : Prim) : Prop := ∃ k, 0 < k ∧ run M86 k a = some b

theorem positive {k : Nat} {a b : Prim} (h : run M86 k a = some b) (hk : 0 < k) : Plus a b := ⟨k,hk,h⟩

theorem Plus.transR {a b c : Prim} (h : Plus a b) (g : R b c) : Plus a c := by
  obtain ⟨m,hm,h⟩ := h
  obtain ⟨n,g⟩ := g
  exact ⟨m+n,by omega,join h g⟩

theorem a2Return (p : Nat) (hp : 24 ≤ p) : Plus (A2 p) (cfg (ret .a2 p)) := by
  have h0 := positive (aSeed (p-24)) (by omega)
  have h1 : Plus (A2 p) (D (p-4)) := by
    simpa only [A2,D,show p-24+24=p by omega,show p-24+20=p-4 by omega,
        U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] using h0
  exact Plus.transR h1 (dReturn_sound (p-4) (by omega))

#print axioms dReturn_sound
#print axioms a2Return
end Raw14086
