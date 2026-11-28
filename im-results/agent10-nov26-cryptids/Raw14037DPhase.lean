import Raw14037Terminal
namespace Raw14037DPhase
open BB6BlockFAR Raw140Orbit Raw140Extra
open Raw140Double (Reach)
open Raw14042Counter Raw14042CounterLocal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] boundary run

theorem forward4_2 (X Y : List Sym) :
    run base 19 (boundary 2 true (S 4::X) (S 4::S 2::Y)) = some (boundary 2 true (S 4::S 5::X) (S 2::Y)) := by
  have h0 := stepR base 2 3 false (S 4) (S 6) 3 (S 4::X) (S 2::Y) (by rfl)
  have h1 := stepL base 3 4 true (S 4) (S 1) 7 (X) (S 6::S 2::Y) (by rfl)
  have h2 := stepR base 4 1 false (S 6) (S 6) 1 (S 1::X) (S 2::Y) (by rfl)
  have h3 := stepL base 1 2 true (S 1) (S 5) 1 (X) (S 6::S 2::Y) (by rfl)
  have h4 := stepR base 2 4 true (S 6) (S 0) 5 (S 5::X) (S 2::Y) (by rfl)
  have h5 := stepR base 4 1 false (S 2) (S 2) 1 (S 0::S 5::X) (Y) (by rfl)
  have h6 := stepL base 1 2 true (S 0) (S 4) 1 (S 5::X) (S 2::Y) (by rfl)
  exact join (join (join (join (join (join (h0) h1) h2) h3) h4) h5) h6

theorem enterC (X Y : List Sym) :
    run base 9 (boundary 2 true (S 4::X) (S 2::S 3::Y)) = some (boundary 4 true (S 2::S 4::X) (S 3::Y)) := by
  have h0 := stepR base 2 3 true (S 2) (S 6) 7 (S 4::X) (S 3::Y) (by rfl)
  have h1 := stepR base 3 4 false (S 3) (S 3) 1 (S 6::S 4::X) (Y) (by rfl)
  have h2 := stepL base 4 4 true (S 6) (S 2) 1 (S 4::X) (S 3::Y) (by rfl)
  exact join (join (h0) h1) h2

theorem dropTwo (X Y : List Sym) :
    run base 20 (boundary 2 true (S 4::X) (S 2::S 2::Y)) = some (boundary 3 false (S 5::S 5::X) (S 2::Y)) := by
  have h0 := stepR base 2 3 true (S 2) (S 6) 7 (S 4::X) (S 2::Y) (by rfl)
  have h1 := stepR base 3 1 false (S 2) (S 3) 1 (S 6::S 4::X) (Y) (by rfl)
  have h2 := stepL base 1 1 false (S 6) (S 2) 3 (S 4::X) (S 3::Y) (by rfl)
  have h3 := stepL base 1 1 true (S 4) (S 5) 5 (X) (S 2::S 3::Y) (by rfl)
  have h4 := stepR base 1 1 true (S 2) (S 5) 3 (S 5::X) (S 3::Y) (by rfl)
  have h5 := stepR base 1 3 false (S 3) (S 2) 1 (S 5::S 5::X) (Y) (by rfl)
  exact join (join (join (join (join (h0) h1) h2) h3) h4) h5

theorem scanFour (a : Nat) (X Y : List Sym) :
    Reach base (boundary 2 true (S 4::X) (U 4 a ++ S 2::Y))
      (boundary 2 true (S 4::(U 5 a ++ X)) (S 2::Y)) := by
  induction a generalizing X with
  | zero => exact Reach.refl base _
  | succ a ih =>
    cases a with
    | zero => exact ⟨_,forward4_2 X Y⟩
    | succ a =>
      have h0 := Raw140Double.forward4_4 X (U 4 a ++ S 2::Y)
      have h1 := ih (S 5::X)
      simpa only [U,List.replicate_succ,List.cons_append,rep_cons] using Reach.trans ⟨_,h0⟩ h1

theorem front (a : Nat) (X Y : List Sym) :
    Reach base (boundary 3 false (S 6::X) (U 4 (a+1) ++ S 2::Y))
      (boundary 2 true (S 4::(U 5 (a+1) ++ X)) (S 2::Y)) := by
  have h0 := Raw140Double.lift_4 X (U 4 a ++ S 2::Y)
  exact Reach.trans ⟨_,h0⟩ (scanFour (a+1) X Y)

def H (a n : Nat) (s : CTail) (X : List Sym) : Prim :=
  boundary 3 false X (U 4 a ++ S 2::(T n ++ cword s))

theorem drop (a : Nat) (X Y : List Sym) :
    Reach base (boundary 3 false (S 6::X) (U 4 (a+1) ++ S 2::S 2::Y))
      (boundary 3 false X (U 4 (a+3) ++ S 2::Y)) := by
  have h0 := front a X (S 2::Y)
  have h1 := dropTwo (U 5 (a+1) ++ X) Y
  have h2 := sweepL base 3 (S 5) (S 4) 3 (a+3) X (S 2::Y) (by rfl)
  exact Reach.trans (Reach.trans h0 ⟨_,h1⟩) ⟨_,h2⟩

theorem bigFront (a n : Nat) (s : CTail) (X : List Sym) :
    Reach base (H (a+1) (n+1) s (S 6::X))
      (boundary 1 true (U 5 (a+6) ++ X) (T (n+ccarry s) ++ cword (next s))) := by
  let Z := S 4::(U 5 (a+1) ++ X)
  let R := T n ++ cword s
  have h0 := front a X (T (n+1) ++ cword s)
  have h1 := enterC (U 5 (a+1) ++ X) (S 2::S 2::R)
  have h2 := scanTwo 2 Z R
  have h3 := scanTrip n (U 6 2 ++ Z) (cword s)
  have h4 := prep s (B n ++ U 6 2 ++ Z)
  have h5 := backAll n 2 Z s
  have h6 := stepL base 1 1 true (S 4) (S 5) 5 (U 5 (a+1) ++ X) (U 2 4 ++ T (n+ccarry s) ++ cword (next s)) (by rfl)
  have h7 := sweepR base 1 (S 2) (S 5) 3 4 (U 5 (a+2) ++ X) (T (n+ccarry s) ++ cword (next s)) (by rfl)
  simp only [H,Z,R,T,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append,rep_cons] at h0 h1 h2 h3 h4 h5 h6 h7
  exact Reach.trans (Reach.trans (Reach.trans (Reach.trans (Reach.trans (Reach.trans (Reach.trans h0 ⟨_,h1⟩) h2) h3) h4) h5) ⟨_,h6⟩) ⟨_,h7⟩

theorem large (a n : Nat) (s : CTail) (X : List Sym) :
    Reach base (H (a+1) (n+2) s (S 6::X))
      (boundary 3 false X (U 4 (a+6) ++ S 2::S 2::S 2::(T (n+ccarry s) ++ cword (next s)))) := by
  have h0 := bigFront a (n+1) s X
  rw [show n+1+ccarry s=(n+ccarry s)+1 by omega] at h0
  have h1 := stepR base 1 3 false (S 3) (S 2) 1 (U 5 (a+6) ++ X) (S 2::S 2::(T (n+ccarry s) ++ cword (next s))) (by rfl)
  have h2 := sweepL base 3 (S 5) (S 4) 3 (a+6) X (S 2::S 2::S 2::(T (n+ccarry s) ++ cword (next s))) (by rfl)
  exact Reach.trans (Reach.trans h0 ⟨_,h1⟩) ⟨_,h2⟩

theorem advance (a n : Nat) (s : CTail) (X : List Sym) :
    Reach base (H (a+1) (n+2) s (S 6::S 6::S 6::X))
      (H (a+10) (n+ccarry s) (next s) X) := by
  let R := T (n+ccarry s) ++ cword (next s)
  have h0 := large a n s (S 6::S 6::X)
  have h1 := drop (a+5) (S 6::X) (S 2::R)
  have h2 := drop (a+7) X R
  exact Reach.trans (Reach.trans h0 h1) h2

def rank : CTail → Nat
  | .c31 => 0 | .c32 => 1 | .c315 => 2 | .c325 => 3 | .c3242 => 4 | .c35221 => 5

def tailOf (r : Nat) : CTail :=
  match r with
  | 0 => .c31 | 1 => .c32 | 2 => .c315 | 3 => .c325 | 4 => .c3242 | _ => .c35221

theorem rank_lt (s : CTail) : rank s < 6 := by cases s <;> decide
theorem tailOf_rank (s : CTail) : tailOf (rank s) = s := by cases s <;> rfl
theorem rank_tailOf (r : Nat) (h : r < 6) : rank (tailOf r) = r := by
  have h' : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 := by omega
  rcases h' with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem balance (n : Nat) (s : CTail) :
    6*(n+ccarry s)+rank (next s)=6*(n+2)+rank s-11 := by
  cases s <;> simp [rank,ccarry,next] <;> omega

theorem iterate (j a n k : Nat) (s : CTail) (X : List Sym)
    (ha : 0<a) (hz : j=0 ∨ 11*j<6*n+rank s) (hk : 3*j≤k) :
    Reach base (H a n s (U 6 k ++ X))
      (H (a+9*j) ((6*n+rank s-11*j)/6)
        (tailOf ((6*n+rank s-11*j)%6)) (U 6 (k-3*j) ++ X)) := by
  induction j generalizing a n k s with
  | zero =>
    have hr := rank_lt s
    have hq : (6*n+rank s)/6=n := by omega
    have hm : (6*n+rank s)%6=rank s := by omega
    simpa [hq,hm,tailOf_rank] using Reach.refl base (H a n s (U 6 k ++ X))
  | succ j ih =>
    have hr := rank_lt s
    have hn : n-2+2=n := by omega
    have ha' : a-1+1=a := by omega
    have hk' : k-3+3=k := by omega
    have h0 := advance (a-1) (n-2) s (U 6 (k-3) ++ X)
    rw [hn,ha',show a-1+10=a+9 by omega] at h0
    have h0' : Reach base (H a n s (U 6 k ++ X))
        (H (a+9) (n-2+ccarry s) (next s) (U 6 (k-3) ++ X)) := by
      have hL := congrArg (fun z => U 6 z ++ X) hk'
      simp only [U,List.replicate_succ,List.cons_append] at hL
      rwa [←hL]
    have hbal := balance (n-2) s
    rw [hn] at hbal
    have h1 := ih (a+9) (n-2+ccarry s) (k-3) (next s) (by omega) (by omega) (by omega)
    have hsum := Reach.trans h0' h1
    have he : 6*(n-2+ccarry s)+rank (next s)-11*j=6*n+rank s-11*(j+1) := by omega
    simpa only [he,show a+9+9*j=a+9*(j+1) by omega,show k-3-3*j=k-3*(j+1) by omega] using hsum

def rounds (n : Nat) (s : CTail) : Nat := (6*n+rank s-1)/11

theorem drain (a n k : Nat) (s : CTail) (X : List Sym) (ha : 0<a)
    (hk : 3*rounds n s≤k) :
    ∃ n' s', n'<2 ∧ 6*n'+rank s'=6*n+rank s-11*rounds n s ∧
      Reach base (H a n s (U 6 k ++ X))
        (H (a+9*rounds n s) n' s' (U 6 (k-3*rounds n s) ++ X)) := by
  have hz : rounds n s=0 ∨ 11*rounds n s<6*n+rank s := by unfold rounds; omega
  let z := 6*n+rank s-11*rounds n s
  have hlt : z<12 := by unfold z rounds; omega
  refine ⟨z/6,tailOf (z%6),by omega,?_,iterate (rounds n s) a n k s X ha hz hk⟩
  rw [rank_tailOf _ (by omega)]
  omega

#print axioms drain
#print axioms advance
end Raw14037DPhase
