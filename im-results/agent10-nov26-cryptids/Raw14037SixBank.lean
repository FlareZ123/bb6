import Raw140ERExit
import Raw140VariantTransfer
namespace Raw14037SixBank
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140ERSuffix Raw140ERSuffixLocal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] boundary run

theorem loopOne (X Y : List Sym) :
    run base 19 (boundary 3 true (S 6::S 2::X) (S 2::Y)) = some (boundary 3 true (S 6::S 2::S 6::X) (Y)) := by
  have h0 := stepR base 3 1 false (S 2) (S 3) 1 (S 6::S 2::X) (Y) (by rfl)
  have h1 := stepL base 1 1 false (S 6) (S 2) 3 (S 2::X) (S 3::Y) (by rfl)
  have h2 := stepL base 1 2 true (S 2) (S 6) 1 (X) (S 2::S 3::Y) (by rfl)
  have h3 := stepR base 2 3 true (S 2) (S 6) 7 (S 6::X) (S 3::Y) (by rfl)
  have h4 := stepR base 3 4 false (S 3) (S 3) 1 (S 6::S 6::X) (Y) (by rfl)
  have h5 := stepL base 4 4 true (S 6) (S 2) 1 (S 6::X) (S 3::Y) (by rfl)
  have h6 := stepR base 4 3 true (S 3) (S 6) 5 (S 2::S 6::X) (Y) (by rfl)
  exact join (join (join (join (join (join (h0) h1) h2) h3) h4) h5) h6

theorem seed (X Y : List Sym) :
    run base 26 (boundary 1 false (S 7::S 3::X) (S 2::Y)) = some (boundary 3 true (S 6::S 2::S 7::X) (Y)) := by
  have h0 := stepL base 1 3 true (S 7) (S 6) 7 (S 3::X) (S 2::Y) (by rfl)
  have h1 := stepR base 3 1 false (S 2) (S 3) 1 (S 6::S 3::X) (Y) (by rfl)
  have h2 := stepL base 1 1 false (S 6) (S 2) 3 (S 3::X) (S 3::Y) (by rfl)
  have h3 := stepL base 1 2 true (S 3) (S 7) 1 (X) (S 2::S 3::Y) (by rfl)
  have h4 := stepR base 2 3 true (S 2) (S 6) 7 (S 7::X) (S 3::Y) (by rfl)
  have h5 := stepR base 3 4 false (S 3) (S 3) 1 (S 6::S 7::X) (Y) (by rfl)
  have h6 := stepL base 4 4 true (S 6) (S 2) 1 (S 7::X) (S 3::Y) (by rfl)
  have h7 := stepR base 4 3 true (S 3) (S 6) 5 (S 2::S 7::X) (Y) (by rfl)
  exact join (join (join (join (join (join (join (h0) h1) h2) h3) h4) h5) h6) h7

theorem turn1 (X Y : List Sym) :
    run base 9 (boundary 3 true (S 6::S 2::X) (S 1::Y)) = some (boundary 4 false (S 2::S 2::X) (S 5::Y)) := by
  have h0 := stepR base 3 4 false (S 1) (S 1) 1 (S 6::S 2::X) (Y) (by rfl)
  have h1 := stepL base 4 4 true (S 6) (S 2) 1 (S 2::X) (S 1::Y) (by rfl)
  have h2 := stepR base 4 4 false (S 1) (S 5) 7 (S 2::S 2::X) (Y) (by rfl)
  exact join (join (h0) h1) h2

theorem turn5 (X Y : List Sym) :
    run base 9 (boundary 3 true (S 6::S 2::X) (S 5::Y)) = some (boundary 4 true (S 1::S 2::S 2::X) (Y)) := by
  have h0 := stepR base 3 4 false (S 5) (S 5) 1 (S 6::S 2::X) (Y) (by rfl)
  have h1 := stepL base 4 4 true (S 6) (S 2) 1 (S 2::X) (S 5::Y) (by rfl)
  have h2 := stepR base 4 4 true (S 5) (S 1) 7 (S 2::S 2::X) (Y) (by rfl)
  exact join (join (h0) h1) h2

theorem loopMany (n : Nat) (X Y : List Sym) :
    run base (19*n) (boundary 3 true (S 6::S 2::X) (U 2 n ++ Y)) =
    some (boundary 3 true (S 6::S 2::(U 6 n ++ X)) Y) := by
  induction n generalizing X with
  | zero => simp [U,run]
  | succ n ih =>
    have h := join (loopOne X (U 2 n ++ Y)) (ih (S 6::X))
    simpa only [U,List.replicate_succ,List.cons_append,rep_cons,
      show 19+19*n=19*(n+1) by omega] using h

theorem inner (v k : Nat) (X Y : List Sym) :
    run base (22*(v+k+2)+3*k+38)
      (boundary 4 false (S 2::S 2::(U 6 v ++ S 7::S 3::X)) (U 1 k ++ S 5::Y)) =
    some (boundary 3 true (S 6::S 2::(U 6 (v+k+2) ++ S 7::X)) Y) := by
  let L := S 7::S 3::X
  let R := U 1 k ++ S 5::Y
  have h0 := stepL base 4 1 false (S 2) (S 1) 3 (S 2::(U 6 v ++ L)) R (by rfl)
  have h1 := stepL base 1 2 true (S 2) (S 6) 1 (U 6 v ++ L) (S 1::R) (by rfl)
  have h2 := sweepR base 2 (S 1) (S 6) 3 (k+1) (U 6 (v+1) ++ L) (S 5::Y) (by rfl)
  have h2' : run base ((k+1)*3) (boundary 2 true (S 6::(U 6 v ++ L)) (S 1::R)) =
      some (boundary 2 true (U 6 (v+k+2) ++ L) (S 5::Y)) := by
    have he : k+1+(v+1)=v+k+2 := by omega
    rw [merge 6 (k+1) (v+1),he] at h2
    simpa only [R,U,List.replicate_succ,List.cons_append] using h2
  have h3 := stepR base 2 1 false (S 5) (S 2) 5 (U 6 (v+k+2) ++ L) Y (by rfl)
  have h4 := sweepL base 1 (S 6) (S 2) 3 (v+k+2) L (S 2::Y) (by rfl)
  have h5 := seed X (U 2 (v+k+2) ++ Y)
  have h4' : run base ((v+k+2)*3) (boundary 1 false (U 6 (v+k+2) ++ L) (S 2::Y)) =
      some (boundary 1 false L (S 2::(U 2 (v+k+2) ++ Y))) := by
    simpa only [U,rep_cons] using h4
  have h6 := loopMany (v+k+2) (S 7::X) Y
  have h := join (join (join (join (join (join h0 h1) h2') h3) h4') h5) h6
  simpa only [L,R,show 3+1+(k+1)*3+5+(v+k+2)*3+26+19*(v+k+2)=22*(v+k+2)+3*k+38 by omega] using h

theorem core (v w : Nat) (X Y : List Sym) :
    run base (66*v+628)
      (boundary 4 true (S 3::S 3::S 3::S 2::S 2::(U 6 v ++ S 7::(U 3 (w+3) ++ X))) (S 1::S 1::S 1::S 5::Y)) =
    some (boundary 4 true (S 1::S 2::S 2::(U 6 (v+9) ++ S 7::(U 3 w ++ X))) Y) := by
  let L := S 2::S 2::(U 6 v ++ S 7::(U 3 (w+3) ++ X))
  have h0 := stepR base 4 4 false (S 1) (S 5) 7 (S 3::S 3::S 3::L) (S 1::S 1::S 5::Y) (by rfl)
  have h1 := sweepL base 4 (S 3) (S 1) 3 3 L (S 5::S 1::S 1::S 5::Y) (by rfl)
  have h2 := inner v 3 (U 3 (w+2) ++ X) (S 1::S 1::S 5::Y)
  have h3 := turn1 (U 6 (v+5) ++ S 7::(U 3 (w+2) ++ X)) (S 1::S 5::Y)
  have h4 := inner (v+5) 0 (U 3 (w+1) ++ X) (S 1::S 5::Y)
  have h5 := turn1 (U 6 (v+7) ++ S 7::(U 3 (w+1) ++ X)) (S 5::Y)
  have h6 := inner (v+7) 0 (U 3 w ++ X) (S 5::Y)
  have h7 := turn5 (U 6 (v+9) ++ S 7::(U 3 w ++ X)) Y
  simp only [U,List.replicate_succ,List.cons_append,List.replicate_zero,List.nil_append,L,
    show v+3+2=v+5 by omega,show v+5+0+2=v+7 by omega,show v+7+0+2=v+9 by omega] at h0 h1 h2 h3 h4 h5 h6 h7
  have h := join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7
  simpa only [U,List.replicate_succ,List.cons_append,
    show 7+3*3+(22*(v+5)+3*3+38)+9+(22*(v+7)+3*0+38)+9+(22*(v+9)+3*0+38)+9=66*v+628 by omega] using h

open Raw140ERExit (trip133 trip115 extra)

theorem preprocess (j u v w : Nat) (X Y : List Sym) :
    run base (5+3*(j+1)+21*(u+1)+66*v+628)
      (boundary 4 false (U 3 (j+1) ++ trip133 (u+2) ++ S 2::S 2::(U 6 v ++ S 7::(U 3 (w+3) ++ X))) Y) =
    some (boundary 4 true (S 1::S 2::S 2::(U 6 (v+9) ++ S 7::(U 3 w ++ X))) (trip115 u ++ U 1 j ++ Y)) := by
  let W := S 2::S 2::(U 6 v ++ S 7::(U 3 (w+3) ++ X))
  have h0 := prepareCarry j (S 3::S 3::S 1::S 3::S 3::(trip133 u ++ W)) Y
  have h1 := tripLoop (trip133 u ++ W) (U 1 j ++ Y)
  have h2 := Raw140ERExit.pump u W (U 1 j ++ Y)
  have h3 := core v w X (trip115 u ++ (U 1 j ++ Y))
  simp only [trip133,U,List.replicate_succ,List.cons_append,List.append_assoc] at h0 h1 h2
  have h := join (join (join h0 h1) h2) h3
  simpa only [W,trip133,U,List.replicate_succ,List.cons_append,List.append_assoc,
    show 5+3*(j+1)+(7+3*3+3+1+1)+21*u+(66*v+628)=5+3*(j+1)+21*(u+1)+66*v+628 by omega] using h

theorem trip133_snoc (n : Nat) : trip133 (n+1) = trip133 n ++ [S 1,S 3,S 3] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change S 1::S 3::S 3::trip133 (n+1) = (S 1::S 3::S 3::trip133 n) ++ [S 1,S 3,S 3]
    simp only [ih,List.cons_append]

theorem erMany (n : Nat) (X Y : List Sym) :
    run base (45*n) (boundary 4 true (S 1::X) (trip115 n ++ Y)) =
    some (boundary 4 true (S 1::(trip133 n ++ X)) Y) := by
  have he : Raw140VariantTransfer.trip n = trip115 n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Raw140VariantTransfer.trip,trip115,ih]
  have hb : Raw140VariantTransfer.bank n = trip133 n := by
    clear he
    induction n with
    | zero => rfl
    | succ n ih => simp only [Raw140VariantTransfer.bank,trip133_snoc,ih]
  simpa only [he,hb] using Raw140VariantTransfer.erMany base (fun _ _ _ h => h) n X Y

def F (u v w : Nat) (s : Tail) (X : List Sym) : Prim :=
  boundary 4 true (S 1::(trip133 u ++ S 2::S 2::(U 6 v ++ S 7::(U 3 w ++ X)))) (tailWord s)

def C : Tail → Nat
  | .t542 => 684
  | .t152 => 708
  | .t1121 => 722
  | .t5215 => 694
  | .t1155 => 750
  | .t11511 => 817

theorem advance (u v w : Nat) (s : Tail) (X : List Sym) :
    run base (66*u+66*v+C s) (F (u+2) v (w+3) s X) =
    some (F (u+extra s) (v+9) w (rho s) X) := by
  let W := S 2::S 2::(U 6 v ++ S 7::(U 3 (w+3) ++ X))
  let W' := S 2::S 2::(U 6 (v+9) ++ S 7::(U 3 w ++ X))
  cases s with
  | t542 =>
    have h0 := prep542 (trip133 (u+2) ++ W)
    have h1 := preprocess 1 u v w X [S 5,S 2]
    have h2 := erMany u W' (U 1 1 ++ [S 5,S 2])
    simp only [W,W',U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] at h0 h1 h2
    have h := join (join h0 h1) h2
    simpa only [F,extra,rho,tailWord,C,Nat.add_zero,U,List.replicate_succ,List.cons_append,
      show 24+(5+3*(1+1)+21*(u+1)+66*v+628)+45*u=66*u+66*v+684 by omega] using h
  | t152 =>
    have h0 := prep152 (trip133 (u+2) ++ W)
    have h1 := preprocess 1 u v w X [S 1,S 2,S 1]
    have h2 := erMany u W' (U 1 1 ++ [S 1,S 2,S 1])
    simp only [W,W',U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] at h0 h1 h2
    have h := join (join h0 h1) h2
    simpa only [F,extra,rho,tailWord,C,Nat.add_zero,U,List.replicate_succ,List.cons_append,
      show 48+(5+3*(1+1)+21*(u+1)+66*v+628)+45*u=66*u+66*v+708 by omega] using h
  | t1121 =>
    have h0 := prep1121 (trip133 (u+2) ++ W)
    have h1 := preprocess 0 u v w X [S 5,S 2,S 1,S 5]
    have h2 := erMany u W' (U 1 0 ++ [S 5,S 2,S 1,S 5])
    simp only [W,W',U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] at h0 h1 h2
    have h := join (join h0 h1) h2
    simpa only [F,extra,rho,tailWord,C,Nat.add_zero,U,List.replicate_succ,List.cons_append,
      show 65+(5+3*(0+1)+21*(u+1)+66*v+628)+45*u=66*u+66*v+722 by omega] using h
  | t5215 =>
    have h0 := prep5215 (trip133 (u+2) ++ W)
    have h1 := preprocess 0 u v w X [S 1,S 1,S 5,S 5]
    have h2 := erMany u W' (U 1 0 ++ [S 1,S 1,S 5,S 5])
    simp only [W,W',U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] at h0 h1 h2
    have h := join (join h0 h1) h2
    simpa only [F,extra,rho,tailWord,C,Nat.add_zero,U,List.replicate_succ,List.cons_append,
      show 37+(5+3*(0+1)+21*(u+1)+66*v+628)+45*u=66*u+66*v+694 by omega] using h
  | t1155 =>
    have h0 := prep1155 (trip133 (u+2) ++ W)
    have h1 := preprocess 2 u v w X [S 5,S 1,S 1]
    have h2 := erMany u W' (U 1 2 ++ [S 5,S 1,S 1])
    simp only [W,W',U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] at h0 h1 h2
    have h := join (join h0 h1) h2
    simpa only [F,extra,rho,tailWord,C,Nat.add_zero,U,List.replicate_succ,List.cons_append,
      show 87+(5+3*(2+1)+21*(u+1)+66*v+628)+45*u=66*u+66*v+750 by omega] using h
  | t11511 =>
    have h0 := prep11511 (trip133 (u+2) ++ W)
    have h1 := preprocess 2 u v w X [S 5,S 5,S 4,S 2]
    have h2 := erMany (u+1) W' [S 5,S 4,S 2]
    simp only [W,W',U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] at h0 h1 h2
    rw [Raw140ERExit.trip115_snoc] at h2
    simp only [List.append_assoc,List.cons_append] at h2
    have h := join (join h0 h1) h2
    simpa only [F,extra,rho,tailWord,C,Nat.add_zero,U,List.replicate_succ,List.cons_append,
      show 109+(5+3*(2+1)+21*(u+1)+66*v+628)+45*(u+1)=66*u+66*v+817 by omega] using h

#print axioms inner
#print axioms advance

def rank : Tail → Nat
  | .t542 => 0
  | .t152 => 1
  | .t1121 => 2
  | .t5215 => 3
  | .t1155 => 4
  | .t11511 => 5

def tailOf (n : Nat) : Tail :=
  match n with
  | 0 => .t542
  | 1 => .t152
  | 2 => .t1121
  | 3 => .t5215
  | 4 => .t1155
  | _ => .t11511

theorem rank_lt (s : Tail) : rank s < 6 := by cases s <;> decide

theorem tailOf_rank (s : Tail) : tailOf (rank s) = s := by cases s <;> rfl

theorem balance (u : Nat) (s : Tail) :
    6*(u+extra s)+rank (rho s) = 6*(u+2)+rank s-11 := by
  cases s <;> simp [extra,rank,rho] <;> omega

theorem drainN (n u v w : Nat) (s : Tail) (X : List Sym)
    (hz : n = 0 ∨ 11*n < 6*u+rank s) (hw : 3*n ≤ w) :
    ∃ t, run base t (F u v w s X) =
      some (F ((6*u+rank s-11*n)/6) (v+9*n) (w-3*n)
        (tailOf ((6*u+rank s-11*n)%6)) X) := by
  induction n generalizing u v w s with
  | zero =>
    have hr := rank_lt s
    have ha : (6*u+rank s)/6=u := by omega
    have hb : (6*u+rank s)%6=rank s := by omega
    exact ⟨0, by simp [ha,hb,tailOf_rank,run]⟩
  | succ n ih =>
    have hr := rank_lt s
    have hu : u-2+2=u := by omega
    have hw' : w-3+3=w := by omega
    have h := advance (u-2) v (w-3) s X
    rw [hu,hw'] at h
    have he := balance (u-2) s
    rw [hu] at he
    obtain ⟨t,ht⟩ := ih (u-2+extra s) (v+9) (w-3) (rho s) (by omega) (by omega)
    have hsum := join h ht
    have ha : 6*(u-2+extra s)+rank (rho s)-11*n=6*u+rank s-11*(n+1) := by omega
    have hv : v+9+9*n=v+9*(n+1) := by omega
    have hb : w-3-3*n=w-3*(n+1) := by omega
    exact ⟨_, by simpa only [ha,hv,hb] using hsum⟩

def iterations (u : Nat) (s : Tail) : Nat := (6*u+rank s-1)/11

theorem drain (u v w : Nat) (s : Tail) (X : List Sym)
    (hw : 3*iterations u s ≤ w) :
    ∃ t u' s', u' < 2 ∧
      6*u'+rank s'=6*u+rank s-11*iterations u s ∧
      run base t (F u v w s X) =
      some (F u' (v+9*iterations u s) (w-3*iterations u s) s' X) := by
  have hz : iterations u s=0 ∨ 11*iterations u s < 6*u+rank s := by
    unfold iterations; omega
  obtain ⟨t,ht⟩ := drainN (iterations u s) u v w s X hz hw
  let z := 6*u+rank s-11*iterations u s
  have hlt : z < 12 := by unfold z iterations; omega
  have htail : rank (tailOf (z%6)) = z%6 := by
    have h : z%6 < 6 := by omega
    have hh : z%6=0 ∨ z%6=1 ∨ z%6=2 ∨ z%6=3 ∨ z%6=4 ∨ z%6=5 := by omega
    rcases hh with h|h|h|h|h|h <;> rw [h] <;> rfl
  refine ⟨t,z/6,tailOf (z%6),by omega,?_,ht⟩
  rw [htail]
  omega

#print axioms drainN
#print axioms drain
end Raw14037SixBank
