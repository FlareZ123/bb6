import Raw14037GTerm
import Raw14037DTerm
import Raw14042Counter
namespace Raw14037GBank
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double
open Raw14037Counter (G)
open Raw14037GTerm (finish)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] boundary run

theorem firstPrep (Z Y : List Sym) :
    Reach base (boundary 3 true (S 6::S 2::Z) (S 5::S 4::Y))
      (boundary 1 false Z (S 2::S 2::S 4::S 6::Y)) := by
  exact ⟨_,Raw140Framed.execute_sound base true true 11 29
    ⟨3,true,[S 6,S 2],[S 5,S 4]⟩ ⟨1,false,[],[S 2,S 2,S 4,S 6]⟩ Z Y (by decide +kernel)⟩

theorem first (v : Nat) (X Y : List Sym) :
    Reach base (G v (S 3::X) (S 5::S 4::Y))
      (G (v+1) X (S 4::S 6::Y)) := by
  have h0 := Raw140Framed.execute_sound base true true 11 29
    ⟨3,true,[S 6,S 2],[S 5,S 4]⟩ ⟨1,false,[],[S 2,S 2,S 4,S 6]⟩ (U 6 v ++ S 7::S 3::X) Y (by decide +kernel)
  exact Reach.trans ⟨_,h0⟩ (finish v 1 X (S 4::S 6::Y))

theorem enter (X R : List Sym) (hR : EvenStart R) :
    Reach base (boundary 3 true (S 6::S 2::X) (S 4::S 6::R))
      (boundary 2 true (S 4::S 5::S 2::S 6::X) R) := by
  rcases hR with ⟨Y,h|h⟩
  · subst R
    exact ⟨_,Raw140Framed.execute_sound base true true 12 30
      ⟨3,true,[S 6,S 2],[S 4,S 6,S 4]⟩ ⟨2,true,[S 4,S 5,S 2,S 6],[S 4]⟩ X Y (by decide +kernel)⟩
  · subst R
    exact ⟨_,Raw140Framed.execute_sound base true true 12 30
      ⟨3,true,[S 6,S 2],[S 4,S 6,S 6]⟩ ⟨2,true,[S 4,S 5,S 2,S 6],[S 6]⟩ X Y (by decide +kernel)⟩

theorem secondPrep (Z : List Sym) (W : List Bool) (s : Tail) :
    Reach base (boundary 3 true (S 6::S 2::Z) (S 4::S 6::(word W ++ tailWord s)))
      (boundary 1 false Z (S 2::S 5::S 4::S 4::(word W ++ word (trips (carry s)) ++ tailWord (rho s)))) := by
  let R := word W ++ word (trips (carry s)) ++ tailWord (rho s)
  have h0 := enter Z (word W ++ tailWord s) (word_tail_even W s)
  have h1 := bounce W s (S 5::S 2::S 6::Z)
  have h2 := Raw140Framed.execute_sound base true true 4 12
    ⟨3,false,[S 5,S 5,S 2,S 6],[]⟩ ⟨1,false,[],[S 2,S 5,S 4,S 4]⟩ Z R (by decide +kernel)
  simp only [Raw140Framed.prim,List.cons_append,List.nil_append,ite_true,List.append_assoc] at h2
  exact Reach.trans (Reach.trans h0 h1) ⟨_,h2⟩

theorem second (v : Nat) (W : List Bool) (s : Tail) (X : List Sym) :
    Reach base (G v (S 3::X) (S 4::S 6::(word W ++ tailWord s)))
      (G v X (S 5::S 4::S 4::(word W ++ word (trips (carry s)) ++ tailWord (rho s)))) := by
  let Z := U 6 v ++ S 7::S 3::X
  let R := word W ++ word (trips (carry s)) ++ tailWord (rho s)
  have h0 := enter Z (word W ++ tailWord s) (word_tail_even W s)
  have h1 := bounce W s (S 5::S 2::S 6::Z)
  have h2 := Raw140Framed.execute_sound base true true 4 12
    ⟨3,false,[S 5,S 5,S 2,S 6],[]⟩ ⟨1,false,[],[S 2,S 5,S 4,S 4]⟩ Z R (by decide +kernel)
  simp only [Raw140Framed.prim,List.cons_append,List.nil_append,ite_true,List.append_assoc] at h2
  have h3 := finish v 0 X (S 5::S 4::S 4::R)
  simpa only [G,Z,R,Nat.add_zero,List.append_assoc] using Reach.trans (Reach.trans (Reach.trans h0 h1) ⟨_,h2⟩) h3

def P (v a n : Nat) (s : Tail) (X : List Sym) : Prim :=
  G v X (S 5::(U 4 (a+1) ++ word (trips n) ++ tailWord s))

theorem pair (v a n : Nat) (s : Tail) (X : List Sym) :
    Reach base (P v a n s (S 3::S 3::X))
      (P (v+1) (a+1) (n+carry s) (rho s) X) := by
  let W := List.replicate a false ++ trips n
  let Y := word (trips n) ++ tailWord s
  have h0 := first v (S 3::X) (U 4 a ++ Y)
  have h1 := second (v+1) W s X
  simp only [W,word_append,word_four,List.append_assoc] at h1
  have h := Reach.trans h0 h1
  simpa only [P,Y,U,List.replicate_succ,List.cons_append,List.append_assoc,trips_add,word_append] using h

theorem iterate (k v a n : Nat) (s : Tail) (X : List Sym) :
    Reach base (P v a n s (U 3 (2*k) ++ X))
      (P (v+k) (a+k) (n+(turn k s).1) (turn k s).2 X) := by
  induction k generalizing v a n s with
  | zero => simpa [turn,U] using Reach.refl base (P v a n s X)
  | succ k ih =>
    have h0 := pair v a n s (U 3 (2*k) ++ X)
    have h1 := ih (v+1) (a+1) (n+carry s) (rho s)
    simpa only [turn,show 2*(k+1)=2*k+1+1 by omega,U,List.replicate_succ,List.cons_append,
      show v+1+k=v+(k+1) by omega,show a+1+k=a+(k+1) by omega,Nat.add_assoc] using Reach.trans h0 h1

theorem seed542 (v : Nat) (X : List Sym) :
    Reach base (G v (U 3 12 ++ X) [S 5,S 4,S 2]) (P (v+6) 8 0 .s62 X) := by
  have h := Raw14037GTerm.follow_sound 12 v 6 [S 5,S 4,S 2] (S 5::(U 4 9 ++ [S 6,S 2])) X (by decide +kernel)
  exact h

-- The marker 7 2 is consumed once; the output is an ordinary DR bank.
theorem last (v c : Nat) (R : List Sym) (h : 1 ≤ v+c) :
    Reach base (boundary 1 false (U 6 v ++ [S 7,S 2]) (U 2 (c+1) ++ R))
      (boundary 3 true (S 6::S 2::U 6 (v+c+1)) R) := by
  let k := v+c-1
  have hk : v+c+1=k+2 := by dsimp [k]; omega
  have h0 := sweepL base 1 (S 6) (S 2) 3 v [S 7,S 2] (U 2 (c+1) ++ R) (by rfl)
  change run base (v*3) (boundary 1 false (U 6 v ++ [S 7,S 2]) (U 2 (c+1) ++ R)) = some (boundary 1 false [S 7,S 2] (U 2 v ++ (U 2 (c+1) ++ R))) at h0
  rw [merge,show v+(c+1)=k+2 by dsimp [k]; omega] at h0
  have h1 := Raw14042CounterLocal.finishZero (U 2 k ++ R)
  have h2 := Raw14042Counter.scanTwo (k+1) [S 6] R
  have h3 := stepR base 4 3 true (S 3) (S 6) 5 (S 2::U 6 (k+2)) R (by rfl)
  have h2' : Reach base (boundary 4 true [S 2,S 6] (S 3::(U 2 (k+1) ++ R)))
      (boundary 4 true (S 2::U 6 (k+2)) (S 3::R)) := by
    simpa only [U,List.replicate_succ,rep_cons,List.cons_append,List.append_nil] using h2
  have h01 : Reach base (boundary 1 false (U 6 v ++ [S 7,S 2]) (U 2 (c+1) ++ R))
      (boundary 4 true [S 2,S 6] (S 3::(U 2 (k+1) ++ R))) := by
    exact ⟨_,join h0 h1⟩
  rw [hk]
  exact Reach.trans (Reach.trans h01 h2') ⟨_,h3⟩

theorem lastEven (v a n : Nat) (s : Tail) :
    Reach base (P v a n s [S 2])
      (boundary 1 false [] (U 2 (v+3) ++ S 5::(U 4 (a+2) ++ word (trips (n+carry s)) ++ tailWord (rho s)))) := by
  let W := List.replicate a false ++ trips n
  let R := word W ++ word (trips (carry s)) ++ tailWord (rho s)
  have h0 := firstPrep (U 6 v ++ [S 7,S 2]) (U 4 a ++ word (trips n) ++ tailWord s)
  have h1 := last v 1 (S 4::S 6::(word W ++ tailWord s)) (by omega)
  have h2 := secondPrep (U 6 (v+2)) W s
  have h3 := sweepL base 1 (S 6) (S 2) 3 (v+2) [] (S 2::S 5::S 4::S 4::R) (by rfl)
  have h3' : Reach base (boundary 1 false (U 6 (v+2)) (S 2::S 5::S 4::S 4::R))
      (boundary 1 false [] (U 2 (v+3) ++ S 5::S 4::S 4::R)) := by
    change run base ((v+2)*3) (boundary 1 false (U 6 (v+2) ++ []) (S 2::S 5::S 4::S 4::R)) = some (boundary 1 false [] (U 2 (v+2) ++ (U 2 1 ++ S 5::S 4::S 4::R))) at h3
    rw [List.append_nil,merge] at h3
    exact ⟨_,h3⟩
  simp only [W,word_append,word_four,List.append_assoc,show v+1+1=v+2 by omega,U,List.replicate_succ,List.cons_append] at h0 h1 h2 h3'
  simp only [R,W,word_append,word_four,List.append_assoc,List.replicate_zero,List.nil_append] at h0 h1 h2 h3'
  have h := Reach.trans (Reach.trans (Reach.trans h0 h1) h2) h3'
  simpa only [P,G,W,R,word_append,word_four,trips_add,U,List.replicate_succ,List.cons_append,List.append_assoc] using h

theorem lastOdd (v a n : Nat) (s : Tail) :
    Reach base (P v a n s [S 3,S 2])
      (boundary 1 false [] (U 2 (v+4) ++ S 4::S 6::(U 4 (a+1) ++ word (trips (n+carry s)) ++ tailWord (rho s)))) := by
  let W := List.replicate a false ++ trips n
  let R := word W ++ word (trips (carry s)) ++ tailWord (rho s)
  have h0 := first v [S 2] (U 4 a ++ word (trips n) ++ tailWord s)
  have h1 := secondPrep (U 6 (v+1) ++ [S 7,S 2]) W s
  have h2 := last (v+1) 0 (S 5::S 4::S 4::R) (by omega)
  have h3 := firstPrep (U 6 (v+2)) (S 4::R)
  have h4 := sweepL base 1 (S 6) (S 2) 3 (v+2) [] (S 2::S 2::S 4::S 6::S 4::R) (by rfl)
  have h4' : Reach base (boundary 1 false (U 6 (v+2)) (S 2::S 2::S 4::S 6::S 4::R))
      (boundary 1 false [] (U 2 (v+4) ++ S 4::S 6::S 4::R)) := by
    change run base ((v+2)*3) (boundary 1 false (U 6 (v+2) ++ []) (S 2::S 2::S 4::S 6::S 4::R)) = some (boundary 1 false [] (U 2 (v+2) ++ (U 2 2 ++ S 4::S 6::S 4::R))) at h4
    rw [List.append_nil,merge,show v+2+2=v+4 by omega] at h4
    exact ⟨_,h4⟩
  simp only [W,word_append,word_four,List.append_assoc,Nat.add_zero,show v+1+1=v+2 by omega,U,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append] at h0 h1 h2 h3 h4'
  simp only [R,W,word_append,word_four,List.append_assoc] at h0 h1 h2 h3 h4'
  have h := Reach.trans (Reach.trans (Reach.trans (Reach.trans h0 h1) h2) h3) h4'
  simpa only [P,G,W,R,word_append,word_four,trips_add,U,List.replicate_succ,List.cons_append,List.append_assoc] using h

-- A finite prefix sends the exceptional 55 branch to D-left, without
-- inspecting any of the variable bank or the trailing marker.
theorem seed55 (v : Nat) (X : List Sym) :
    Reach base (G v X [S 5,S 5])
      (boundary 3 false (U 6 v ++ S 7::X) (U 4 5 ++ [S 2,S 5,S 4,S 2])) := by
  exact ⟨_,Raw140Framed.execute_sound base true false 185 517
    ⟨3,true,[S 6,S 2],[S 5,S 5]⟩ ⟨3,false,[],[S 4,S 4,S 4,S 4,S 4,S 2,S 5,S 4,S 2]⟩ (U 6 v ++ S 7::X) [] (by decide +kernel)⟩

theorem convert55 (v : Nat) (X : List Sym) :
    Reach base (G (v+1) X [S 5,S 5])
      (boundary 3 false (S 7::X) (U 4 (v+8) ++ word (trips (turn v .s62).1) ++ tailWord (turn v .s62).2)) := by
  have h0 := seed55 (v+1) X
  let r : Raw14037DTerm.Rule := ⟨[S 2,S 5,S 4,S 2],1,2,[S 6,S 2],13,35⟩
  have h1 := r.sound (by decide +kernel) 4 (U 6 v ++ S 7::X)
  have h2 := dIter v (S 7::X) (List.replicate 8 false) .s62
  simp only [word_append,word_four,List.append_assoc,merge] at h2
  simp only [r,Raw14037DTerm.Rule.src,Raw14037DTerm.Rule.dst,Raw14037DTerm.Rule.extra5,Raw14037DTerm.Rule.extra4] at h1
  simpa only [U,List.replicate_succ,List.cons_append,List.append_assoc] using Reach.trans (Reach.trans h0 h1) h2

#print axioms lastEven
#print axioms lastOdd
#print axioms convert55
#print axioms seed542
#print axioms last
#print axioms pair
#print axioms iterate
end Raw14037GBank
