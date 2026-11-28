import Raw14037GBank
import Raw140VariantTransfer
namespace Raw14037BRight
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140VariantTransfer
set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] boundary run

inductive Variant where
  | v37 | v40 | v44 | v83
  deriving DecidableEq, Repr

def table : Variant → Table
  | .v37 => M37 | .v40 => M40 | .v44 => M44 | .v83 => M83

theorem ext (v : Variant) : Extends (table v) := by cases v <;> exact fill_extends _ _

def B (p n : Nat) (s : Tail) : Prim := boundary 1 true (U 5 p) (word (trips n) ++ tailWord s)
def K (p k n : Nat) (s : Tail) (X : List Sym) : Prim := boundary 0 true (U 3 p ++ U 5 k ++ X) (word (trips n) ++ tailWord s)

theorem entry (v : Variant) (X Y : List Sym) :
    Reach (table v) (boundary 1 true (S 5::X) (S 6::S 4::S 4::S 6::S 4::S 4::S 6::Y))
      (boundary 2 true (S 4::S 5::S 5::S 5::S 1::S 3::S 3::X) (S 6::Y)) := by
  cases v with
  | v37 => exact ⟨_,Raw140Framed.execute_sound M37 true true 42 126
      ⟨1,true,[S 5],[S 6,S 4,S 4,S 6,S 4,S 4,S 6]⟩ ⟨2,true,[S 4,S 5,S 5,S 5,S 1,S 3,S 3],[S 6]⟩ X Y (by decide +kernel)⟩
  | v40 => exact ⟨_,Raw140Framed.execute_sound M40 true true 46 130
      ⟨1,true,[S 5],[S 6,S 4,S 4,S 6,S 4,S 4,S 6]⟩ ⟨2,true,[S 4,S 5,S 5,S 5,S 1,S 3,S 3],[S 6]⟩ X Y (by decide +kernel)⟩
  | v44 => exact ⟨_,Raw140Framed.execute_sound M44 true true 42 124
      ⟨1,true,[S 5],[S 6,S 4,S 4,S 6,S 4,S 4,S 6]⟩ ⟨2,true,[S 4,S 5,S 5,S 5,S 1,S 3,S 3],[S 6]⟩ X Y (by decide +kernel)⟩
  | v83 => exact ⟨_,Raw140Framed.execute_sound M83 true true 44 128
      ⟨1,true,[S 5],[S 6,S 4,S 4,S 6,S 4,S 4,S 6]⟩ ⟨2,true,[S 4,S 5,S 5,S 5,S 1,S 3,S 3],[S 6]⟩ X Y (by decide +kernel)⟩

theorem start (v : Variant) (p n : Nat) (s : Tail) :
    Reach (table v) (B (p+1) (n+2) s) (K 7 p (n+carry s) (rho s) []) := by
  let X := U 5 p
  let R := word (trips n) ++ tailWord s
  have h0 : Reach (table v) (B (p+1) (n+2) s)
      (boundary 2 true (S 4::S 5::S 5::S 5::S 1::S 3::S 3::X) R) := by
    have hr := word_tail_even (trips n) s
    have hr' : ∃ Y,R=S 6::Y := by cases n <;> cases s <;> exact ⟨_,rfl⟩
    obtain ⟨Y,hY⟩ := hr'
    have h := entry v X Y
    have he : word (trips (n+2)) ++ tailWord s = S 6::S 4::S 4::S 6::S 4::S 4::R := by rfl
    simpa only [B,he,U,List.replicate_succ,List.cons_append,←hY,X] using h
  have h1 := bounce (trips n) s (S 5::S 5::S 5::S 1::S 3::S 3::X)
  let Y := word (trips n) ++ word (trips (carry s)) ++ tailWord (rho s)
  have h2 := sweepL base 3 (S 5) (S 4) 3 4 (S 1::S 3::S 3::X) Y (by rfl)
  have h3 := Raw140Framed.execute_sound base true true 5 15
    ⟨3,false,[S 1,S 3,S 3],[S 4,S 4,S 4,S 4]⟩ ⟨0,true,[S 3,S 3,S 3,S 3,S 3,S 3,S 3],[]⟩ X Y (by decide +kernel)
  simp only [X,R,Y,Raw140Framed.prim,List.cons_append,List.nil_append,ite_true,List.append_assoc] at h0 h1 h2 h3
  have h := Reach.trans (Reach.trans (Reach.trans h0 (Reach.ext (ext v) h1)) (Reach.ext (ext v) ⟨_,h2⟩)) (Reach.ext (ext v) ⟨_,h3⟩)
  simpa only [K,trips_add,word_append,U,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append,List.append_assoc,List.append_nil] using h

theorem collect (p : Nat) (X Y : List Sym) :
    Reach base (boundary 0 true (U 3 p ++ S 5::X) (S 6::Y))
      (boundary 4 true (S 1::S 1::(U 3 p ++ X)) Y) := by
  have h0 := stepR base 0 4 false (S 6) (S 5) 3 (U 3 p ++ S 5::X) Y (by rfl)
  have h1 := sweepL base 4 (S 3) (S 1) 3 p (S 5::X) (S 5::Y) (by rfl)
  have h2 := stepL base 4 4 true (S 5) (S 1) 1 X (U 1 p ++ S 5::Y) (by rfl)
  have h3 := Raw140ERSweep.many p X (S 5::Y)
  have h4 := stepR base 4 4 true (S 5) (S 1) 7 (S 1::(U 3 p ++ X)) Y (by rfl)
  exact ⟨_,join (join (join (join h0 h1) h2) h3) h4⟩

theorem drop4 (p : Nat) (X Y : List Sym) :
    Reach base (boundary 0 true (U 3 p ++ S 5::X) (S 6::S 4::Y))
      (boundary 0 true (U 3 (p+2) ++ X) (S 6::Y)) := by
  have h0 := collect p X (S 4::Y)
  have h1 := Raw140Framed.execute_sound base true true 6 14
    ⟨4,true,[S 1,S 1],[S 4]⟩ ⟨0,true,[S 3,S 3],[S 6]⟩ (U 3 p ++ X) Y (by decide +kernel)
  exact Reach.trans h0 ⟨_,h1⟩

theorem enter (X R : List Sym) (hR : EvenStart R) :
    Reach base (boundary 4 true (S 1::S 1::X) (S 6::R))
      (boundary 2 true (S 4::S 5::S 1::X) R) := by
  rcases hR with ⟨Y,h|h⟩
  · subst R
    exact ⟨_,Raw140Framed.execute_sound base true true 5 9
      ⟨4,true,[S 1,S 1],[S 6,S 4]⟩ ⟨2,true,[S 4,S 5,S 1],[S 4]⟩ X Y (by decide +kernel)⟩
  · subst R
    exact ⟨_,Raw140Framed.execute_sound base true true 5 9
      ⟨4,true,[S 1,S 1],[S 6,S 6]⟩ ⟨2,true,[S 4,S 5,S 1],[S 6]⟩ X Y (by decide +kernel)⟩

theorem large (p n : Nat) (s : Tail) (X : List Sym) :
    Reach base (boundary 0 true (U 3 p ++ S 5::X) (S 6::S 6::S 4::S 4::(word (trips n) ++ tailWord s)))
      (boundary 0 true (U 3 (p+5) ++ X) (word (trips (n+carry s)) ++ tailWord (rho s))) := by
  let Z := U 3 p ++ X
  let W := false::false::trips n
  let R := word (trips (n+carry s)) ++ tailWord (rho s)
  have h0 := collect p X (S 6::(word W ++ tailWord s))
  have h1 := enter Z (word W ++ tailWord s) (word_tail_even W s)
  have h2 := bounce W s (S 5::S 1::Z)
  have h3 := Raw140Framed.execute_sound base true true 7 21
    ⟨3,false,[S 5,S 5,S 1],[S 4,S 4]⟩ ⟨0,true,[S 3,S 3,S 3,S 3,S 3],[]⟩ Z R (by decide +kernel)
  simp only [W,word,trips_add,word_append,R,Z,List.cons_append,List.append_assoc,Raw140Framed.prim,List.nil_append,ite_true,Bool.false_eq_true,ite_false] at h0 h1 h2 h3
  have h := Reach.trans (Reach.trans (Reach.trans h0 h1) h2) ⟨_,h3⟩
  simpa only [U,List.replicate_succ,List.cons_append,List.append_assoc,R,Z,trips_add,word_append] using h

theorem advance (p k n : Nat) (s : Tail) (X : List Sym) :
    Reach base (K p (k+3) (n+2) s X) (K (p+9) k (n+carry s) (rho s) X) := by
  let Y := word (trips n) ++ tailWord s
  have h0 := drop4 p (S 5::S 5::(U 5 k ++ X)) (S 4::S 6::S 4::S 4::Y)
  have h1 := drop4 (p+2) (S 5::(U 5 k ++ X)) (S 6::S 4::S 4::Y)
  have h2 := large (p+4) n s (U 5 k ++ X)
  simpa only [K,Y,trips,word,word_append,triple,List.nil_append,ite_true,ite_false,Bool.false_eq_true,U,List.replicate_succ,List.cons_append,List.append_assoc,show p+4+5=p+9 by omega] using Reach.trans (Reach.trans h0 h1) h2

def tailOf (r : Nat) : Tail :=
  match r with
  | 0 => .s62 | 1 => .s64 | 2 => .s6221 | 3 => .s6421 | 4 => .s6405 | _ => .s62542

theorem rank_lt (s : Tail) : rank s < 6 := by cases s <;> decide
theorem tailOf_rank (s : Tail) : tailOf (rank s) = s := by cases s <;> rfl
theorem rank_tailOf (r : Nat) (h : r < 6) : rank (tailOf r) = r := by
  have h' : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 := by omega
  rcases h' with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem balance (n : Nat) (s : Tail) :
    6*(n+carry s)+rank (rho s)=6*(n+2)+rank s-11 := by
  cases s <;> simp [rank,carry,rho] <;> omega

theorem iterate (j p n k : Nat) (s : Tail) (X : List Sym)
    (hz : j=0 ∨ 11*j<6*n+rank s) (hk : 3*j≤k) :
    Reach base (K p k n s X)
      (K (p+9*j) (k-3*j) ((6*n+rank s-11*j)/6)
        (tailOf ((6*n+rank s-11*j)%6)) X) := by
  induction j generalizing p n k s with
  | zero =>
    have hr := rank_lt s
    have hq : (6*n+rank s)/6=n := by omega
    have hm : (6*n+rank s)%6=rank s := by omega
    simpa [hq,hm,tailOf_rank] using Reach.refl base (K p k n s X)
  | succ j ih =>
    have hr := rank_lt s
    have hn : n-2+2=n := by omega
    have hk' : k-3+3=k := by omega
    have h0 := advance p (k-3) (n-2) s X
    rw [hn,hk'] at h0
    have hbal := balance (n-2) s
    rw [hn] at hbal
    have h1 := ih (p+9) (n-2+carry s) (k-3) (rho s) (by omega) (by omega)
    have hsum := Reach.trans h0 h1
    have he : 6*(n-2+carry s)+rank (rho s)-11*j=6*n+rank s-11*(j+1) := by omega
    simpa only [he,show p+9+9*j=p+9*(j+1) by omega,show k-3-3*j=k-3*(j+1) by omega] using hsum

def rounds (n : Nat) (s : Tail) : Nat := (6*n+rank s-1)/11

theorem drain (p n k : Nat) (s : Tail) (X : List Sym) 
    (hk : 3*rounds n s≤k) :
    ∃ n' s', n'<2 ∧ 6*n'+rank s'=6*n+rank s-11*rounds n s ∧
      Reach base (K p k n s X)
        (K (p+9*rounds n s) (k-3*rounds n s) n' s' X) := by
  have hz : rounds n s=0 ∨ 11*rounds n s<6*n+rank s := by unfold rounds; omega
  let z := 6*n+rank s-11*rounds n s
  have hlt : z<12 := by unfold z rounds; omega
  refine ⟨z/6,tailOf (z%6),by omega,?_,iterate (rounds n s) p n k s X hz hk⟩
  rw [rank_tailOf _ (by omega)]
  omega

#print axioms drain
#print axioms start
#print axioms advance
end Raw14037BRight
