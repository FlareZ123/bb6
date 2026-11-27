import Raw140DoubleCore
import Raw140VariantTransfer
namespace Raw14042DGeneral
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140VariantTransfer
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run
abbrev TB (n : Nat) := word (trips n)
def D (k h : Nat) (s : Tail) : Prim := boundary 3 false (U 6 k ++ [S 4]) (U 4 h ++ tailWord s)
def B (p n : Nat) (s : Tail) : Prim := boundary 1 true (U 5 p) (TB n ++ tailWord s)
theorem dFront (k h : Nat) (s : Tail) (hp : 0 < k+h) :
    Reach base (D k h s) (E 1 (k+h-1) (TB (turn k s).1 ++ tailWord (turn k s).2)) := by
  have h0 := dIter k [S 4] (List.replicate h false) s
  have h1 : Reach base (D k h s) (boundary 3 false [S 4]
    (U 4 (k+h) ++ TB (turn k s).1 ++ tailWord (turn k s).2)) := by
    simpa only [D,word_append,word_four,List.append_assoc,merge] using h0
  have h2 := dEndE (k+h-1) (TB (turn k s).1 ++ tailWord (turn k s).2)
  exact Reach.trans h1 (by simpa only [List.append_assoc,show k+h-1+1=k+h by omega] using h2)
theorem oddReturn (k h : Nat) (s : Tail) (ho : (k+h)%2=1) :
    Reach M42 (D k h s) (B (2*(k+h)+2) (turn k s).1 (turn k s).2) := by
  let j := (k+h-1)/2
  have hj : 2*j=k+h-1 := by dsimp [j]; omega
  have hm : 1+4*j+3=2*(k+h)+2 := by omega
  have h0 := dFront k h s (by omega)
  have h1 := eEven j 1 (TB (turn k s).1 ++ tailWord (turn k s).2)
  rw [hj,hm] at h1
  exact Reach.ext (fill_extends _ _) (Reach.trans h0 h1)
theorem oddReturn_rank (k h : Nat) (s : Tail) (ho : (k+h)%2=1) :
    ∃ t : Tail, rank t=(k+rank s)%6 ∧
      Reach M42 (D k h s) (B (2*(k+h)+2) ((k+rank s)/6) t) := by
  have hb := turn_balance k s
  have ht := rank_lt (turn k s).2
  have hn : (turn k s).1=(k+rank s)/6 := by omega
  have hr : rank (turn k s).2=(k+rank s)%6 := by omega
  exact ⟨(turn k s).2, hr, by simpa only [hn] using oddReturn k h s ho⟩
#print axioms oddReturn_rank
end Raw14042DGeneral
