import Raw14042MixedExitOdd
import Raw14042BGeneral
import Raw14042ExtraTail
namespace Raw14042MixedExitEvenC
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer Raw140Double
open Raw14042AWord Raw14042DExit Raw14042DExitTail Raw14042BGeneral
open Raw14042DMixed (AT aw tr15_add)
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] run boundary
abbrev RR := Reach base
private theorem rr {k : Nat} {c d : Prim} (h : run base k c = some d) : RR c d := ⟨k,h⟩

theorem turn_balance (k : Nat) (s : AT) : 6*(Raw14042DMixed.turn k s).1+arank (Raw14042DMixed.turn k s).2=k+arank s := by
  induction k generalizing s with
  | zero => simp [Raw14042DMixed.turn]
  | succ k ih =>
    have h := ih (Raw14042DMixed.an s)
    have h' : 6*Raw14042AWord.ac s+arank (Raw14042DMixed.an s)=arank s+1 := by cases s <;> decide
    change 6*(Raw14042AWord.ac s+(Raw14042DMixed.turn k (Raw14042DMixed.an s)).1)+arank (Raw14042DMixed.turn k (Raw14042DMixed.an s)).2=k+1+arank s
    omega

theorem ta_eq (n : Nat) : Raw14042AWord.TA n = Raw14042Bank.T n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Raw14042AWord.TA,tcons,ih]

theorem cEvenExit (k n : Nat) (s : AT) (hb : 6*n+arank s=2*k+3) :
    RR (boundary 3 false [S 4] (U 4 (2*k+5) ++ S 0::S 5::(U 1 (2*k+3) ++ S 5::(Raw14042AWord.TA n ++ aw s))))
      (A (12*k+44) (Raw14042Bank.T (k+1) ++ [S 1,S 1])) := by
  let W := List.replicate (2*k+3) false ++ true::tr15 n
  let Y := w15 W ++ aw s
  let Z := S 0::S 5::Y
  have h0 := dEndE (2*k+4) Z
  have h1 := eEven (k+2) 1 Z
  have h2 := rr (Raw14042DExitLocal.b05 (U 5 (4*k+11)) Y)
  have h3 := dropFirst W (U 5 (4*k+10)) s
  have h4 := dropMany (4*k+10) (false::true::true::W ++ tr15 (Raw14042AWord.ac s)) [] (Raw14042DMixed.an s)
  have hb' := turn_balance (4*k+10) (Raw14042DMixed.an s)
  have hs : 6*Raw14042AWord.ac s+arank (Raw14042DMixed.an s)=arank s+1 := by cases s <;> decide
  have hlt := arank_lt (Raw14042DMixed.turn (4*k+10) (Raw14042DMixed.an s)).2
  have hcount : n+Raw14042AWord.ac s+(Raw14042DMixed.turn (4*k+10) (Raw14042DMixed.an s)).1=k+2 := by omega
  have hrank : arank (Raw14042DMixed.turn (4*k+10) (Raw14042DMixed.an s)).2=2 := by omega
  have htail : (Raw14042DMixed.turn (4*k+10) (Raw14042DMixed.an s)).2 = .t1121 := by
    generalize (Raw14042DMixed.turn (4*k+10) (Raw14042DMixed.an s)).2 = t at hrank ⊢
    cases t <;> simp_all [arank]
  have h01 : RR (boundary 3 false [S 4] (U 4 (2*k+5) ++ Z)) (boundary 1 true (U 5 (4*k+12)) Z) := by
    simpa only [show 2*(k+2)=2*k+4 by omega,show 1+4*(k+2)+3=4*k+12 by omega] using Reach.trans h0 h1
  have h2' : RR (boundary 1 true (U 5 (4*k+12)) Z) (boundary 4 true (S 1::S 1::S 1::U 5 (4*k+11)) Y) := by
    simpa only [Z,U,List.replicate_succ] using h2
  have h3' : RR (boundary 4 true (S 1::S 1::S 1::U 5 (4*k+11)) Y) (boundary 4 true (S 1::U 5 (4*k+10)) (w15 (false::true::true::W ++ tr15 (Raw14042AWord.ac s)) ++ aw (Raw14042DMixed.an s))) := by
    simpa only [Y,U,List.replicate_succ] using h3
  have h4' : RR (boundary 4 true (S 1::U 5 (4*k+10)) (w15 (false::true::true::W ++ tr15 (Raw14042AWord.ac s)) ++ aw (Raw14042DMixed.an s)))
      (ER [S 1] (U 1 (4*k+11) ++ S 5::S 5::(U 1 (2*k+3) ++ S 5::(Raw14042Bank.T (k+2) ++ [S 1,S 1,S 2,S 1])))) := by
    have h := h4
    rw [htail] at h
    have he : List.replicate (4*k+10) false ++ (false::true::true::W ++ tr15 (Raw14042AWord.ac s)) ++ tr15 (Raw14042DMixed.turn (4*k+10) (Raw14042DMixed.an s)).1 =
        List.replicate (4*k+11) false ++ true::true::(List.replicate (2*k+3) false ++ true::tr15 (k+2)) := by
      simp only [W,List.cons_append,List.append_assoc,← tr15_add,← Nat.add_assoc,hcount]
      rw [show List.replicate (4*k+11) false = List.replicate (4*k+10) false ++ [false] by rw [List.replicate_succ']]
      simp only [List.append_assoc,List.singleton_append]
    rw [he] at h
    simpa only [ER,List.append_nil,w15_append,w15_one,w15_tr,ta_eq,w15,ite_true,Raw140ERSuffix.tailWord,List.cons_append,List.append_assoc] using h
  have h5 := evenWordExit (2*k+5) (k+1) (k+1)
  have h5' : RR (ER [S 1] (U 1 (4*k+11) ++ S 5::S 5::(U 1 (2*k+3) ++ S 5::(Raw14042Bank.T (k+2) ++ [S 1,S 1,S 2,S 1]))))
      (A (12*k+44) (Raw14042Bank.T (k+1) ++ [S 1,S 1])) := by
    simpa only [show 2*(2*k+5)+1=4*k+11 by omega,show 2*(k+1)+1=2*k+3 by omega,show 4*(2*k+5)+4*(k+1)+20=12*k+44 by omega] using h5
  have h := Reach.trans (Reach.trans (Reach.trans (Reach.trans h01 h2') h3') h4') h5'
  simpa only [Z,Y,W,w15_append,w15_one,w15_tr,w15,ite_true,List.cons_append,List.append_assoc] using h

#print axioms turn_balance
#print axioms cEvenExit
end Raw14042MixedExitEvenC
