import Leaf2265MacroRounds

namespace BB6.Agent3Leaf2265
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
Source-proved counted section moves for the remaining arbitrarily large
positive unary runs. Together with one, one0010 and terminal3, these
lemmas provide the branch grammar needed for a finite (but astronomical
primitive-time) blank-root trace certificate.
-/

theorem stripG (k j : Nat) (r : Ray) :
    Runs (4*(k+1)+2)
      (S k (cons false (rep G (j+1) r)))
      (S (k+2) (pre [false,false,false] (rep G j r))) := by
  have he : S k (cons false (rep G (j+1) r)) =
      S (k+1) (cons true (pre [false,false] (rep G j r))) := by
    change S k (pre P (cons true (pre [false,false] (rep G j r)))) = _
    rw [S_push]
  rw [he]
  exact one (k+1) (pre [false,false] (rep G j r))

theorem oneHighRound (k j : Nat) (r : Ray) :
    Runs ((4*k+10+10*(j+1))+(4*((k+1)+1)+2))
      (S k (pre [false,false] (rep O (4*(j+1)+1) (cons false r))))
      (S (k+3) (pre [false,false,false]
         (rep G j (pre [true,true,true] r)))) := by
  exact chain (ret1 k (j+1) r) (stripG (k+1) j (pre [true,true,true] r))

theorem fourOddRound (t j : Nat) (r : Ray) :
    Runs ((4*((2*t)+1)+13+10*(j+1))+(6+30*t*t+32*t))
      (S ((2*t)+1) (pre [false,false]
         (rep O (4*(j+1)) (cons false r))))
      (S (2+5*t) (pre [false,false,false,true,false,false,false]
         (rep G j (pre [true,true,true] r)))) := by
  exact chain (ret4 (2*t) j r)
    (drain t 0 (pre [false,false,true,false,false,false]
       (rep G j (pre [true,true,true] r))))

theorem fourEvenRound (t j : Nat) (r : Ray) :
    Runs ((4*((2*t+1)+1)+13+10*(j+1))+
          (6+30*t*t+32*t+(8*(2+5*t)+20)))
      (S ((2*t+1)+1) (pre [false,false]
         (rep O (4*(j+1)) (cons false r))))
      (S (2+5*t+5) (pre [false,false,false]
         (rep G j (pre [true,true,true] r)))) := by
  have h := chain (ret4 (2*t+1) j r)
    (drainOdd t (pre [false,true,false,false,false]
       (rep G j (pre [true,true,true] r))))
  have he : S (2+5*t+4) (pre [false,true,false,false,false]
      (rep G j (pre [true,true,true] r))) =
      S (2+5*t+5) (pre [false,false,false]
         (rep G j (pre [true,true,true] r))) := by
    change S (2+5*t+4) (pre P (pre [false,false,false]
      (rep G j (pre [true,true,true] r)))) = _
    rw [S_push]
  rw [he] at h
  exact h

theorem twoOddHighRound (t j : Nat) (r : Ray) :
    Runs (((4*(2*t+1)+13+10*(j+1))+
           (6+30*t*t+32*t+(8*(2+5*t)+20)))+
           (4*((2+5*t+4)+1)+2))
      (S (2*t+1) (pre [false,false]
         (rep O (4*(j+1)+2) (cons false r))))
      (S (2+5*t+6) (pre [false,false,false]
         (rep G j (pre [true,true,true] r)))) := by
  have h := chain (ret2 (2*t+1) (j+1) r)
    (drainOdd t (cons false
       (rep G (j+1) (pre [true,true,true] r))))
  exact chain h (stripG (2+5*t+4) j (pre [true,true,true] r))

#print axioms stripG
#print axioms oneHighRound
#print axioms fourOddRound
#print axioms fourEvenRound
#print axioms twoOddHighRound
end BB6.Agent3Leaf2265
