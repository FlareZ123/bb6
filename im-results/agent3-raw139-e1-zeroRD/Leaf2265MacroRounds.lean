import Leaf2265Compress

namespace BB6.Agent3Leaf2265
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
Four counted unbounded source-level normalizations. These discharge the
m=0 odd/even and m=2 even/odd (r=0) branches of the finite-section
calculation without enumerating tape bits or primitive moves.
All input/output rays are arbitrary: no blank-tail hypothesis is used.
-/

theorem zeroOddRound (t : Nat) (r : Ray) :
    Runs ((4*(2*t+1)+13)+(6+30*t*t+32*t))
      (S (2*t+1) (pre [false,false,false] r))
      (S (2+5*t) (pre [false,false,false,true,false,true] r)) := by
  exact chain (ret0 (2*t) r)
    (drain t 0 (pre [false,false,true,false,true] r))

theorem zeroEvenRound (t : Nat) (r : Ray) :
    Runs ((4*((2*t+1)+1)+13)+
          (6+30*t*t+32*t+(8*(2+5*t)+20)))
      (S ((2*t+1)+1) (pre [false,false,false] r))
      (S (2+5*t+6) r) := by
  have h := chain (ret0 (2*t+1) r)
    (drainOdd t (pre [false,true,false,true] r))
  have he : S (2+5*t+4) (pre [false,true,false,true] r) =
      S (2+5*t+6) r := by
    change S (2+5*t+4) (pre P (pre P r)) = _
    rw [S_push, S_push]
  rw [he] at h
  exact h

theorem twoEvenRound (t j : Nat) (r : Ray) :
    Runs ((4*(2*t)+13+10*j)+(6+30*t*t+32*t))
      (S (2*t) (pre [false,false] (rep O (4*j+2) (cons false r))))
      (S (2+5*t) (pre [false,false,false]
        (rep G j (pre [true,true,true] r)))) := by
  exact chain (ret2 (2*t) j r)
    (drain t 0 (pre [false,false] (rep G j (pre [true,true,true] r))))

theorem twoOddZeroRound (t : Nat) (r : Ray) :
    Runs (((4*(2*t+1)+13+10*0)+
           (6+30*t*t+32*t+(8*(2+5*t)+20)))+
           (4*(2+5*t+5)+2))
      (S (2*t+1) (pre [false,false]
        (rep O 2 (cons false r))))
      (S (2+5*t+7) r) := by
  have h := chain (ret2 (2*t+1) 0 r)
    (drainOdd t (pre [false,true,true,true] r))
  have he : S (2+5*t+4) (pre [false,true,true,true] r) =
      S (2+5*t+5) (cons true (cons true r)) := by
    change S (2+5*t+4) (pre P (cons true (cons true r))) = _
    rw [S_push]
  rw [he] at h
  have g := chain h (one (2+5*t+5) (cons true r))
  have hf : S ((2+5*t+5)+1) (cons false (cons true r)) =
      S (2+5*t+7) r := by
    change S ((2+5*t+5)+1) (pre P r) = _
    rw [S_push]
  rw [hf] at g
  exact g

#print axioms zeroOddRound
#print axioms zeroEvenRound
#print axioms twoEvenRound
#print axioms twoOddZeroRound
end BB6.Agent3Leaf2265
