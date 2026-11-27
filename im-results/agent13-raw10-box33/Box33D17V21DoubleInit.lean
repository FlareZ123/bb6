import Box33D17V21Double

namespace BB6.Agent13.Box33D17V21Double
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep cfg ones rep_add)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def Reaches (b : Bool) (c d : Config) : Prop :=
  ∃ t, run b t c = some d

theorem reach (b : Bool) {t : Nat} {c d : Config}
    (h : run b t c = some d) : Reaches b c d := ⟨t,h⟩
theorem trans (b : Bool) {c d e : Config} (h : Reaches b c d) (j : Reaches b d e) :
    Reaches b c e := by
  obtain ⟨n,hn⟩ := h
  obtain ⟨m,hm⟩ := j
  exact reach b (chain b hn hm)

def X (n g k : Nat) : Config :=
  A (ones 11 (zeros 3 (ones (2*n) (zeros g (ones (2*k) z))))) z
def P (g k : Nat) : Config :=
  A (ones 17 (zeros g (ones (2*k) z))) z

theorem advanceX (b : Bool) (n g k : Nat) :
    Reaches b (X n (g+3) k) (X (n+4) g k) := by
  unfold X
  rw [show g+3=3+g by omega,zeros_add 3 g (ones (2*k) z)]
  exact reach b (growthGen b n _)

theorem advanceMany (b : Bool) (j n g k : Nat) :
    Reaches b (X n (g+3*j) k) (X (n+4*j) g k) := by
  induction j generalizing n with
  | zero => exact ⟨0,rfl⟩
  | succ j ih =>
    rw [show g+3*(j+1)=g+3*j+3 by omega,show n+4*(j+1)=n+4+4*j by omega]
    exact trans b (advanceX b n (g+3*j) k) (ih (n+4))

theorem exitTwo (b : Bool) (n k : Nat) :
    Reaches b (X (n+1) 2 (k+1)) (P (2*n) (k+4)) := by
  let u := 2*(n+1)
  let v := 2*(k+1)
  let r := ones 2 (zeros 1 (ones 11 z))
  have h0 := lsweepBlank b 5 (ones 1 (zeros 3 (ones u (zeros 2 (ones v z)))))
  have h1 := chain b h0 (odd b (ones u (zeros 2 (ones v z))) (ones 10 z))
  have h2 := chain b h1 (lsweep b (n+1) (zeros 2 (ones v z)) r)
  have hv : ones v z = ones 2 (ones (2*k) z) := by
    dsimp [v]
    rw [show 2*(k+1)=2+2*k by omega]
    exact ones_add _ _ _
  have ht : run b (6+extra b) (L (zeros 2 (ones v z)) (ones u r)) =
      some (L (ones v z) (zeros 1 (ones 1 (ones u r)))) := by
    rw [hv]
    exact turn2 b _ _
  have h3 := chain b h2 ht
  have h4 := chain b h3 (lsweep b (k+1) z (zeros 1 (ones 1 (ones u r))))
  have h5 := chain b h4 (turnBlank b (ones v (zeros 1 (ones 1 (ones u r)))))
  have h6 := chain b h5 (asweep b v (ones 5 z) (zeros 1 (ones 1 (ones u r))))
  let s := ones 1 (ones v (ones 5 z))
  have h7 := chain b h6 (enterB b (ones v (ones 5 z)) (ones 1 (ones u r)))
  have hr : ones 1 (ones u r) = ones (u+3) (zeros 1 (ones 11 z)) := by
    dsimp only [r]
    rw [←ones_add u 2 _,←ones_add 1 (u+2) _]
    rw [show 1+(u+2)=u+3 by omega]
  rw [hr] at h7
  have h8 := chain b h7 (bsweep b (u+3) s (zeros 1 (ones 11 z)))
  have hz : zeros (u+3) s = zeros 2 (zeros (2*n+3) s) := by
    dsimp only [u]
    rw [show 2*(n+1)+3=2+(2*n+3) by omega]
    exact zeros_add _ _ _
  rw [hz] at h8
  have h9 := chain b h8 (exitB b (zeros (2*n+3) s) (ones 11 z))
  have hz2 : zeros (2*n+3) s = zeros 3 (zeros (2*n) s) := by
    rw [show 2*n+3=3+2*n by omega]
    exact zeros_add _ _ _
  rw [hz2] at h9
  have h10 := chain b h9 (turn3 b (zeros (2*n) s) (ones 12 z))
  have h11 := chain b h10 (asweep b 12 (ones 5 (zeros (2*n) s)) z)
  have hs : s = ones (2*(k+4)) z := by
    dsimp only [s,v]
    rw [←ones_add (2*(k+1)) 5 z,←ones_add 1 (2*(k+1)+5) z]
    rw [show 1+(2*(k+1)+5)=2*(k+4) by omega]
  rw [hs] at h11
  exact reach b h11

theorem odd17 (b : Bool) (l : Stream) :
    Reaches b (A (ones 17 (zeros 6 l)) z) (A (ones 6 (zeros 12 (ones 8 l))) z) := by
  have h0 := lsweepBlank b 8 (ones 1 (zeros 3 (zeros 3 l)))
  have h1 := chain b h0 (odd b (zeros 3 l) (ones 16 z))
  have h2 := chain b h1 (turn3 b l (ones 2 (zeros 1 (ones 17 z))))
  have h3 := chain b h2 (asweep b 2 (ones 5 l) (zeros 1 (ones 17 z)))
  have h4 := chain b h3 (enterB b (ones 7 l) (ones 17 z))
  have h5 := chain b h4 (bsweep b 17 (ones 8 l) z)
  have hx : run b 2 (B (zeros 17 (ones 8 l)) z) =
      some (L (zeros 15 (ones 8 l)) (ones 1 z)) := by
    rw [show zeros 17 (ones 8 l)=zeros 2 (zeros 15 (ones 8 l)) from zeros_add 2 15 _]
    simpa only [zeros_z] using exitB b (zeros 15 (ones 8 l)) z
  have h6 := chain b h5 hx
  have h7 := chain b h6 (turn3 b (zeros 12 (ones 8 l)) (ones 1 z))
  exact reach b (chain b h7 (asweep b 1 (ones 5 (zeros 12 (ones 8 l))) z))

theorem odd11 (b : Bool) (l : Stream) :
    Reaches b (A (ones 11 (zeros 6 l)) z) (A (ones 6 (zeros 6 (ones 8 l))) z) := by
  have h0 := lsweepBlank b 5 (ones 1 (zeros 3 (zeros 3 l)))
  have h1 := chain b h0 (odd b (zeros 3 l) (ones 10 z))
  have h2 := chain b h1 (turn3 b l (ones 2 (zeros 1 (ones 11 z))))
  have h3 := chain b h2 (asweep b 2 (ones 5 l) (zeros 1 (ones 11 z)))
  have h4 := chain b h3 (enterB b (ones 7 l) (ones 11 z))
  have h5 := chain b h4 (bsweep b 11 (ones 8 l) z)
  have hx : run b 2 (B (zeros 11 (ones 8 l)) z) =
      some (L (zeros 9 (ones 8 l)) (ones 1 z)) := by
    rw [show zeros 11 (ones 8 l)=zeros 2 (zeros 9 (ones 8 l)) from zeros_add 2 9 _]
    simpa only [zeros_z] using exitB b (zeros 9 (ones 8 l)) z
  have h6 := chain b h5 hx
  have h7 := chain b h6 (turn3 b (zeros 6 (ones 8 l)) (ones 1 z))
  exact reach b (chain b h7 (asweep b 1 (ones 5 (zeros 6 (ones 8 l))) z))

theorem even6 (b : Bool) (l : Stream) :
    Reaches b (A (ones 6 (zeros 3 l)) z) (A (ones 11 l) z) := by
  have h0 := lsweepBlank b 3 (zeros 3 l)
  have h1 := chain b h0 (turn3 b l (ones 6 z))
  exact reach b (chain b h1 (asweep b 6 (ones 5 l) z))

theorem enterP (b : Bool) (g k : Nat) :
    Reaches b (P (g+6) k) (X 12 g k) := by
  let l := zeros g (ones (2*k) z)
  have hp : P (g+6) k = A (ones 17 (zeros 6 l)) z := by
    unfold P
    dsimp only [l]
    rw [show g+6=6+g by omega,zeros_add 6 g _]
  rw [hp]
  have h0 := odd17 b l
  have h1 := trans b h0 (even6 b (zeros 9 (ones 8 l)))
  have h2 := trans b h1 (odd11 b (zeros 3 (ones 8 l)))
  have h3 := trans b h2 (even6 b (zeros 3 (ones 8 (zeros 3 (ones 8 l)))))
  have h4 := trans b h3 (reach b (growthGen b 4 (ones 8 l)))
  exact h4

#print axioms exitTwo
#print axioms enterP
end BB6.Agent13.Box33D17V21Double
