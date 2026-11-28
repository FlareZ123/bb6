import D100FiniteF1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7D100FiniteF1
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay

theorem entry : run0 table 7 ⟨0,[],[]⟩ = some (A 1 [false, false, false]) := by rfl

theorem e00 : run0 table 14 (A 1 [false, false, false]) = some (A 2 [false, false, false, false]) := by
  have h := epoch 0 1 2 8 [false, false, false] [false, false, false, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e01 : run0 table 16 (A 2 [false, false, false, false]) = some (A 4 [false, true, false, false]) := by
  have h := epoch 0 2 4 8 [false, false, false, false] [false, true, false, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e02 : run0 table 43 (A 4 [false, true, false, false]) = some (A 8 [false, false, false]) := by
  have h := epoch 1 1 4 12 [false, true, false, false] [false, false, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e03 : run0 table 74 (A 8 [false, false, false]) = some (A 12 [false, true, false]) := by
  have h := epoch 2 2 4 8 [false, false, false] [false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e04 : run0 table 172 (A 12 [false, true, false]) = some (A 16 [false, false, false, true, false]) := by
  have h := epoch 4 0 0 4 [false, true, false] [false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e05 : run0 table 249 (A 16 [false, false, false, true, false]) = some (A 22 [false, false, false, false, true, false]) := by
  have h := epoch 5 1 2 8 [false, false, false, true, false] [false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e06 : run0 table 427 (A 22 [false, false, false, false, true, false]) = some (A 30 [false, false, false, false, false, true, false]) := by
  have h := epoch 7 1 2 8 [false, false, false, false, true, false] [false, false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e07 : run0 table 778 (A 30 [false, false, false, false, false, true, false]) = some (A 40 [false, false, false, false, false, false, false, true, false]) := by
  have h := epoch 10 0 0 4 [false, false, false, false, false, true, false] [false, false, false, false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e08 : run0 table 1249 (A 40 [false, false, false, false, false, false, false, true, false]) = some (A 54 [false, false, false, false, false, false, false, false, true, false]) := by
  have h := epoch 13 1 2 8 [false, false, false, false, false, false, false, true, false] [false, false, false, false, false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e09 : run0 table 2258 (A 54 [false, false, false, false, false, false, false, false, true, false]) = some (A 72 [false, false, false, false, false, false, false, false, false, false, true, false]) := by
  have h := epoch 18 0 0 4 [false, false, false, false, false, false, false, false, true, false] [false, false, false, false, false, false, false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e10 : run0 table 3872 (A 72 [false, false, false, false, false, false, false, false, false, false, true, false]) = some (A 96 [false, false, false, false, false, false, false, false, false, false, false, false, true, false]) := by
  have h := epoch 24 0 0 4 [false, false, false, false, false, false, false, false, false, false, true, false] [false, false, false, false, false, false, false, false, false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e11 : run0 table 6696 (A 96 [false, false, false, false, false, false, false, false, false, false, false, false, true, false]) = some (A 128 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) := by
  have h := epoch 32 0 0 4 [false, false, false, false, false, false, false, false, false, false, false, false, true, false] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e12 : run0 table 11314 (A 128 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) = some (A 172 [false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) := by
  have h := epoch 42 2 4 8 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] [false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e13 : run0 table 20483 (A 172 [false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) = some (A 232 [false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) := by
  have h := epoch 57 1 4 12 [false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false] [false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e14 : run0 table 36897 (A 232 [false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) = some (A 310 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) := by
  have h := epoch 77 1 2 8 [false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e15 : run0 table 65419 (A 310 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) = some (A 414 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) := by
  have h := epoch 103 1 2 8 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e16 : run0 table 116618 (A 414 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) = some (A 552 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) := by
  have h := epoch 138 0 0 4 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e17 : run0 table 206272 (A 552 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) = some (A 736 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) := by
  have h := epoch 184 0 0 4 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e18 : run0 table 364329 (A 736 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) = some (A 982 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) := by
  have h := epoch 245 1 2 8 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e19 : run0 table 647147 (A 982 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) = some (A 1310 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) := by
  have h := epoch 327 1 2 8 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem e20 : run0 table 1148004 (A 1310 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) = some (A 1748 [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) := by
  have h := epoch 436 2 4 8 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false] (by decide) (by intro L; rfl)
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul] using h

theorem finish (j : Nat) (R : List Bool) :
    run0 table (scanCost j+6) (A (3*j+2) (false::true::R)) =
      some ⟨5,U (4*j+6),R⟩ := by
  have h := epoch_scan j 2 (false::true::R) (by omega)
  have g : ∀ L R, run0 table 6 ⟨2,false::true::L,true::true::false::true::R⟩ =
      some ⟨5,U 6++L,R⟩ := by intro L R; rfl
  have H := join0 h (g (U (4*j)) R)
  rw [← U_add,Nat.add_comm 6 (4*j)] at H
  exact H

def final : Z0 := ⟨5,U 2334,[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]⟩

theorem e21 : run0 table 2039920 (A 1748 [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]) = some final := by
  have h := finish 582 [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]
  simpa only [scanCost,loopCost,Nat.reduceAdd,Nat.reduceMul,final] using h

theorem reached : run0 table 4672258 ⟨0,[],[]⟩ = some final := by
  have h00 := join0 entry e00
  have h01 := join0 h00 e01
  have h02 := join0 h01 e02
  have h03 := join0 h02 e03
  have h04 := join0 h03 e04
  have h05 := join0 h04 e05
  have h06 := join0 h05 e06
  have h07 := join0 h06 e07
  have h08 := join0 h07 e08
  have h09 := join0 h08 e09
  have h10 := join0 h09 e10
  have h11 := join0 h10 e11
  have h12 := join0 h11 e12
  have h13 := join0 h12 e13
  have h14 := join0 h13 e14
  have h15 := join0 h14 e15
  have h16 := join0 h15 e16
  have h17 := join0 h16 e17
  have h18 := join0 h17 e18
  have h19 := join0 h18 e19
  have h20 := join0 h19 e20
  have h21 := join0 h20 e21
  simpa only [Nat.reduceAdd] using h21

theorem rest : ∀ s : Fin 6 × Bool, s ≠ (final.q, final.l.headD false) → ∃ a b q, table s = some (some ⟨a,b,q⟩) := by
  intro ⟨q,b⟩ h
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first | exact ⟨_,_,_,rfl⟩ | exact False.elim (h rfl)

theorem bound (m : Machine) (hm : compatible table m) : WeightedBound 4672264 m := by
  apply BB6.Agent7Run0LastHole.bound table 4672258 4672264 final reached rfl ?_ (by decide) m hm
  · intro s hs; obtain ⟨a,b,q,h⟩ := rest s hs; exact ⟨⟨a,b,q⟩,h⟩

#print axioms reached
#print axioms bound
end BB6.Agent7D100FiniteF1
