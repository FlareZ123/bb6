import PositiveZFirstCycleBridges
import Q4Suffix
import Lean.Elab.Tactic.Omega

/-!
# Source composition for the positive-z first q4-cycle prefix P(z)

This module composes the fixed 22-step checkpoint bridge, the state-4
unary scan, the two-zero setup, the state-1 three-one block scan, and the
fixed 29-step q4 tail. The resulting theorem is an original infinite-tape
run theorem with an exact framed endpoint.

The hypotheses are the exact right-stream conditions at q4 checkpoint 1:
- the eight-cell local bridge window;
- a run of m ones;
- two separator zeroes;
- n consecutive three-one blocks;
- five zeroes after those blocks.

For the positive-z specialization, m=3*z+5 and n=2^z. The theorem does
not yet identify its final frame pointwise with the arbitrary-left S0
normal form; that is a separate list/tape identity obligation. This file
is a source draft and has NOT passed local Lean compilation.
-/

namespace BB6Coverage.Agent48PositiveZFirstCyclePrefix

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent48PositiveZFirstCycle

/-- The 22-step frame does not change any cell at or to the right of h+4. -/
private theorem firstCyclePrefix22_preserves_after
    (T : Int → Bool) (h y : Int) (hy : h+4 ≤ y) :
    (frameAt T h firstCyclePrefix22Inside firstCyclePrefix22End).tape y = T y := by
  rw [frameAt_tape]
  have hnot : firstCyclePrefix22Inside (y-h) = false := by
    simp [firstCyclePrefix22Inside]
    omega
  simp [frameAt_tape,hnot]

/-- The two-zero setup leaves every cell at or beyond its next head unchanged. -/
private theorem afterFirstCycleTwoZero_preserves_after
    (T : Int → Bool) (h y : Int) (hy : h+2 ≤ y) :
    afterFirstCycleTwoZero T h y = T y := by
  have hne0 : y ≠ h := by omega
  have hne1 : y ≠ h+1 := by omega
  simp [afterFirstCycleTwoZero,hne0,hne1]

/-- Compose all five exact source phases of P. The final frame is the
29-step q4 tail applied after the repeated state-1 111-to-001 scan. -/
theorem firstCyclePrefix_from_checkpoint
    (m n : Nat) (T : Int → Bool) (h : Int)
    (hinput22 :
      T (h-4) = false ∧
      T (h-3) = false ∧
      T (h-2) = true ∧
      T (h-1) = true ∧
      T h = false ∧
      T (h+1) = false ∧
      T (h+2) = false ∧
      T (h+3) = false)
    (hfirst : linearRightOnes T (h+4) m)
    (hsep0 : T (h+4+(m:Int)) = false)
    (hsep1 : T (h+4+(m:Int)+1) = false)
    (hblocks : d1BlocksOn T (h+4+(m:Int)+2) n)
    (hzeros : ∀ i : Nat, i≤4 →
      T (h+4+(m:Int)+2+3*(n:Int)+(i:Int)) = false)
    (hn : 2≤n) :
    let T1 := (frameAt T h
      firstCyclePrefix22Inside firstCyclePrefix22End).tape
    let h1 : Int := h+4+(m:Int)
    let T2 := afterFirstCycleTwoZero T1 h1
    let h2 : Int := h1+2
    let T3 : Int → Bool := d0Sweep n T2 h2
    let g : Int := h2+3*(n:Int)
    run tm2 (22+m+2+3*n+29) ⟨4,h,T⟩ =
      some (frameAt T3 g q4TailInside q4TailEnd) := by
  let T1 : Int → Bool :=
    (frameAt T h firstCyclePrefix22Inside firstCyclePrefix22End).tape
  let h1 : Int := h+4+(m:Int)
  let T2 : Int → Bool := afterFirstCycleTwoZero T1 h1
  let h2 : Int := h1+2
  let T3 : Int → Bool := d0Sweep n T2 h2
  let g : Int := h2+3*(n:Int)

  have h22 := firstCyclePrefix22_at T h hinput22
  have hframe :
      frameAt T h firstCyclePrefix22Inside firstCyclePrefix22End =
        ⟨4,h+4,T1⟩ := by
    apply config_ext
    · simp [frameAt_state,firstCyclePrefix22End]
    · simp [frameAt_head,firstCyclePrefix22End] <;> omega
    · rfl
  have h22run :
      run tm2 22 ⟨4,h,T⟩ = some ⟨4,h+4,T1⟩ := by
    simpa [hframe] using h22

  have hEones : linearRightOnes T1 (h+4) m := by
    intro i hi
    have hp := firstCyclePrefix22_preserves_after T h
      (h+4+(i:Int)) (by omega)
    have hval : T (h+4+(i:Int)) = true := hfirst i hi
    simpa [T1] using hp.trans hval
  have hErun :
      run tm2 m ⟨4,h+4,T1⟩ = some ⟨4,h1,T1⟩ := by
    simpa [h1] using E_scan T1 (h+4) m hEones

  have hsep0' : T1 h1 = false := by
    have hp := firstCyclePrefix22_preserves_after T h h1 (by dsimp [h1]; omega)
    have hval : T h1 = false := by simpa [h1] using hsep0
    simpa [T1] using hp.trans hval
  have hsep1' : T1 (h1+1) = false := by
    have hp := firstCyclePrefix22_preserves_after T h (h1+1)
      (by dsimp [h1]; omega)
    have hval : T (h1+1) = false := by
      simpa [h1,Int.add_assoc] using hsep1
    simpa [T1] using hp.trans hval
  have hsetup :
      run tm2 2 ⟨4,h1,T1⟩ = some ⟨1,h2,T2⟩ := by
    simpa [h2,T2] using firstCycleTwoZeroSetup T1 h1 hsep0' hsep1'

  have hblocks2 : d1BlocksOn T2 h2 n := by
    intro i hi
    obtain ⟨ha,hb,hc⟩ := hblocks i hi
    have hp2a :
        T2 (h2+3*(i:Int)) = T1 (h2+3*(i:Int)) := by
      change afterFirstCycleTwoZero T1 h1 (h2+3*(i:Int)) = _
      apply afterFirstCycleTwoZero_preserves_after
      dsimp [h2]
      omega
    have hp1a :
        T1 (h2+3*(i:Int)) = T (h2+3*(i:Int)) := by
      change (frameAt T h firstCyclePrefix22Inside firstCyclePrefix22End).tape _ = _
      apply firstCyclePrefix22_preserves_after
      dsimp [h2,h1]
      omega
    have hp2b :
        T2 (h2+3*(i:Int)+1) = T1 (h2+3*(i:Int)+1) := by
      change afterFirstCycleTwoZero T1 h1 (h2+3*(i:Int)+1) = _
      apply afterFirstCycleTwoZero_preserves_after
      dsimp [h2]
      omega
    have hp1b :
        T1 (h2+3*(i:Int)+1) = T (h2+3*(i:Int)+1) := by
      change (frameAt T h firstCyclePrefix22Inside firstCyclePrefix22End).tape _ = _
      apply firstCyclePrefix22_preserves_after
      dsimp [h2,h1]
      omega
    have hp2c :
        T2 (h2+3*(i:Int)+2) = T1 (h2+3*(i:Int)+2) := by
      change afterFirstCycleTwoZero T1 h1 (h2+3*(i:Int)+2) = _
      apply afterFirstCycleTwoZero_preserves_after
      dsimp [h2]
      omega
    have hp1c :
        T1 (h2+3*(i:Int)+2) = T (h2+3*(i:Int)+2) := by
      change (frameAt T h firstCyclePrefix22Inside firstCyclePrefix22End).tape _ = _
      apply firstCyclePrefix22_preserves_after
      dsimp [h2,h1]
      omega
    exact ⟨hp2a.trans (hp1a.trans ha),
      hp2b.trans (hp1b.trans hb),
      hp2c.trans (hp1c.trans hc)⟩

  have hscan :
      run tm2 (3*n) ⟨1,h2,T2⟩ = some ⟨1,g,T3⟩ := by
    simpa [g,T3] using state1_d1_blocks_right n T2 h2 hblocks2

  have htail : q4TailInput T3 g := by
    have hlast : n-1<n := by omega
    have hprev : n-2<n := by omega
    obtain ⟨hl0,hl1,hl2⟩ := d0Sweep_block n T2 h2 (n-1) hlast
    obtain ⟨hp0,hp1,hp2⟩ := d0Sweep_block n T2 h2 (n-2) hprev
    refine ⟨?_,?_,?_,?_,?_⟩
    · have heq : h2+3*((n-2:Int))+2 = g-4 := by dsimp [g]; omega
      change d0Sweep n T2 h2 (g-4) = true
      rw [← heq]
      have hc : ((n-2:Nat):Int) = (n:Int)-2 := by omega
      simpa only [hc] using hp2
    · have heq : h2+3*((n-1:Int)) = g-3 := by dsimp [g]; omega
      change d0Sweep n T2 h2 (g-3) = false
      rw [← heq]
      have hc : ((n-1:Nat):Int) = (n:Int)-1 := by omega
      simpa only [hc] using hl0
    · have heq : h2+3*((n-1:Int))+1 = g-2 := by dsimp [g]; omega
      change d0Sweep n T2 h2 (g-2) = false
      rw [← heq]
      have hc : ((n-1:Nat):Int) = (n:Int)-1 := by omega
      simpa only [hc] using hl1
    · have heq : h2+3*((n-1:Int))+2 = g-1 := by dsimp [g]; omega
      change d0Sweep n T2 h2 (g-1) = true
      rw [← heq]
      have hc : ((n-1:Nat):Int) = (n:Int)-1 := by omega
      simpa only [hc] using hl2
    · intro i hi
      have hsw :
          d0Sweep n T2 h2 (g+(i:Int)) = T2 (g+(i:Int)) :=
        d0Sweep_after n T2 h2 (g+(i:Int)) (by dsimp [g]; omega)
      have htwo :
          T2 (g+(i:Int)) = T1 (g+(i:Int)) := by
        change afterFirstCycleTwoZero T1 h1 (g+(i:Int)) = _
        apply afterFirstCycleTwoZero_preserves_after
        dsimp [g,h2]
        omega
      have hframe :
          T1 (g+(i:Int)) = T (g+(i:Int)) := by
        change (frameAt T h firstCyclePrefix22Inside firstCyclePrefix22End).tape _ = _
        apply firstCyclePrefix22_preserves_after
        dsimp [g,h2,h1]
        omega
      change d0Sweep n T2 h2 (g+(i:Int)) = false
      rw [hsw,htwo,hframe]
      simpa [g,h2,h1] using hzeros i hi

  have htailrun := q4Tail_at T3 g htail
  have hpart3 :
      run tm2 (3*n+29) ⟨1,h2,T2⟩ =
        some (frameAt T3 g q4TailInside q4TailEnd) := by
    rw [run_append,hscan]
    simp only [Option.bind_some]
    exact htailrun
  have hpart2 :
      run tm2 (2+3*n+29) ⟨4,h1,T1⟩ =
        some (frameAt T3 g q4TailInside q4TailEnd) := by
    have heq : 2+3*n+29 = 2+(3*n+29) := by omega
    rw [heq,run_append,hsetup]
    simp only [Option.bind_some]
    exact hpart3
  have hfirstPart :
      run tm2 (22+m) ⟨4,h,T⟩ = some ⟨4,h1,T1⟩ := by
    rw [run_append,h22run]
    simp only [Option.bind_some]
    exact hErun
  have htotal : 22+m+2+3*n+29 = (22+m)+(2+3*n+29) := by omega
  rw [htotal,run_append,hfirstPart]
  simp only [Option.bind_some]
  exact hpart2

/-- The prefix cost for the first positive-z q4 cycle. -/
theorem firstCyclePrefix_cost (z : Nat) :
    22+(3*z+5)+2+3*(2^z)+29 = 3*2^z+3*z+58 := by
  omega

#print axioms firstCyclePrefix22_preserves_after
#print axioms afterFirstCycleTwoZero_preserves_after
#print axioms firstCyclePrefix_from_checkpoint
#print axioms firstCyclePrefix_cost

end BB6Coverage.Agent48PositiveZFirstCyclePrefix
