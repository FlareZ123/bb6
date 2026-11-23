import PositiveZSecondCycleBridge
import PositiveZFirstCycleBridges
import Q4Suffix
import Lean.Elab.Tactic.Omega

/-!
# Source composition for the second q4-checkpoint prefix

The 34-step finite bridge is followed by exactly the same three large
right-stream phases as the first checkpoint prefix: E_scan, two-zero
setup, state-1 111-to-001 block scan, and q4Tail. This theorem packages
that composition under explicit local/right-stream hypotheses.

For the q4 checkpoint-2 stream observed in the repository, the intended
parameters are m=3*2^z+3*z+7 and n=2^(2^z-1). The theorem is an
intermediate source draft; it has NOT passed local Lean compilation.
-/

namespace BB6Coverage.Agent48PositiveZSecondCyclePrefix

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent48PositiveZSecondCycle
open BB6Coverage.Agent48PositiveZFirstCycle

/-- The 34-step frame leaves all cells at or to the right of h+4 unchanged. -/
private theorem secondCyclePrefix34_preserves_after
    (T : Int → Bool) (h y : Int) (hy : h+4 ≤ y) :
    (frameAt T h secondCyclePrefix34Inside secondCyclePrefix34End).tape y = T y := by
  rw [frameAt_tape]
  have hnot : secondCyclePrefix34Inside (y-h) = false := by
    simp [secondCyclePrefix34Inside]
    omega
  simp [frameAt_tape,hnot]

/-- The two-zero setup leaves every cell at or beyond its next head unchanged. -/
private theorem afterSecondCycleTwoZero_preserves_after
    (T : Int → Bool) (h y : Int) (hy : h+2 ≤ y) :
    afterFirstCycleTwoZero T h y = T y := by
  have hne0 : y ≠ h := by omega
  have hne1 : y ≠ h+1 := by omega
  simp [afterFirstCycleTwoZero,hne0,hne1]

/-- Exact second-checkpoint prefix composition, ending at the q4Tail frame. -/
theorem secondCyclePrefix_from_checkpoint
    (m n : Nat) (T : Int → Bool) (h : Int)
    (hinput34 :
      T (h-7) = false ∧
      T (h-6) = false ∧
      T (h-5) = true ∧
      T (h-4) = true ∧
      T (h-3) = true ∧
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
      secondCyclePrefix34Inside secondCyclePrefix34End).tape
    let h1 : Int := h+4+(m:Int)
    let T2 := afterFirstCycleTwoZero T1 h1
    let h2 : Int := h1+2
    let T3 : Int → Bool := d0Sweep n T2 h2
    let g : Int := h2+3*(n:Int)
    run tm2 (34+m+2+3*n+29) ⟨4,h,T⟩ =
      some (frameAt T3 g q4TailInside q4TailEnd) := by
  let T1 : Int → Bool :=
    (frameAt T h secondCyclePrefix34Inside secondCyclePrefix34End).tape
  let h1 : Int := h+4+(m:Int)
  let T2 : Int → Bool := afterFirstCycleTwoZero T1 h1
  let h2 : Int := h1+2
  let T3 : Int → Bool := d0Sweep n T2 h2
  let g : Int := h2+3*(n:Int)

  have h34 := secondCyclePrefix34_at T h hinput34
  have hframe :
      frameAt T h secondCyclePrefix34Inside secondCyclePrefix34End =
        ⟨4,h+4,T1⟩ := by
    apply config_ext
    · simp [frameAt_state,secondCyclePrefix34End]
    · simp [frameAt_head,secondCyclePrefix34End] <;> omega
    · rfl
  have h34run :
      run tm2 34 ⟨4,h,T⟩ = some ⟨4,h+4,T1⟩ := by
    simpa [hframe] using h34

  have hEones : linearRightOnes T1 (h+4) m := by
    intro i hi
    have hp := secondCyclePrefix34_preserves_after T h
      (h+4+(i:Int)) (by omega)
    change T1 (h+4+(i:Int)) = true
    rw [hp]
    exact hfirst i hi
  have hErun :
      run tm2 m ⟨4,h+4,T1⟩ = some ⟨4,h1,T1⟩ := by
    simpa [h1] using E_scan T1 (h+4) m hEones

  have hsep0' : T1 h1 = false := by
    have hp := secondCyclePrefix34_preserves_after T h h1 (by dsimp [h1]; omega)
    change T1 h1 = false
    rw [hp]
    simpa [h1] using hsep0
  have hsep1' : T1 (h1+1) = false := by
    have hp := secondCyclePrefix34_preserves_after T h (h1+1)
      (by dsimp [h1]; omega)
    change T1 (h1+1) = false
    rw [hp]
    simpa [h1,Int.add_assoc] using hsep1
  have hsetup :
      run tm2 2 ⟨4,h1,T1⟩ = some ⟨1,h2,T2⟩ := by
    simpa [h2,T2] using firstCycleTwoZeroSetup T1 h1 hsep0' hsep1'

  have hblocks2 : d1BlocksOn T2 h2 n := by
    intro i hi
    obtain ⟨ha,hb,hc⟩ := hblocks i hi
    have hp2a :
        T2 (h2+3*(i:Int)) = T1 (h2+3*(i:Int)) := by
      change afterFirstCycleTwoZero T1 h1 (h2+3*(i:Int)) = _
      apply afterSecondCycleTwoZero_preserves_after
      dsimp [h2]
      omega
    have hp1a :
        T1 (h2+3*(i:Int)) = T (h2+3*(i:Int)) := by
      change (frameAt T h secondCyclePrefix34Inside secondCyclePrefix34End).tape _ = _
      apply secondCyclePrefix34_preserves_after
      dsimp [h2,h1]
      omega
    have hp2b :
        T2 (h2+3*(i:Int)+1) = T1 (h2+3*(i:Int)+1) := by
      change afterFirstCycleTwoZero T1 h1 (h2+3*(i:Int)+1) = _
      apply afterSecondCycleTwoZero_preserves_after
      dsimp [h2]
      omega
    have hp1b :
        T1 (h2+3*(i:Int)+1) = T (h2+3*(i:Int)+1) := by
      change (frameAt T h secondCyclePrefix34Inside secondCyclePrefix34End).tape _ = _
      apply secondCyclePrefix34_preserves_after
      dsimp [h2,h1]
      omega
    have hp2c :
        T2 (h2+3*(i:Int)+2) = T1 (h2+3*(i:Int)+2) := by
      change afterFirstCycleTwoZero T1 h1 (h2+3*(i:Int)+2) = _
      apply afterSecondCycleTwoZero_preserves_after
      dsimp [h2]
      omega
    have hp1c :
        T1 (h2+3*(i:Int)+2) = T (h2+3*(i:Int)+2) := by
      change (frameAt T h secondCyclePrefix34Inside secondCyclePrefix34End).tape _ = _
      apply secondCyclePrefix34_preserves_after
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
      exact hp2
    · have heq : h2+3*((n-1:Int)) = g-3 := by dsimp [g]; omega
      change d0Sweep n T2 h2 (g-3) = false
      rw [← heq]
      exact hl0
    · have heq : h2+3*((n-1:Int))+1 = g-2 := by dsimp [g]; omega
      change d0Sweep n T2 h2 (g-2) = false
      rw [← heq]
      exact hl1
    · have heq : h2+3*((n-1:Int))+2 = g-1 := by dsimp [g]; omega
      change d0Sweep n T2 h2 (g-1) = true
      rw [← heq]
      exact hl2
    · intro i hi
      have hsw :
          d0Sweep n T2 h2 (g+(i:Int)) = T2 (g+(i:Int)) :=
        d0Sweep_after n T2 h2 (g+(i:Int)) (by dsimp [g]; omega)
      have htwo :
          T2 (g+(i:Int)) = T1 (g+(i:Int)) := by
        change afterFirstCycleTwoZero T1 h1 (g+(i:Int)) = _
        apply afterSecondCycleTwoZero_preserves_after
        dsimp [g,h2]
        omega
      have hframe :
          T1 (g+(i:Int)) = T (g+(i:Int)) := by
        change (frameAt T h secondCyclePrefix34Inside secondCyclePrefix34End).tape _ = _
        apply secondCyclePrefix34_preserves_after
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
      run tm2 (34+m) ⟨4,h,T⟩ = some ⟨4,h1,T1⟩ := by
    rw [run_append,h34run]
    simp only [Option.bind_some]
    exact hErun
  have htotal : 34+m+2+3*n+29 = (34+m)+(2+3*n+29) := by omega
  rw [htotal,run_append,hfirstPart]
  simp only [Option.bind_some]
  exact hpart2

/-- Cost of the second q4-checkpoint prefix with m=3*2^z+3*z+7 and
n=2^(2^z-1). -/
theorem secondCyclePrefix_cost (z : Nat) :
    34+(3*2^z+3*z+7)+2+3*(2^(2^z-1))+29 =
      3*(2^(2^z-1))+3*2^z+3*z+72 := by
  omega

#print axioms secondCyclePrefix34_preserves_after
#print axioms afterSecondCycleTwoZero_preserves_after
#print axioms secondCyclePrefix_from_checkpoint
#print axioms secondCyclePrefix_cost

end BB6Coverage.Agent48PositiveZSecondCyclePrefix
