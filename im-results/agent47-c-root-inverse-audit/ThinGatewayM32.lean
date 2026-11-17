import CSourceBridge32
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47ThinGateway

/-- A state with even first counter and zero middle counter has no incoming
    edge once its third counter is above the exceptional initial region. -/
private theorem no_incoming_even_terminal (K C : Nat)
    (hK : 8 ≤ K) (hKe : K % 2 = 0) (hC : 4 ≤ C)
    (s : Nat × Nat × Nat)
    (h : BB6CLine.nextC s = some (K,0,C+K)) : False := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
      omega
    · rcases k with _|k
      · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
        omega
      · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
        omega
    · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
      omega
  · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
    omega
  · simp [BB6CLine.nextC] at h
  · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
    omega
  · rcases a with _|a
    · dsimp [BB6CLine.nextC] at h
      by_cases he : k % 2 = 0
      · simp only [he, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        omega
      · simp only [he, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        omega
    · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
      omega

private theorem terminal_unreachable (K C : Nat)
    (hK : 8 ≤ K) (hKe : K % 2 = 0) (hC : 4 ≤ C) :
    ¬ BB6CLine.Reach (K,0,C+K) := by
  intro hR
  cases hR with
  | init => omega
  | next s t hs ht =>
      exact no_incoming_even_terminal K C hK hKe hC s ht

/-- All possible predecessors of an interior point of the descending
    high-counter chain.  The only extra parent is the even-a=0 branch at
    middle counter 2. -/
private theorem chain_predecessor (K C r : Nat)
    (hK : 8 ≤ K) (hC : 4 ≤ C) (hr : r ≤ K-2)
    (s : Nat × Nat × Nat)
    (h : BB6CLine.nextC s = some (r,K-r,C+r)) :
    s = (r+1,K-r-1,C+r+1) ∨
      (r=K-2 ∧ K%4=0 ∧ s=(0,(K-4)/2,C+K+1)) := by
  rcases s with ⟨a,k,c⟩
  have hmid : 2 ≤ K-r := by omega
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
      omega
    · rcases k with _|k
      · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
        omega
      · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
        omega
    · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
      omega
  · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
    omega
  · simp [BB6CLine.nextC] at h
  · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
    omega
  · rcases a with _|a
    · dsimp [BB6CLine.nextC] at h
      by_cases he : k % 2 = 0
      · simp only [he, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨ha,hk,hc⟩
        have hrEq : r=K-2 := by omega
        have hK4 : K%4=0 := by omega
        have hkEq : k=(K-4)/2 := by omega
        have hcEq : d+4=C+K+1 := by omega
        right
        refine ⟨hrEq, hK4, ?_⟩
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact hkEq
          · exact hcEq
      · simp only [he, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        omega
    · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨ha,hk,hc⟩
      left
      apply Prod.ext
      · omega
      · apply Prod.ext
        · omega
        · omega

/-- The last high-chain point has either the even-a=0 terminal parent
    (which is unreachable), or the displayed c=0 parent. -/
private theorem last_chain_predecessor (K C : Nat)
    (hK : 8 ≤ K) (hKe : K%2=0) (hC : 4 ≤ C)
    (s : Nat × Nat × Nat)
    (h : BB6CLine.nextC s = some (K-1,1,C+K-1)) :
    s=(K,0,C+K) ∨
      (C%2=0 ∧ s=(K+1,(C+K-2)/2,0)) := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
      omega
    · rcases k with _|k
      · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
        omega
      · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
        omega
    · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨ha,hk,hc⟩
      have hCe : C%2=0 := by omega
      have hkEq : k=(C+K-2)/2 := by omega
      right
      refine ⟨hCe, ?_⟩
      apply Prod.ext
      · omega
      · apply Prod.ext
        · exact hkEq
        · rfl
  · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
    omega
  · simp [BB6CLine.nextC] at h
  · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
    omega
  · rcases a with _|a
    · dsimp [BB6CLine.nextC] at h
      by_cases he : k%2=0
      · simp only [he, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        omega
      · simp only [he, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        omega
    · simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨ha,hk,hc⟩
      left
      apply Prod.ext
      · omega
      · apply Prod.ext
        · omega
        · omega

/-- A blank-reachable state (0,K,C), for even K and C>=4, must have
    either its c=0 parent or its next even-a=0 parent reachable.  The
    terminal state (K,0,C+K) has no incoming edge. -/
private theorem zeroA_reach_parent (K C : Nat)
    (hK : 8 ≤ K) (hKe : K%2=0) (hC : 4 ≤ C)
    (hReach : BB6CLine.Reach (0,K,C)) :
    (C%2=0 ∧ BB6CLine.Reach (K+1,(C+K-2)/2,0)) ∨
      (K%4=0 ∧ BB6CLine.Reach (0,(K-4)/2,C+K+1)) := by
  let R : Prop :=
    (C%2=0 ∧ BB6CLine.Reach (K+1,(C+K-2)/2,0)) ∨
      (K%4=0 ∧ BB6CLine.Reach (0,(K-4)/2,C+K+1))
  have hAll : ∀ s, BB6CLine.Reach s → ∀ r, r≤K-1 →
      s=(r,K-r,C+r) → R := by
    intro s hs
    induction hs with
    | init =>
        intro r hr heq
        have hc : (1:Nat)=C+r := by
          simpa using congrArg (fun x : Nat×Nat×Nat => x.2.2) heq
        omega
    | next p q hp hstep ih =>
        intro r hr heq
        have hstep' : BB6CLine.nextC p = some (r,K-r,C+r) := by
          rw [heq] at hstep
          exact hstep
        by_cases hlast : r=K-1
        · subst r
          rcases last_chain_predecessor K C hK hKe hC p hstep' with hterm | hQ
          · subst p
            exact False.elim (terminal_unreachable K C hK hKe hC hp)
          · rcases hQ with ⟨hCe,hpeq⟩
            subst p
            exact Or.inl ⟨hCe,hp⟩
        · have hr2 : r≤K-2 := by omega
          rcases chain_predecessor K C r hK hC hr2 p hstep' with hchain | hbranch
          · subst p
            have hr' : r+1≤K-1 := by omega
            exact ih (r+1) hr' rfl
          · rcases hbranch with ⟨hrEq,hK4,hpeq⟩
            subst p
            exact Or.inr ⟨hK4,hp⟩
  have hres := hAll (0,K,C) hReach 0 (by omega) rfl
  simpa [R] using hres

private theorem no_parent_15_25 (n : Nat) :
    ¬ BB6CLine.Reach (207+256*n,313+384*n,0) := by
  intro h
  have hs := CCert.reachable_seen (CCert.source_reachable_embeds32 h)
  have hqa : CCert.q (207+256*n)=15 := by
    calc
      CCert.q (207+256*n) = CCert.q 15 :=
        CCert.q_congr_big _ _ (by omega) (by omega) (by omega)
      _ = 15 := by decide
  have hqk : CCert.q (313+384*n)=25 := by
    calc
      CCert.q (313+384*n) = CCert.q 25 :=
        CCert.q_congr_big _ _ (by omega) (by omega) (by omega)
      _ = 25 := by decide
  have hs' : CCert.seen 15 25 0 = true := by
    simpa [hqa,hqk,CCert.q] using hs
  have hnot : CCert.seen 15 25 0 = false := by decide
  rw [hnot] at hs'
  cases hs'

private theorem no_parent_13_38 (n : Nat) :
    ¬ BB6CLine.Reach (173+256*n,262+384*n,0) := by
  intro h
  have hs := CCert.reachable_seen (CCert.source_reachable_embeds32 h)
  have hqa : CCert.q (173+256*n)=13 := by
    calc
      CCert.q (173+256*n) = CCert.q 13 :=
        CCert.q_congr_big _ _ (by omega) (by omega) (by omega)
      _ = 13 := by decide
  have hqk : CCert.q (262+384*n)=38 := by
    calc
      CCert.q (262+384*n) = CCert.q 38 :=
        CCert.q_congr_big _ _ (by omega) (by omega) (by omega)
      _ = 38 := by decide
  have hs' : CCert.seen 13 38 0 = true := by
    simpa [hqa,hqk,CCert.q] using hs
  have hnot : CCert.seen 13 38 0 = false := by decide
  rw [hnot] at hs'
  cases hs'

private theorem no_parent_9_37 (n : Nat) :
    ¬ BB6CLine.Reach (41+64*n,325+480*n,0) := by
  intro h
  have hs := CCert.reachable_seen (CCert.source_reachable_embeds32 h)
  have hqa : CCert.q (41+64*n)=9 := by
    calc
      CCert.q (41+64*n) = CCert.q 9 :=
        CCert.q_congr_big _ _ (by omega) (by omega) (by omega)
      _ = 9 := by decide
  have hqk : CCert.q (325+480*n)=37 := by
    calc
      CCert.q (325+480*n) = CCert.q 37 :=
        CCert.q_congr_big _ _ (by omega) (by omega) (by omega)
      _ = 37 := by decide
  have hs' : CCert.seen 9 37 0 = true := by
    simpa [hqa,hqk,CCert.q] using hs
  have hnot : CCert.seen 9 37 0 = false := by decide
  rw [hnot] at hs'
  cases hs'

/-- Every gateway with j=103 mod 128 has only the m=0 c=0 parent.
    Its quotient image (15,25,0) is absent from the kernel-checked M32 cone. -/
theorem thin_gateway_103_unreachable (n : Nat) :
    ¬ BB6CLine.Reach (0,2*(103+128*n),4*(103+128*n)+10) := by
  intro h
  have hp := zeroA_reach_parent (2*(103+128*n))
    (4*(103+128*n)+10) (by omega) (by omega) (by omega) h
  rcases hp with hQ | hU
  · have hQ' : BB6CLine.Reach (207+256*n,313+384*n,0) := by
      convert hQ.2 using 1 <;> omega
    exact no_parent_15_25 n hQ'
  · have hKmod : (2*(103+128*n))%4=2 := by omega
    omega

/-- Every gateway with j=86 mod 128 has only two viable c=0 inverse
    parents, with M32 images (13,38,0) and (9,37,0). -/
theorem thin_gateway_86_unreachable (n : Nat) :
    ¬ BB6CLine.Reach (0,2*(86+128*n),4*(86+128*n)+10) := by
  intro h
  have hp0 := zeroA_reach_parent (2*(86+128*n))
    (4*(86+128*n)+10) (by omega) (by omega) (by omega) h
  rcases hp0 with hQ0 | hU0
  · have hQ0' : BB6CLine.Reach (173+256*n,262+384*n,0) := by
      convert hQ0.2 using 1 <;> omega
    exact no_parent_13_38 n hQ0'
  · have hU0' : BB6CLine.Reach (0,84+128*n,527+768*n) := by
      convert hU0.2 using 1 <;> omega
    have hp1 := zeroA_reach_parent (84+128*n) (527+768*n)
      (by omega) (by omega) (by omega) hU0'
    rcases hp1 with hQ1 | hU1
    · have hodd : (527+768*n)%2=1 := by omega
      omega
    · have hU1' : BB6CLine.Reach (0,40+64*n,612+896*n) := by
        convert hU1.2 using 1 <;> omega
      have hp2 := zeroA_reach_parent (40+64*n) (612+896*n)
        (by omega) (by omega) (by omega) hU1'
      rcases hp2 with hQ2 | hU2
      · have hQ2' : BB6CLine.Reach (41+64*n,325+480*n,0) := by
          convert hQ2.2 using 1 <;> omega
        exact no_parent_9_37 n hQ2'
      · have hU2' : BB6CLine.Reach (0,18+32*n,653+960*n) := by
          convert hU2.2 using 1 <;> omega
        have hp3 := zeroA_reach_parent (18+32*n) (653+960*n)
          (by omega) (by omega) (by omega) hU2'
        rcases hp3 with hQ3 | hU3
        · have hodd : (653+960*n)%2=1 := by omega
          omega
        · have hKmod : (18+32*n)%4=2 := by omega
          omega

#print axioms thin_gateway_103_unreachable
#print axioms thin_gateway_86_unreachable

end BB6.Agent47ThinGateway
