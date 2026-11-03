import P1Rank
import P1Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace BB6.Gap
open BB6.Agent1 BB6.Fast BB6.Rank

theorem trace_add (m n : Nat) (s : Nat × Nat) :
    trace (m+n) s = (trace m s).bind (trace n) := by
  induction m generalizing s with
  | zero => simp [trace]
  | succ m ih =>
      simp only [Nat.succ_add, trace]
      cases hs : Tfast s.1 s.2 with
      | none => simp [hs]
      | some t => simp [hs, ih]

theorem trace_preserves_reach (n a c b d : Nat)
    (hr : Reach a c) (ht : trace n (a,c) = some (b,d)) : Reach b d := by
  induction n generalizing a c with
  | zero =>
      simp only [trace, Option.some.injEq, Prod.mk.injEq] at ht
      rcases ht with ⟨h1,h2⟩
      subst b
      subst d
      exact hr
  | succ n ih =>
      simp only [trace] at ht
      cases hs : Tfast a c with
      | none => simp [hs] at ht
      | some t =>
          simp only [hs, Option.bind_some] at ht
          have ht1 : T a c = some t := by simpa [Tfast_eq] using hs
          exact ih t.1 t.2 (Reach.next a c t.1 t.2 hr ht1) ht

theorem trace_rank_nondecreasing (n a c b d : Nat)
    (hr : Reach a c) (ht : trace n (a,c) = some (b,d)) :
    a+c ≤ b+d := by
  induction n generalizing a c with
  | zero =>
      simp only [trace, Option.some.injEq, Prod.mk.injEq] at ht
      omega
  | succ n ih =>
      simp only [trace] at ht
      cases hs : Tfast a c with
      | none => simp [hs] at ht
      | some t =>
          simp only [hs, Option.bind_some] at ht
          have ht1 : T a c = some t := by simpa [Tfast_eq] using hs
          have hstep := reachable_step_rank_strict a c t.1 t.2 hr ht1
          have htail := ih t.1 t.2 (Reach.next a c t.1 t.2 hr ht1) ht
          omega

theorem reach_has_index (a c : Nat) (hr : Reach a c) :
    ∃ n : Nat, trace n (2,1) = some (a,c) := by
  induction hr with
  | init => exact ⟨0,rfl⟩
  | next a c b d hr ht ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n+1, ?_⟩
      have hadd := trace_add n 1 (2,1)
      rw [hadd, hn]
      simp only [Option.bind_some]
      simpa [trace, Tfast_eq] using ht

theorem no_reach_rank_gap (N a c : Nat) (p q : Nat × Nat)
    (hN : trace N (2,1) = some p)
    (hstep : Tfast p.1 p.2 = some q)
    (hlow : p.1+p.2 < a+c) (hhigh : a+c < q.1+q.2) :
    ¬ Reach a c := by
  intro hr
  obtain ⟨n, hn⟩ := reach_has_index a c hr
  have hp : Reach p.1 p.2 := trace_preserves_reach N 2 1 p.1 p.2 Reach.init hN
  by_cases hcase : n ≤ N
  · have hsum : n+(N-n)=N := by omega
    have hab := trace_add n (N-n) (2,1)
    rw [hsum, hn, Option.bind_some] at hab
    rw [hN] at hab
    have hrank := trace_rank_nondecreasing (N-n) a c p.1 p.2 hr hab.symm
    omega
  · have hge : N+1 ≤ n := by omega
    have hT : trace 1 p = some q := by
      change (Tfast p.1 p.2).bind (fun x => some x) = some q
      simp [hstep]
    have hQ : trace (N+1) (2,1) = some q := by
      rw [trace_add N 1 (2,1),hN,Option.bind_some]
      exact hT
    have hsum : (N+1)+(n-(N+1))=n := by omega
    have hab := trace_add (N+1) (n-(N+1)) (2,1)
    rw [hsum,hQ,Option.bind_some] at hab
    rw [hn] at hab
    have hreachq : Reach q.1 q.2 := trace_preserves_reach (N+1) 2 1 q.1 q.2 Reach.init hQ
    have hrank := trace_rank_nondecreasing (n-(N+1)) q.1 q.2 a c hreachq hab.symm
    omega

#print axioms no_reach_rank_gap
end BB6.Gap
