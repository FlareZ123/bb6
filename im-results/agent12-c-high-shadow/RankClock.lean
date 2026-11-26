import CRawCountBridge
import Lean

namespace BB6.Agent12RankClock
open BB6CLine BB6.Agent47ThinCounted
set_option maxHeartbeats 0

/-- Cubic primitive-clock budget with a right-counter correction.
    The correction telescopes exactly across every rank-preserving sweep. -/
def G (r : Nat) : Nat := r^3+6*r^2
def F (k : Nat) : Nat := 12*k^2+42*k
def potential (s : State) : Nat := G (rankC s)+F s.2.1

theorem G_mono {a b : Nat} (h : a≤b) : G a≤G b := by
  unfold G
  have h2 := Nat.pow_le_pow_left h 2
  have h3 := Nat.pow_le_pow_left h 3
  omega

theorem G_succ (r : Nat) : G (r+1)=G r+3*r^2+15*r+7 := by
  unfold G; grind

theorem G_three (r : Nat) : G (r+3)=G r+9*r^2+63*r+81 := by
  unfold G; grind

theorem F_succ (k : Nat) : F (k+1)=F k+6*(4*k+9) := by
  unfold F; grind

theorem F_mono {a b : Nat} (h : a≤b) : F a≤F b := by
  unfold F
  have h2 := Nat.pow_le_pow_left h 2
  omega

/-- Six times the literal raw move weight is paid by potential growth.
    No ordinary-section assumptions are required. -/
theorem edge_budget {s t : State} (h : nextC s=some t) :
    potential s+6*weight s≤potential t := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp only [nextC,Option.some.injEq] at h
      subst t
      simp only [potential,rankC,weight,Nat.zero_add,Nat.add_zero,Nat.mul_zero]
      rw [show 1+(2*k+2)=2*k+3 by omega,G_three]
      unfold F
      grind
    · rcases k with _|k
      · simp only [nextC,Option.some.injEq] at h
        subst t; decide
      · simp only [nextC,Option.some.injEq] at h
        subst t
        simp only [potential,rankC,weight,Nat.add_zero]
        have hR : 1+2*(k+1)+3≤2+2*2+(2*k+1) := by omega
        have hG := G_mono hR
        rw [G_three] at hG
        have h2 := Nat.pow_le_pow_left (show 2*(k+1)≤1+2*(k+1) by omega) 2
        unfold F
        grind
    · simp only [nextC,Option.some.injEq] at h
      subst t
      simp only [potential,rankC,weight,Nat.add_zero]
      rw [show a+2*1+(2*k+1)=a+2+2*k+1 by omega,G_succ]
      have h2 := Nat.pow_le_pow_left (show 2*k+2≤a+2+2*k by omega) 2
      unfold F
      grind
  · simp only [nextC,Option.some.injEq] at h
    subst t
    simp only [potential,rankC,weight,Nat.add_zero]
    change G (a+2*k+1)+F k+6*2≤G (a+2*(k+1))+F (k+1)
    have hG := G_mono (show a+2*k+1≤a+2*(k+1) by omega)
    rw [F_succ]; omega
  · simp [nextC] at h
  · simp only [nextC,Option.some.injEq] at h
    subst t
    simp only [potential,rankC,weight]
    change G (a+2*k+3)+F k+6*12≤G (a+2*(k+2)+1)+F (k+2)
    have hG := G_mono (show a+2*k+3≤a+2*(k+2)+1 by omega)
    have hF := F_mono (show k+1≤k+2 by omega)
    rw [F_succ] at hF
    have hG' := G_mono (show a+2*k+3+1≤a+2*(k+2)+1 by omega)
    rw [G_succ] at hG'
    have hsq : 1≤(a+2*k+3)^2 := Nat.pow_le_pow_left (by omega : 1≤a+2*k+3) 2
    omega
  · rcases a with _|a
    · by_cases he:k%2=0
      · simp only [nextC,he,ite_true,Option.some.injEq] at h
        subst t
        simp only [potential,rankC,weight,he,ite_true,Nat.zero_add]
        have hk : k=2*(k/2) := by omega
        have hR : 4*(k/2)+2+2*2+(d+1)=(2*k+(d+4))+3 := by omega
        rw [hR,G_three]
        have h2 := Nat.pow_le_pow_left (show 2*k+4≤2*k+(d+4) by omega) 2
        unfold F
        grind
      · simp only [nextC,he,ite_false,Option.some.injEq] at h
        subst t
        simp only [potential,rankC,weight,he,ite_false,Nat.zero_add,Nat.mul_zero,Nat.add_zero]
        have hk : k=2*(k/2)+1 := by omega
        have hR : 4*(k/2)+5+(d+4)=(2*k+(d+4))+3 := by omega
        rw [hR,G_three]
        have h2 := Nat.pow_le_pow_left (show 2*k+4≤2*k+(d+4) by omega) 2
        unfold F
        grind
    · simp only [nextC,Option.some.injEq] at h
      subst t
      simp only [potential,rankC,weight]
      change G (a+1+2*k+(d+4))+F k+6*(4*k+9)≤G (a+2*(k+1)+(d+3))+F (k+1)
      rw [show a+2*(k+1)+(d+3)=a+1+2*k+(d+4) by omega,F_succ]
      omega

theorem path_budget {n w : Nat} {s t : State} (p : Path n w s t) :
    potential s+6*w≤potential t := by
  induction p with
  | nil => simp
  | cons h p ih => have he := edge_budget h; omega

theorem potential_rank (s : State) : potential s≤(rankC s)^3+9*(rankC s)^2+21*rankC s := by
  have hk : 2*s.2.1≤rankC s := by unfold rankC; omega
  have hs := Nat.pow_le_pow_left hk 2
  unfold potential G F
  grind

theorem stop_iff_c2 (s : State) : nextC s=none ↔ s.2.2=2 := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp [nextC]
    · rcases k with _|k <;> simp [nextC]
    · simp [nextC]
  · simp [nextC]
  · simp [nextC]
  · simp [nextC]
  · rcases a with _|a
    · by_cases he : k%2=0 <;> simp [nextC,he]
    · simp [nextC]

theorem terminal_shape {s t : State} (h : nextC s=some t) (hr : 6≤rankC s)
    (ht : nextC t=none) : t.2.1=2 ∧ t.1%4=2 := by
  have hc := (stop_iff_c2 t).mp ht
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp only [nextC,Option.some.injEq] at h
      subst t
      simp [rankC] at hr
      simp at hc
      omega
    · rcases k with _|k <;> simp only [nextC,Option.some.injEq] at h <;> subst t <;> simp at hc
      omega
    · simp only [nextC,Option.some.injEq] at h
      subst t; simp at hc; omega
  · simp only [nextC,Option.some.injEq] at h; subst t; simp at hc
  · simp [nextC] at h
  · simp only [nextC,Option.some.injEq] at h; subst t; simp at hc
  · rcases a with _|a
    · by_cases he:k%2=0
      · simp only [nextC,he,ite_true,Option.some.injEq] at h
        subst t; simp
      · simp only [nextC,he,ite_false,Option.some.injEq] at h
        subst t; simp at hc
    · simp only [nextC,Option.some.injEq] at h
      subst t; simp at hc

theorem reach_rank {s : State} (h : BB6CLine.Reach s) : 6≤rankC s := by
  induction h with
  | init => decide
  | next _ _ _ h ih => exact Nat.le_trans ih (rank_mono h)

theorem reachable_terminal_shape {s : State} (h : BB6CLine.Reach s)
    (ht : nextC s=none) : s.2.1=2 ∧ s.1%4=2 := by
  cases h with
  | init => simp [nextC] at ht
  | next p q hp hq => exact terminal_shape hq (reach_rank hp) ht

/-- A hypothetical raw halt with successful-move count N has a reachable
    terminal rank R, and its Busy Beaver score N+1 obeys the cubic bound.
    The +204 constant includes the blank prefix and final halt query. -/
theorem raw_halt_rank_bound (N : Nat) (h : BB6Coverage.HaltsAfter BB6.Agent47CRaw.cMachine N) :
    ∃ t : State, BB6CLine.Reach t ∧ nextC t=none ∧
      6*(N+1)+204≤(rankC t)^3+6*(rankC t)^2 := by
  obtain ⟨n,w,t,p,ht,hN⟩ := (BB6.Agent47CRaw.raw_haltsAfter_iff N).mp h
  have hr := BB6.Agent47CRaw.path_reach p BB6CLine.Reach.init
  have hk := (reachable_terminal_shape hr ht).1
  have hb := path_budget p
  have hi : potential (5,0,1)=432 := by decide
  rw [hi] at hb
  unfold potential F G at hb
  rw [hk] at hb
  exact ⟨t,hr,ht,by omega⟩

#print axioms edge_budget
#print axioms path_budget
#print axioms potential_rank
#print axioms terminal_shape
#print axioms raw_halt_rank_bound

/-- Every literal halt has a genuine thin-gateway index; its exact terminal
    rank is 8*(j+2). This converts the clock bound to an index cutoff. -/
theorem raw_halt_gateway_bound (N : Nat)
    (h : BB6Coverage.HaltsAfter BB6.Agent47CRaw.cMachine N) :
    ∃ j : Nat, BB6CLine.Reach (0,2*j,4*j+10) ∧
      6*(N+1)+204≤G (8*j+16) := by
  obtain ⟨n,w,t,p,ht,hN⟩ := (BB6.Agent47CRaw.raw_haltsAfter_iff N).mp h
  obtain ⟨j,hj⟩ := stops_iff_thin.mp ⟨t,BB6.Agent47CRaw.path_reach p BB6CLine.Reach.init,ht⟩
  obtain ⟨l,v,q⟩ := BB6.Agent47CRaw.reach_path hj
  have hterm : nextC (8*j+10,2,2)=none := rfl
  have hpath := q.append (thin_tail_counted j)
  have he := (p.terminal_unique ht hpath hterm).2.2
  obtain ⟨u,hu,hbudget⟩ := raw_halt_rank_bound N h
  obtain ⟨l',v',q'⟩ := BB6.Agent47CRaw.reach_path hu
  have he' := (p.terminal_unique ht q' hbudget.1).2.2
  rw [←he',he] at hbudget
  refine ⟨j,hj,?_⟩
  simpa [rankC,G] using hbudget.2

/-- Any score above B must have a thin gateway beyond J whenever
    the cubic budget at J is at most B. The user of the theorem only
    needs to exclude large gateway indices, not compute smaller clocks. -/
theorem above_bound_requires_large_gateway (B J N : Nat)
    (hcut : G (8*J+16)≤6*B+204)
    (h : BB6Coverage.HaltsAfter BB6.Agent47CRaw.cMachine N)
    (hlarge : B<N+1) :
    ∃ j : Nat, J<j ∧ BB6CLine.Reach (0,2*j,4*j+10) := by
  obtain ⟨j,hj,hg⟩ := raw_halt_gateway_bound N h
  refine ⟨j,?_,hj⟩
  by_cases hn : J<j
  · exact hn
  · have hm := G_mono (show 8*j+16≤8*J+16 by omega)
    omega

/-- Gateway-tail exclusion is sufficient for a literal BB-score bound. -/
theorem raw_bound_of_gateway_tail (B J : Nat)
    (hcut : G (8*J+16)≤6*B+204)
    (hexcl : ∀ j : Nat, J<j → ¬ BB6CLine.Reach (0,2*j,4*j+10))
    (N : Nat) (h : BB6Coverage.HaltsAfter BB6.Agent47CRaw.cMachine N) :
    N+1≤B := by
  by_cases hn : N+1≤B
  · exact hn
  · obtain ⟨j,hj,hr⟩ := above_bound_requires_large_gateway B J N hcut h (by omega)
    exact False.elim (hexcl j hj hr)

#print axioms raw_halt_gateway_bound
#print axioms above_bound_requires_large_gateway
#print axioms raw_bound_of_gateway_tail

end BB6.Agent12RankClock
