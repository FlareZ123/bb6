import TraceComplement
import LagChecker

namespace BB6.Agent43P1Complement
open BB6.Agent45.DelayedCarry

/-- The reflection commutes with chronological extension, not just complete traces. -/
theorem extend_complement (n s B a k C c : Nat) (hn : 1≤n)
    (htr : Trace n s B a) (hE : Extend n s B a k C c) :
    Extend n s (2^s-B) (cap n s-a) k (2^(s+k)-C) (cap n (s+k)-c) := by
  induction hE with
  | nil => simpa using (Extend.nil : Extend n s (2^s-B) (cap n s-a) 0 (2^s-B) (cap n s-a))
  | step k C c x d he hx hh ih =>
    have hp := extend_trace n s B a k C c htr he
    obtain ⟨hi,hC,ho,_⟩ := trace_bounds n (s+k) C c hp
    have hc := trace_le_cap n (s+k) C c hn hp
    have hd := trace_le_cap n (s+k+1) (C+2^(s+k)*x) d hn (Trace.step (s+k) C c x d hp hx hh)
    have hcap := cap_step n (s+k) C hn hi hC ho
    have hw : 2^(s+k+1)-(C+2^(s+k)*x)=2^(s+k)-C+2^(s+k)*(1-x) := by
      rw [Nat.pow_succ]
      rcases (show x=0 ∨ x=1 by omega) with rfl|rfl <;> simp <;> omega
    rw [show s+(k+1)=s+k+1 by omega,hw]
    refine Extend.step k (2^(s+k)-C) (cap n (s+k)-c) (1-x) (cap n (s+k+1)-d) ih (by omega) ?_
    rcases (show x=0 ∨ x=1 by omega) with rfl|rfl <;> simp at hh ⊢ <;> omega

def HalfCovered (n s : Nat) (ps : List Prefix) : Prop :=
  ∀ B a C c, Trace n s B a → B%4=1 → Extend n s B a n C c → (B,a)∈ps

def reflectPrefix (n s : Nat) (p : Prefix) : Prefix := (2^s-p.1,cap n s-p.2)

private theorem pow_mod_four (s : Nat) (hs : 2≤s) : 2^s%4=0 := by
  have hd := Nat.pow_dvd_pow 2 hs
  exact Nat.dvd_iff_mod_eq_zero.mp (by simpa using hd)

/-- An ordinary coverage certificate follows by adding the missing reflected prefixes. -/
theorem complete_half (n s : Nat) (ps : List Prefix) (hn : 1≤n) (heven : n%2=0)
    (hs : 2≤s) (h : HalfCovered n s ps) :
    Covered n s (ps ++ ps.map (reflectPrefix n s)) := by
  intro B a C c ht he
  by_cases hm : B%4=1
  · exact List.mem_append_left _ (h B a C c ht hm he)
  obtain ⟨_,hB,ho,_⟩ := trace_bounds n s B a ht
  have ha := trace_le_cap n s B a hn ht
  have hh : 2^s-B+B=2^s := by omega
  have hr := congrArg (fun k : Nat => k%4) hh
  rw [Nat.add_mod,pow_mod_four s hs] at hr
  have hmod : (2^s-B)%4=1 := by omega
  have hmem := h _ _ _ _ (trace_complement n s B a hn heven ht) hmod (extend_complement n s B a n C c hn ht he)
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨(2^s-B,cap n s-a),hmem,?_⟩
  simp [reflectPrefix,show 2^s-(2^s-B)=B by omega,show cap n s-(cap n s-a)=a by omega]

/-- Existing full-prefix certificates can be restricted to the canonical half. -/
theorem restrict_full (n s : Nat) (ps : List Prefix) (h : Covered n s ps) :
    HalfCovered n s (ps.filter fun p => p.1%4=1) := by
  intro B a C c ht hm he
  simp [h B a C c ht he,hm]

/-- Any sound extension checker preserves half coverage; the residue mod 4 is fixed
    by the chronological prefix once its length is at least two. -/
theorem half_next (n s h : Nat) (ps qs : List Prefix) (hs : 2≤s)
    (hcover : HalfCovered n s ps)
    (hstep : ∀ B a C c, (B,a)∈ps → Extend n s B a h C c →
      (∃ D d, Extend n (s+h) C c n D d) → (C,c)∈qs) : HalfCovered n (s+h) qs := by
  intro B a C c ht hm he
  obtain ⟨D,d,hpre,hExt⟩ := trace_split n (s+h) B a s ht (by omega) (by omega)
  have hExt' : Extend n s D d h B a := by simpa using hExt
  obtain ⟨R,hR⟩ := extend_mod n s D d h B a hExt'
  have hmod : D%4=1 := by
    rw [hR,Nat.add_mod,Nat.mul_mod,pow_mod_four s hs] at hm
    simpa using hm
  have hfull := extend_append n s D d h B a n C c hExt' he
  obtain ⟨F,f,hshort⟩ := extend_prefix n s D d (h+n) C c n hfull (by omega)
  exact hstep D d B a (hcover D d F f hpre hmod hshort) hExt' ⟨C,c,he⟩

/-- An empty canonical half proves the same exclusion as an empty full cover. -/
theorem no_trace_of_half_empty (n s : Nat) (hn : 1≤n) (heven : n%2=0) (hs : 2≤s)
    (h : HalfCovered n s []) : ∀ m B a, n+s≤m → ¬ Trace n m B a := by
  apply no_trace_of_empty n s (by omega)
  simpa using complete_half n s [] hn heven hs h

#print axioms extend_complement
#print axioms complete_half
#print axioms restrict_full
#print axioms half_next
#print axioms no_trace_of_half_empty
end BB6.Agent43P1Complement
