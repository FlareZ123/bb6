import LongBlockCover
import TraceComplementCover

namespace BB6.Agent45LongBlock
open BB6.Agent45ReverseBlock
open BB6.Agent45.DelayedCarry
open BB6.Agent43P1Complement

def recoverHalfRows (s : Nat) (ps : List Prefix) (rows : Nat → List WitnessRow) : List Prefix :=
  (recoverRows s ps rows).filter fun p => p.1%4=1

theorem half_covered_first (n : Nat) : HalfCovered n 1 [(1,(n+2)/2)] := by
  intro B a C c ht hm he
  exact covered_first n B a C c ht he

private theorem extend_mod4 (n s B a h C c : Nat) (hs : 2≤s)
    (he : Extend n s B a h C c) : C%4=B%4 := by
  have hd : 4 ∣ (2:Nat)^s := by simpa using Nat.pow_dvd_pow 2 hs
  obtain ⟨R,hR⟩ := extend_mod n s B a h C c he
  rw [hR,Nat.add_mod,Nat.mul_mod,Nat.mod_eq_zero_of_dvd hd]
  simp

private theorem prefix_mod4 (n s B a h C c : Nat) (hs : 1≤s)
    (ht : Trace n s B a) (he : Extend n s B a h C c) (hm : C%4=1) : B%4=1 := by
  obtain ⟨_,hb,ho,_⟩ := trace_bounds n s B a ht
  by_cases h1 : s=1
  · subst s; simp at hb; omega
  · rw [←extend_mod4 n s B a h C c (by omega) he]
    exact hm

theorem half_covered_next_rows (L n s h : Nat) (ps qs : List Prefix)
    (rows : Nat → List WitnessRow) (hs : 1≤s) (hhn : h≤n) (hL : h≤2^L)
    (hOld : HalfCovered n s ps) (hLive : MidpointRows L n s h ps rows)
    (hrec : recoverHalfRows s ps rows=qs) : HalfCovered n (s+h) qs := by
  intro B a C c ht hm he
  obtain ⟨D,d,hpre,hExt⟩ := trace_split n (s+h) B a s ht hs (by omega)
  have hExt' : Extend n s D d h B a := by simpa using hExt
  have hmod := prefix_mod4 n s D d h B a hs hpre hExt' hm
  have hfull := extend_append n s D d h B a n C c hExt' he
  obtain ⟨E,e,hshort⟩ := extend_prefix n s D d (h+n) C c n hfull (by omega)
  have hp := hOld D d E e hpre hmod hshort
  obtain ⟨F,f,hsuf⟩ := extend_prefix n (s+h) B a n C c (n-h) he (by omega)
  have hmem := midpoint_rows_recovered L n s h D d B a F f ps rows hhn hL hp hpre hExt' hsuf hLive
  rw [←hrec]
  simp [recoverHalfRows,hmem,hm]

theorem half_covered_empty_rows (L n s h : Nat) (ps : List Prefix)
    (rows : Nat → List WitnessRow) (hs : 2≤s) (hhn : h≤n) (hL : h≤2^L)
    (hOld : HalfCovered n s ps) (hLive : MidpointRows L n s h ps rows)
    (hrec : recoverHalfRows s ps rows=[]) : HalfCovered n s [] := by
  intro B a C c ht hm he
  obtain ⟨D,d,hpre,hsuf⟩ := BB6.Agent45.DelayedCarry.extend_split n s B a n C c h he hhn
  have hp := hOld B a C c ht hm he
  have hmem := midpoint_rows_recovered L n s h B a D d C c ps rows hhn hL hp ht hpre hsuf hLive
  have hmod : D%4=1 := (extend_mod4 n s B a h D d hs hpre).trans hm
  have hm' : (D,d)∈recoverHalfRows s ps rows := by simp [recoverHalfRows,hmem,hmod]
  rw [hrec] at hm'
  exact False.elim (List.not_mem_nil hm')

theorem half_empty_to_full (n s : Nat) (hn : 1≤n) (heven : n%2=0)
    (hs : 2≤s) (h : HalfCovered n s []) : Covered n s [] := by
  simpa using complete_half n s [] hn heven hs h

#print axioms half_covered_first
#print axioms half_covered_next_rows
#print axioms half_covered_empty_rows
#print axioms half_empty_to_full
end BB6.Agent45LongBlock
