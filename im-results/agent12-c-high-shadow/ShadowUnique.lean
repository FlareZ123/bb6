import NegativeShadow
import Lean

namespace BB6.Agent12ShadowUnique
open BB6.Agent13NegativeShadow
set_option maxHeartbeats 0

def Positive (s : Pair) : Prop := 0<s.x ∧ 0<s.y

def High (s t : Pair) (n : Nat) : Prop :=
  t.x%2=parity s ∧ 2+parity s<t.x ∧
  q s=2^(n+1)*(t.x-2-parity s) ∧ mass t=mass s+7+3*n

def Edge (s t : Pair) (i : Nat) : Prop :=
  (i=1 ∧ s.y%2=0 ∧ t=dir s) ∨ ∃ n, i=n+2 ∧ High s t n

theorem high_of_valid (b n : Nat) (s t : Pair) (hs : Positive s)
    (hv : validVal b s=true) (hd : depthOK s n=true) (hh : validHi s t n=true) : High s t n := by
  obtain ⟨_,hm⟩ := of_decide_eq_true hv
  obtain ⟨hn,_⟩ := of_decide_eq_true hd
  obtain ⟨ha,hk⟩ := of_decide_eq_true hh
  have hvdiv : 2^(val s)∣q s := by
    have h := Nat.mod_add_div (q s) (2^(val s+1))
    rw [hm,Nat.pow_succ] at h
    refine ⟨1+2*(q s/2^(val s+1)),?_⟩
    rw [Nat.mul_add,Nat.mul_one,←Nat.mul_assoc]
    simpa only [←Nat.pow_succ] using h.symm
  have hdiv : 2^(n+2)∣q s := Nat.dvd_trans (Nat.pow_dvd_pow 2 hn) hvdiv
  obtain ⟨d,hd⟩ := hdiv
  have hq : 0<q s := by unfold Positive at hs; unfold q parity; omega
  have hdpos : 0<d := by
    by_cases h : d=0
    · simp [h] at hd; omega
    · omega
  have he : t.x=2*d+2+parity s := by
    apply Nat.mul_left_cancel (n:=2^(n+1)) (Nat.pow_pos (by decide))
    rw [ha,hd,show 2^(n+2)=2^(n+1)*2 by rfl]
    simp only [Nat.mul_add,Nat.mul_assoc]
    ac_rfl
  refine ⟨?_,by omega,?_,?_⟩
  · have hp : parity s<2 := Nat.mod_lt _ (by decide)
    omega
  · rw [he,show 2*d+2+parity s-2-parity s=2*d by omega,hd,show 2^(n+2)=2^(n+1)*2 by rfl,Nat.mul_assoc]
  · unfold mass at hk ⊢; omega

theorem direct_shape {s : Pair} (hs : Positive s) (he : s.y%2=0) :
    (dir s).x>2*(dir s).y ∧ mass (dir s)=mass s+4 := by
  unfold Positive at hs
  simp [dir,mass]; omega

theorem high_shape {s t : Pair} {n : Nat} (hs : Positive s) (h : High s t n) : t.x≤2*t.y := by
  obtain ⟨hp,hx,hq,hm⟩ := h
  have hpow : 2≤2^(n+1) := by
    exact Nat.pow_le_pow_right (show 0<(2:Nat) by decide) (show 1≤n+1 by omega)
  have hle:=Nat.mul_le_mul_right (t.x-2-parity s) hpow
  rw [←hq] at hle
  have hp2 : parity s<2 := Nat.mod_lt _ (by decide)
  have hsum : q s+parity s=s.x+s.y := by unfold q parity; omega
  unfold mass Positive at *
  omega

theorem high_unique {s u t : Pair} {n m : Nat} (hs : Positive s) (hu : Positive u)
    (h : High s t n) (h' : High u t m) : s=u ∧ n=m := by
  obtain ⟨hp,hx,hq,hm⟩ := h
  obtain ⟨hp',hx',hq',hm'⟩ := h'
  have he : parity s=parity u := hp.symm.trans hp'
  rw [←he] at hq'
  have hsum : q s+parity s=s.x+s.y := by unfold q parity; omega
  have hsum' : q u+parity u=u.x+u.y := by unfold q parity; omega
  have hb : parity s<2 := Nat.mod_lt _ (by decide)
  have hnon : ¬n<m := by
    intro hlt
    have hpow : 2^(n+2)≤2^(m+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hle := Nat.mul_le_mul_right (t.x-2-parity s) hpow
    rw [←hq'] at hle
    have heq : 2^(n+2)*(t.x-2-parity s)=2*q s := by rw [hq,show 2^(n+2)=2^(n+1)*2 by rfl]; ac_rfl
    rw [heq] at hle
    unfold mass Positive at *
    omega
  have hnon' : ¬m<n := by
    intro hlt
    have hpow : 2^(m+2)≤2^(n+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hle := Nat.mul_le_mul_right (t.x-2-parity s) hpow
    rw [←hq] at hle
    have heq : 2^(m+2)*(t.x-2-parity s)=2*q u := by rw [hq',show 2^(m+2)=2^(m+1)*2 by rfl]; ac_rfl
    rw [heq] at hle
    unfold mass Positive at *
    omega
  have hnm : n=m := by omega
  subst m
  have hqq : q s=q u := hq.trans hq'.symm
  unfold mass at hm hm'
  have h1 : s.x=u.x := by omega
  have h2 : s.y=u.y := by omega
  cases s; cases u; simp_all

theorem edge_unique {s u t : Pair} {i j : Nat} (hs : Positive s) (hu : Positive u)
    (h : Edge s t i) (h' : Edge u t j) : s=u ∧ i=j := by
  rcases h with ⟨rfl,he,rfl⟩|⟨n,rfl,hh⟩
  · rcases h' with ⟨rfl,he',ht⟩|⟨m,rfl,hh'⟩
    · have hy := congrArg Pair.y ht
      have hx := congrArg Pair.x ht
      simp only [dir] at hy hx
      have h1 : s.x=u.x := by omega
      have h2 : s.y=u.y := by omega
      cases s; cases u; simp_all
    · have h1 := (direct_shape hs he).1
      have h2 := high_shape hu hh'
      omega
  · rcases h' with ⟨rfl,he,ht⟩|⟨m,rfl,hh'⟩
    · subst t
      have h1 := high_shape hs hh
      have h2 := (direct_shape hu he).1
      omega
    · obtain ⟨h1,h2⟩ := high_unique hs hu hh hh'
      exact ⟨h1,by omega⟩

theorem edge_mass {s t : Pair} {i : Nat} (hs : Positive s) (h : Edge s t i) :
    mass t=mass s+3*i+1 := by
  rcases h with ⟨rfl,he,rfl⟩|⟨n,rfl,hh⟩
  · have h:= (direct_shape hs he).2; omega
  · have h:=hh.2.2.2; omega

/-- A trace records the bit charge and destination of every actual edge. -/
inductive Trace (r : Pair) : List (Nat × Pair) → Pair → Prop where
  | nil (hr : Positive r) : Trace r [] r
  | snoc {xs s t i} (p : Trace r xs s) (ht : Positive t) (h : Edge s t i) :
      Trace r (xs++[(i,t)]) t

def bits (xs : List (Nat × Pair)) := (xs.map Prod.fst).sum

theorem trace_positive {r t xs} (p : Trace r xs t) : Positive t := by
  cases p with
  | nil hr => exact hr
  | snoc _ ht _ => exact ht

theorem trace_mass {r t xs} (p : Trace r xs t) :
    mass t=mass r+3*bits xs+xs.length := by
  induction p with
  | nil => simp [bits]
  | snoc p ht he ih =>
    have hh:=edge_mass (trace_positive p) he
    simp only [bits,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,List.length_append,List.length_cons,List.length_nil] at ih ⊢
    omega

theorem trace_unique {r t xs ys} (p : Trace r xs t) (q : Trace r ys t) : xs=ys := by
  induction p generalizing ys with
  | nil hr =>
    have hm:=trace_mass q
    have h : ys.length=0 := by omega
    exact (List.length_eq_zero_iff.mp h).symm
  | @snoc xs s t i p ht he ih =>
    cases q with
    | nil hr =>
      have hm:=trace_mass p
      have hh:=edge_mass (trace_positive p) he
      omega
    | @snoc ys u _ j q hu hf =>
      obtain ⟨h,hij⟩:=edge_unique (trace_positive p) (trace_positive q) he hf
      subst u; subst j
      rw [ih q]

theorem trace_bits_ge_length {r t xs} (p : Trace r xs t) : xs.length≤bits xs := by
  induction p with
  | nil => simp [bits]
  | @snoc xs s t i p ht he ih =>
    have h : 1≤i := by
      rcases he with ⟨rfl,_,_⟩|⟨n,rfl,_⟩ <;> omega
    simp only [bits,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,List.length_append,List.length_cons,List.length_nil] at ih ⊢
    omega

theorem precision_mass_bound {r t xs} (p : Trace r xs t) (B : Nat) (hb : bits xs≤B) :
    mass t≤mass r+4*B := by
  have hm:=trace_mass p
  have hl:=trace_bits_ge_length p
  omega

#print axioms high_of_valid
#print axioms edge_unique
#print axioms trace_unique
#print axioms precision_mass_bound
end BB6.Agent12ShadowUnique
