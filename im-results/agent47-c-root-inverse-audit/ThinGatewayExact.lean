import CLine
import Lean.Elab.Tactic.Omega

namespace BB6.Agent47ThinExact
open BB6CLine

/-- A high-sector decrement preserves the two coordinates K=a+k, C=c-a. -/
def Chain (K C : Nat) (s : Nat × Nat × Nat) : Prop :=
  s.1+s.2.1=K ∧ s.2.2=C+s.1

/-- Every possible entry into an even-K high-sector chain. The K=4
    exception is the special a=1, c=0 transition. -/
def Entry (K C : Nat) (s : Nat × Nat × Nat) : Prop :=
  (2≤K ∧ C%2=0 ∧ s=(K+1,(C+K-2)/2,0)) ∨
  (4≤K ∧ K%4=0 ∧ s=(0,(K-4)/2,C+K+1)) ∨
  (K=4 ∧ C%2=1 ∧ s=(1,(C+3)/2,0))

theorem chain_predecessor (K C : Nat) (he : K%2=0) (hc : 4≤C)
    (p t : Nat × Nat × Nat) (h : nextC p=some t) (ht : Chain K C t) :
    Chain K C p ∨ Entry K C p := by
  rcases p with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp only [nextC,Option.some.injEq] at h
      subst t
      simp [Chain] at ht
      omega
    · rcases k with _|k
      · simp only [nextC,Option.some.injEq] at h
        subst t
        simp [Chain] at ht <;> omega
      · simp only [nextC,Option.some.injEq] at h
        subst t
        simp [Chain] at ht
        right; right; right
        simp only [Prod.mk.injEq, true_and, and_true]
        omega
    · simp only [nextC,Option.some.injEq] at h
      subst t
      simp [Chain] at ht
      right; left
      simp only [Prod.mk.injEq, and_true]
      omega
  · simp only [nextC,Option.some.injEq] at h
    subst t
    simp [Chain] at ht <;> omega
  · simp [nextC] at h
  · simp only [nextC,Option.some.injEq] at h
    subst t
    simp [Chain] at ht
    omega
  · rcases a with _|a
    · dsimp [nextC] at h
      by_cases hk : k%2=0
      · simp only [hk,↓reduceIte,Option.some.injEq] at h
        subst t
        simp [Chain] at ht
        right; right; left
        simp only [Prod.mk.injEq, true_and]
        omega
      · simp only [hk,↓reduceIte,Option.some.injEq] at h
        subst t
        simp [Chain] at ht
        omega
    · simp only [nextC,Option.some.injEq] at h
      subst t
      simp [Chain] at ht ⊢
      left
      omega

/-- Any blank-reachable chain has a blank-reachable entry. -/
theorem reached_chain_has_entry (K C : Nat) (he : K%2=0) (hc : 4≤C)
    (t : Nat × Nat × Nat) (hr : Reach t) (ht : Chain K C t) :
    ∃ p, Reach p ∧ Entry K C p := by
  induction hr with
  | init => simp [Chain] at ht <;> omega
  | next p t hp hstep ih =>
    rcases chain_predecessor K C he hc p t hstep ht with hchain | hentry
    · exact ih hchain
    · exact ⟨p,hp,hentry⟩

/-- Every reached high-chain state drains to its zero-a endpoint. -/
theorem drain (C a k : Nat) (hc : 3≤C) (hr : Reach (a,k,C+a)) :
    Reach (0,k+a,C) := by
  induction a generalizing k with
  | zero => simpa using hr
  | succ a ih =>
    have hstep : nextC (a+1,k,C+(a+1))=some (a,k+1,C+a) := by
      have he : C+(a+1)=(C+a-3)+4 := by omega
      rw [he]
      change some (a,k+1,(C+a-3)+3)=some (a,k+1,C+a)
      simp only [Option.some.injEq,Prod.mk.injEq, true_and]
      omega
    have hh := ih (k+1) (Reach.next _ _ hr hstep)
    rwa [show k+1+a=k+(a+1) by omega] at hh

/-- Every entry actually reaches the high-chain endpoint. -/
theorem entry_reaches_endpoint (K C : Nat) (heK : K%2=0) (hc : 4≤C)
    (p : Nat × Nat × Nat) (hr : Reach p) (hp : Entry K C p) : Reach (0,K,C) := by
  rcases hp with ⟨hK,hCe,hp⟩ | ⟨hK,hKe,hp⟩ | ⟨hK,hCo,hp⟩
  · subst p
    have hstep : nextC (K+1,(C+K-2)/2,0)=some (K-1,1,C+(K-1)) := by
      have hK' : K+1=(K-1)+2 := by omega
      rw [hK']
      simp only [nextC,Option.some.injEq,Prod.mk.injEq]
      simp only [true_and]
      omega
    have hh := drain C (K-1) 1 (by omega) (Reach.next _ _ hr hstep)
    rwa [show 1+(K-1)=K by omega] at hh
  · subst p
    have hstep : nextC (0,(K-4)/2,C+K+1)=some (K-2,2,C+(K-2)) := by
      have he : C+K+1=(C+K-3)+4 := by omega
      rw [he]
      simp only [nextC]
      have hk : ((K-4)/2)%2=0 := by omega
      simp only [hk,↓reduceIte,Option.some.injEq,Prod.mk.injEq]
      simp only [true_and]
      omega
    have hh := drain C (K-2) 2 (by omega) (Reach.next _ _ hr hstep)
    rwa [show 2+(K-2)=K by omega] at hh
  · subst K; subst p
    have hstep : nextC (1,(C+3)/2,0)=some (2,2,C+2) := by
      have he : (C+3)/2=((C+3)/2-1)+1 := by omega
      rw [he]
      simp only [nextC,Option.some.injEq,Prod.mk.injEq]
      simp only [true_and]
      omega
    exact drain C 2 2 (by omega) (Reach.next _ _ hr hstep)

/-- Complete exact reachability recurrence, including K=0,2,4. -/
theorem zeroA_reach_iff (K C : Nat) (he : K%2=0) (hc : 4≤C) :
    Reach (0,K,C) ↔
      (2≤K ∧ C%2=0 ∧ Reach (K+1,(C+K-2)/2,0)) ∨
      (4≤K ∧ K%4=0 ∧ Reach (0,(K-4)/2,C+K+1)) ∨
      (K=4 ∧ C%2=1 ∧ Reach (1,(C+3)/2,0)) := by
  constructor
  · intro h
    obtain ⟨p,hp,hen⟩ := reached_chain_has_entry K C he hc _ h (by simp [Chain])
    rcases hen with ⟨hk,hc,hp'⟩ | ⟨hk,he,hp'⟩ | ⟨hk,hc,hp'⟩
    · subst p; exact Or.inl ⟨hk,hc,hp⟩
    · subst p; exact Or.inr (Or.inl ⟨hk,he,hp⟩)
    · subst p; exact Or.inr (Or.inr ⟨hk,hc,hp⟩)
  · rintro (⟨hk,hc',hr⟩ | ⟨hk,he',hr⟩ | ⟨hk,hc',hr⟩)
    · exact entry_reaches_endpoint K C he hc _ hr (Or.inl ⟨hk,hc',rfl⟩)
    · exact entry_reaches_endpoint K C he hc _ hr (Or.inr (Or.inl ⟨hk,he',rfl⟩))
    · exact entry_reaches_endpoint K C he hc _ hr (Or.inr (Or.inr ⟨hk,hc',rfl⟩))

/-- A nonrecursive entry has third coordinate zero. -/
def RootEntry (K C : Nat) (p : Nat × Nat × Nat) : Prop :=
  (2≤K ∧ C%2=0 ∧ p=(K+1,(C+K-2)/2,0)) ∨
  (K=4 ∧ C%2=1 ∧ p=(1,(C+3)/2,0))

/-- All possible c=0 ancestors of an even-K, C≥4 endpoint, expressed by
    two closed-form invariants at an arbitrary depth. -/
def Origin (K C : Nat) (p : Nat × Nat × Nat) : Prop :=
  ∃ d L D : Nat, L%2=0 ∧ 4≤D ∧
    (L+4)*2^d=K+4 ∧ D+2*L+3*d=C+2*K ∧ RootEntry L D p

private theorem entry_base (K C : Nat) (he : K%2=0) (hc : 4≤C)
    (p : Nat × Nat × Nat) (hp : RootEntry K C p) : Origin K C p := by
  exact ⟨0,K,C,he,hc,by simp,by simp,hp⟩

private theorem origin_lift (K C : Nat) (hK : 4≤K) (h4 : K%4=0)
    (p : Nat × Nat × Nat) (h : Origin ((K-4)/2) (C+K+1) p) : Origin K C p := by
  obtain ⟨d,L,D,hL,hD,hp,hc,hr⟩ := h
  refine ⟨d+1,L,D,hL,hD,?_,?_,hr⟩
  · rw [Nat.pow_succ,←Nat.mul_assoc,hp]
    omega
  · omega

private theorem origin_descend (K C : Nat) (p : Nat × Nat × Nat) (d L D : Nat)
    (hL : L%2=0) (hD : 4≤D) (hp : (L+4)*2^(d+1)=K+4)
    (hc : D+2*L+3*(d+1)=C+2*K) (hr : RootEntry L D p) :
    4≤K ∧ K%4=0 ∧ Origin ((K-4)/2) (C+K+1) p := by
  rw [Nat.pow_succ,←Nat.mul_assoc] at hp
  have hpos : 0<2^d := Nat.pow_pos (by decide)
  have hge : L+4≤(L+4)*2^d := by
    simpa using Nat.mul_le_mul_left (L+4) (show 1≤2^d by omega)
  have hprod : (L+4)*2^d=2*(((L+4)/2)*2^d) := by
    rw [←Nat.mul_assoc,show 2*((L+4)/2)=L+4 by omega]
  have hK : 4≤K := by omega
  have h4 : K%4=0 := by omega
  exact ⟨hK,h4,⟨d,L,D,hL,hD,by omega,by omega,hr⟩⟩

/-- Exact finite inverse fan, for arbitrary C≥4 and even K. Every candidate
    is a real c=0 ancestor (sufficiency), and no other entry can reach the
    endpoint from the blank accelerator root (necessity). -/
theorem origin_reach_iff (K C : Nat) (he : K%2=0) (hc : 4≤C) :
    Reach (0,K,C) ↔ ∃ p, Reach p ∧ Origin K C p := by
  induction K using Nat.strongRecOn generalizing C with
  | ind K ih =>
    constructor
    · intro h
      rcases (zeroA_reach_iff K C he hc).mp h with hhi | hb | hlo
      · obtain ⟨hK,hCe,hr⟩ := hhi
        exact ⟨_,hr,entry_base K C he hc _ (Or.inl ⟨hK,hCe,rfl⟩)⟩
      · obtain ⟨hK,h4,hr⟩ := hb
        have hlt : (K-4)/2<K := by omega
        have hb := (ih _ hlt (C+K+1) (by omega) (by omega)).mp hr
        obtain ⟨p,hp,ho⟩ := hb
        exact ⟨p,hp,origin_lift K C hK h4 p ho⟩
      · obtain ⟨hK,hCo,hr⟩ := hlo
        exact ⟨_,hr,entry_base K C he hc _ (Or.inr ⟨hK,hCo,rfl⟩)⟩
    · rintro ⟨p,hp,d,L,D,hL,hD,hprod,hsum,hr⟩
      cases d with
      | zero =>
        simp at hprod hsum
        have hLK : L=K := by omega
        subst L
        have hDC : D=C := by omega
        subst D
        rcases hr with ⟨hK,hCe,hh⟩ | ⟨hK,hCo,hh⟩
        · subst p
          exact (zeroA_reach_iff K C he hc).mpr (Or.inl ⟨hK,hCe,hp⟩)
        · subst p
          exact (zeroA_reach_iff K C he hc).mpr (Or.inr (Or.inr ⟨hK,hCo,hp⟩))
      | succ d =>
        obtain ⟨hK,h4,ho⟩ := origin_descend K C p d L D hL hD hprod hsum hr
        have hlt : (K-4)/2<K := by omega
        have hh := (ih _ hlt (C+K+1) (by omega) (by omega)).mpr ⟨p,hp,ho⟩
        exact (zeroA_reach_iff K C he hc).mpr (Or.inr (Or.inl ⟨hK,h4,hh⟩))

/-- Parameterized high c=0 stopping candidate for the specified gateway j. -/
def HighOrigin (j : Nat) (p : Nat × Nat × Nat) : Prop :=
  ∃ m q k : Nat, j+2=2^(2*m)*(q+3) ∧
    k+q+3*m+5=4*(j+2) ∧ p=(2*q+3,k,0)

/-- The exceptional low c=0 stopping candidate for the specified gateway j. -/
def LowOrigin (j : Nat) (p : Nat × Nat × Nat) : Prop :=
  ∃ m k : Nat, 1≤m ∧ j+2=2^(2*m+1) ∧
    k+3*m+4=4*(j+2) ∧ p=(1,k,0)

private theorem linear_le_pow (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- The full inverse fan of an individual thin gateway, in the original
    high and low stopping parameters. The low branch is essential. -/
theorem thin_origin_iff (j : Nat) (p : Nat × Nat × Nat) :
    Origin (2*j) (4*j+10) p ↔ HighOrigin j p ∨ LowOrigin j p := by
  constructor
  · rintro ⟨d,L,D,hL,hD,hprod,hsum,hr⟩
    rcases hr with ⟨hL2,hDe,hp⟩ | ⟨hL4,hDo,hp⟩
    · let m := d/2
      let q := (L-2)/2
      have hd : d=2*m := by dsimp [m]; omega
      have hl : L=2*q+2 := by dsimp [q]; omega
      let k := (D+L-2)/2
      have h2k : 2*k=D+L-2 := by dsimp [k]; omega
      have hfac : L+4=2*(q+3) := by omega
      have hj : j+2=2^(2*m)*(q+3) := by
        rw [hd,hfac,Nat.mul_assoc,Nat.mul_comm (q+3)] at hprod
        omega
      left
      refine ⟨m,q,k,hj,?_,?_⟩
      · omega
      · rw [hp,show L+1=2*q+3 by omega]
    · let m := (d+1)/2
      have hm : 1≤m := by dsimp [m]; omega
      have hd : d+1=2*m := by dsimp [m]; omega
      have hj : j+2=2^(2*m+1) := by
        rw [hL4] at hprod
        rw [show 2*m+1=d+2 by omega,Nat.pow_add]
        simp only [show (2:Nat)^2=4 by decide]
        omega
      let k := (D+3)/2
      have hk : 2*k=D+3 := by dsimp [k]; omega
      right
      exact ⟨m,k,hm,hj,by omega,hp⟩
  · rintro (⟨m,q,k,hj,hk,hp⟩ | ⟨m,k,hm,hj,hk,hp⟩)
    · have hpow : m+1≤2^(2*m) := by
        exact Nat.le_trans (linear_le_pow m) (Nat.pow_le_pow_right (by decide) (by omega))
      have hmul := Nat.mul_le_mul_right (q+3) hpow
      rw [←hj,Nat.add_mul] at hmul
      have h3m : 3*m≤m*(q+3) := by
        rw [Nat.mul_comm 3 m]
        exact Nat.mul_le_mul_left m (by omega)
      have hbound : q+3+3*m≤j+2 := by omega
      have hk2 : q+2≤k := by omega
      refine ⟨2*m,2*q+2,2*k-2*q,by omega,by omega,?_,?_,?_⟩
      · rw [show 2*q+2+4=2*(q+3) by omega,Nat.mul_assoc,Nat.mul_comm (q+3),←hj]
        omega
      · omega
      · left
        refine ⟨by omega,by omega,?_⟩
        rw [hp]
        simp only [Prod.mk.injEq,true_and,and_true]
        omega
    · have hpow := linear_le_pow (2*m+1)
      rw [←hj] at hpow
      have hk4 : 4≤k := by omega
      refine ⟨2*m-1,4,2*k-3,by decide,by omega,?_,?_,?_⟩
      · rw [show 2*m+1=(2*m-1)+2 by omega,Nat.pow_add] at hj
        simp only [show (2:Nat)^2=4 by decide] at hj
        omega
      · omega
      · right
        refine ⟨rfl,by omega,?_⟩
        rw [hp]
        simp only [Prod.mk.injEq,true_and,and_true]
        omega

/-- Exact *per-index* blank reachability criterion, with no cutoff. -/
theorem thin_reach_iff (j : Nat) : Reach (0,2*j,4*j+10) ↔
    (∃ m q k : Nat, j+2=2^(2*m)*(q+3) ∧
      k+q+3*m+5=4*(j+2) ∧ Reach (2*q+3,k,0)) ∨
    (∃ m k : Nat, 1≤m ∧ j+2=2^(2*m+1) ∧
      k+3*m+4=4*(j+2) ∧ Reach (1,k,0)) := by
  rw [origin_reach_iff (2*j) (4*j+10) (by omega) (by omega)]
  constructor
  · rintro ⟨p,hp,ho⟩
    rcases (thin_origin_iff j p).mp ho with ⟨m,q,k,hj,hk,he⟩ | ⟨m,k,hm,hj,hk,he⟩
    · subst p; exact Or.inl ⟨m,q,k,hj,hk,hp⟩
    · subst p; exact Or.inr ⟨m,k,hm,hj,hk,hp⟩
  · rintro (⟨m,q,k,hj,hk,hr⟩ | ⟨m,k,hm,hj,hk,hr⟩)
    · exact ⟨_,hr,(thin_origin_iff j _).mpr (Or.inl ⟨m,q,k,hj,hk,rfl⟩)⟩
    · exact ⟨_,hr,(thin_origin_iff j _).mpr (Or.inr ⟨m,k,hm,hj,hk,rfl⟩)⟩

#print axioms zeroA_reach_iff
#print axioms origin_reach_iff
#print axioms thin_origin_iff
#print axioms thin_reach_iff
end BB6.Agent47ThinExact
