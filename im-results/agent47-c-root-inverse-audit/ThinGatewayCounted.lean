import ThinGatewayExact

namespace BB6.Agent47ThinCounted
open BB6CLine BB6.Agent47ThinExact
abbrev State := Nat × Nat × Nat

/-- Weights specified in the published C acceleration rule comments.
    This module proves exact accelerator counts and sums of these weights;
    it does not yet prove a primitive-transition simulation theorem. -/
def weight : State → Nat
  | (_,_,1) => 2
  | (_,_,2) => 3
  | (_,_,3) => 12
  | (0,k,0) => 2*k+3
  | (1,0,0) => 11
  | (1,k+1,0) => 2*k+18
  | (_+2,k,0) => 2*k+4
  | (0,k,_+4) => if k%2=0 then 10*(k/2)+21 else 10*(k/2)+18
  | (_+1,k,_+4) => 4*k+9

inductive Path : Nat → Nat → State → State → Prop
  | nil (s : State) : Path 0 0 s s
  | cons {n w s t u} (h : nextC s=some t) (p : Path n w t u) :
      Path (n+1) (weight s+w) s u

theorem Path.append {n w m v s t u} (p : Path n w s t) (q : Path m v t u) :
    Path (n+m) (w+v) s u := by
  induction p with
  | nil => simpa using q
  | cons h p ih =>
    have h' := Path.cons h (ih q)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h'

theorem drain_counted (C a k : Nat) (hc : 3≤C) :
    Path a (2*a*a+(4*k+7)*a) (a,k,C+a) (0,k+a,C) := by
  induction a generalizing k with
  | zero => simpa using Path.nil (0,k,C)
  | succ a ih =>
    have he : C+(a+1)=(C+a-3)+4 := by omega
    have hstep : nextC (a+1,k,C+(a+1))=some (a,k+1,C+a) := by
      rw [he]
      change some (a,k+1,(C+a-3)+3)=some (a,k+1,C+a)
      simp only [Option.some.injEq,Prod.mk.injEq,true_and]
      omega
    have hh := Path.cons hstep (ih (k+1))
    have hw : weight (a+1,k,C+(a+1))=4*k+9 := by rw [he]; rfl
    rw [hw,show k+1+a=k+(a+1) by omega] at hh
    have hcost : 4*k+9+(2*a*a+(4*(k+1)+7)*a)=2*(a+1)*(a+1)+(4*k+7)*(a+1) := by
      simp only [Nat.add_mul,Nat.mul_add]; omega
    rwa [hcost] at hh

theorem high_entry_counted (K C : Nat) (hK : 2≤K) (he : K%2=0) (hc : 4≤C) (hCe : C%2=0) :
    ∃ w, Path K w (K+1,(C+K-2)/2,0) (0,K,C) ∧ w+7=2*K*K+8*K+C := by
  obtain ⟨r,hr⟩ : ∃ r, K=r+1 := ⟨K-1,by omega⟩
  subst K
  have hn : nextC (r+1+1,(C+(r+1)-2)/2,0)=some (r,1,C+r) := by
    simp only [nextC,Option.some.injEq,Prod.mk.injEq,true_and]
    omega
  have hh := Path.cons hn (drain_counted C r 1 (by omega))
  rw [show 1+r=r+1 by omega] at hh
  refine ⟨_,hh,?_⟩
  change 2*((C+(r+1)-2)/2)+4+(2*r*r+(4*1+7)*r)+7=2*(r+1)*(r+1)+8*(r+1)+C
  simp only [Nat.add_mul,Nat.mul_add]; omega

theorem low_entry_counted (C : Nat) (hc : 4≤C) (ho : C%2=1) :
    Path 3 (C+57) (1,(C+3)/2,0) (0,4,C) := by
  have he : (C+3)/2=((C+3)/2-1)+1 := by omega
  have hn : nextC (1,(C+3)/2,0)=some (2,2,C+2) := by
    rw [he]; simp only [nextC,Option.some.injEq,Prod.mk.injEq,true_and]; omega
  have hh := Path.cons hn (drain_counted C 2 2 (by omega))
  have hw : weight (1,(C+3)/2,0)=C+19 := by
    rw [he]; change 2*((C+3)/2-1)+18=C+19; omega
  rw [hw] at hh
  exact hh

/-- A recursive inverse-fan edge costs K-1 successful calls. The weight
    identity is stated without subtraction to permit direct telescoping. -/
theorem recursive_counted (K C : Nat) (hK : 4≤K) (h4 : K%4=0) (hc : 4≤C) :
    ∃ w, Path (K-1) w (0,(K-4)/2,C+K+1) (0,K,C) ∧
      3*w+51+8*((K-4)/2+4)*((K-4)/2+4)+39*(K+4)=
        8*(K+4)*(K+4)+39*((K-4)/2+4) := by
  let r := K-2
  have hKr : K=r+2 := by dsimp [r]; omega
  have he : C+K+1=(C+K-3)+4 := by omega
  have hk : ((K-4)/2)%2=0 := by omega
  have hn : nextC (0,(K-4)/2,C+K+1)=some (r,2,C+r) := by
    rw [he]; simp only [nextC,hk,↓reduceIte,Option.some.injEq,Prod.mk.injEq,true_and]
    omega
  have hh := Path.cons hn (drain_counted C r 2 (by omega))
  rw [show r+1=K-1 by omega,show 2+r=K by omega] at hh
  have hw : weight (0,(K-4)/2,C+K+1)=10*((K-4)/2/2)+21 := by
    rw [he]; simp only [weight,hk,↓reduceIte]
  rw [hw] at hh
  refine ⟨_,hh,?_⟩
  obtain ⟨z,hz⟩ : ∃ z, K=4*z+4 := ⟨(K-4)/4,by omega⟩
  have h1 : (K-4)/2=2*z := by omega
  have h2 : (K-4)/2/2=z := by omega
  have h3 : r=4*z+2 := by omega
  rw [h2,h3,h1,hz]
  simp only [Nat.add_mul,Nat.mul_add, Nat.mul_assoc]
  simp only [Nat.mul_left_comm z, ←Nat.mul_assoc]
  simp only [Nat.mul_assoc]
  omega


/-- Quantitative form of the entire recursive part of the inverse fan.
    The two closed forms telescope the number of calls and the weights. -/
theorem fan_counted (K C L D d : Nat) (he : L%2=0) (hc : 4≤C)
    (hp : (L+4)*2^d=K+4) (hs : D+2*L+3*d=C+2*K) :
    ∃ n w, Path n w (0,L,D) (0,K,C) ∧
      n+2*L+5*d=2*K ∧
      3*w+51*d+8*(L+4)*(L+4)+39*(K+4)=8*(K+4)*(K+4)+39*(L+4) := by
  induction d generalizing K C with
  | zero =>
    simp at hp hs
    have hl : K=L := by omega
    subst K
    have hd : C=D := by omega
    subst C
    exact ⟨0,0,Path.nil _,by omega,by omega⟩
  | succ d ih =>
    rw [Nat.pow_succ,←Nat.mul_assoc] at hp
    have hpos : 0<2^d := Nat.pow_pos (by decide)
    have hge : L+4≤(L+4)*2^d := by
      simpa using Nat.mul_le_mul_left (L+4) (show 1≤2^d by omega)
    have hprod : (L+4)*2^d=2*(((L+4)/2)*2^d) := by
      rw [←Nat.mul_assoc,show 2*((L+4)/2)=L+4 by omega]
    have hK : 4≤K := by omega
    have h4 : K%4=0 := by omega
    let K' := (K-4)/2
    let C' := C+K+1
    have hp' : (L+4)*2^d=K'+4 := by dsimp [K']; omega
    have hs' : D+2*L+3*d=C'+2*K' := by dsimp [K',C']; omega
    obtain ⟨n,w,hw,hn,ht⟩ := ih K' C' (by dsimp [C']; omega) hp' hs'
    obtain ⟨v,hv,hv'⟩ := recursive_counted K C hK h4 hc
    refine ⟨n+(K-1),w+v,hw.append hv,?_,?_⟩
    · dsimp [K'] at hn; omega
    · change 3*v+51+8*(K'+4)*(K'+4)+39*(K+4)=8*(K+4)*(K+4)+39*(K'+4) at hv'
      omega

/-- The exact terminal wing, from the thin gateway to the first c=2 state. -/
theorem thin_tail_counted (j : Nat) :
    Path (4*j+4) (32*j*j+122*j+100) (0,2*j,4*j+10) (8*j+10,2,2) := by
  have h1 : nextC (0,2*j,4*j+10)=some (4*j+2,2,5+(4*j+2)) := by
    rw [show 4*j+10=(4*j+6)+4 by omega]
    simp only [nextC]
    split <;> simp only [Option.some.injEq,Prod.mk.injEq,true_and] <;> omega
  have h2 : nextC (0,4*j+4,5)=some (8*j+10,2,2) := by
    simp only [nextC]
    split <;> simp only [Option.some.injEq,Prod.mk.injEq,and_true] <;> omega
  have hh := Path.cons h1 (drain_counted 5 (4*j+2) 2 (by decide))
  rw [show 2+(4*j+2)=4*j+4 by omega] at hh
  have ht := hh.append (Path.cons h2 (Path.nil _))
  have hw1 : weight (0,2*j,4*j+10)=10*j+21 := by
    rw [show 4*j+10=(4*j+6)+4 by omega]
    simp only [weight]
    split <;> omega
  have hw2 : weight (0,4*j+4,5)=20*j+41 := by
    simp only [weight]
    split <;> omega
  rw [hw1,hw2] at ht
  have hcost : 10*j+21+(2*(4*j+2)*(4*j+2)+(4*2+7)*(4*j+2))+(20*j+41+0)=32*j*j+122*j+100 := by
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc]
    simp only [Nat.mul_left_comm j, ←Nat.mul_assoc]
    simp only [Nat.mul_assoc]
    omega
  rwa [hcost,show 4*j+2+1+(0+1)=4*j+4 by omega] at ht

/-- High stopping family: the entire suffix, from the c=0 state to the
    first c=2 state, with the exact number of accelerator calls and a
    telescoping identity for its total rule weight. -/
theorem high_stop_counted (j m q k : Nat)
    (hj : j+2=2^(2*m)*(q+3)) (hk : k+q+3*m+5=4*(j+2)) :
    ∃ n w, Path n w (2*q+3,k,0) (8*j+10,2,2) ∧
      n+2*q+10*m=8*j+2 ∧
      3*w+21+102*m+8*(2*q+6)*(2*q+6)+39*(2*j+4)=
      3*(2*(2*q+2)*(2*q+2)+8*(2*q+2)+(2*k-2*q))+
        8*(2*j+4)*(2*j+4)+39*(2*q+6)+3*(32*j*j+122*j+100) := by
  -- Use the explicit parameters to avoid any existential witness ambiguity.
  have hpow : m+1≤2^(2*m) := by
    have hh : ∀ n : Nat, n+1≤2^n := by
      intro n; induction n with
      | zero => decide
      | succ n ih => rw [Nat.pow_succ]; omega
    exact Nat.le_trans (hh m) (Nat.pow_le_pow_right (by decide) (by omega))
  have hmul := Nat.mul_le_mul_right (q+3) hpow
  rw [←hj,Nat.add_mul] at hmul
  have h3m : 3*m≤m*(q+3) := by
    rw [Nat.mul_comm 3 m]; exact Nat.mul_le_mul_left m (by omega)
  have hb : q+2≤k := by omega
  have hp : (2*q+2+4)*2^(2*m)=2*j+4 := by
    rw [show 2*q+2+4=2*(q+3) by omega,Nat.mul_assoc,Nat.mul_comm (q+3),←hj]; omega
  obtain ⟨n,w,hpath,hn,hw⟩ := fan_counted (2*j) (4*j+10) (2*q+2) (2*k-2*q) (2*m) (by omega) (by omega) hp (by omega)
  obtain ⟨v,hv,hv'⟩ := high_entry_counted (2*q+2) (2*k-2*q) (by omega) (by omega) (by omega) (by omega)
  rw [show 2*q+2+1=2*q+3 by omega,show (2*k-2*q+(2*q+2)-2)/2=k by omega] at hv
  refine ⟨_,_,(hv.append hpath).append (thin_tail_counted j),by omega,?_⟩
  simp only [show 2*q+2+4=2*q+6 by omega] at hw
  omega

/-- Exceptional low stopping family, with the exact same quantitative
    terminal certificate. -/
theorem low_stop_counted (j m k : Nat) (hm : 1≤m)
    (hj : j+2=2^(2*m+1)) (hk : k+3*m+4=4*(j+2)) :
    ∃ n w, Path n w (1,k,0) (8*j+10,2,2) ∧
      n+10*m=8*j+4 ∧
      3*w+51*(2*m-1)+8*8*8+39*(2*j+4)=
      3*(2*k-3+57)+8*(2*j+4)*(2*j+4)+39*8+3*(32*j*j+122*j+100) := by
  have hpow : ∀ n : Nat, n+1≤2^n := by
    intro n; induction n with
    | zero => decide
    | succ n ih => rw [Nat.pow_succ]; omega
  have h := hpow (2*m+1)
  rw [←hj] at h
  have hb : 4≤k := by omega
  have hp : (4+4)*2^(2*m-1)=2*j+4 := by
    rw [show 2*m+1=(2*m-1)+2 by omega,Nat.pow_add] at hj
    simp only [show (2:Nat)^2=4 by decide] at hj
    omega
  obtain ⟨n,w,hpath,hn,hw⟩ := fan_counted (2*j) (4*j+10) 4 (2*k-3) (2*m-1) (by decide) (by omega) hp (by omega)
  have hv := low_entry_counted (2*k-3) (by omega) (by omega)
  rw [show (2*k-3+3)/2=k by omega] at hv
  refine ⟨_,_,(hv.append hpath).append (thin_tail_counted j),by omega,?_⟩
  omega

#print axioms fan_counted
#print axioms thin_tail_counted
#print axioms high_stop_counted
#print axioms low_stop_counted

/-- A deterministic successful path ending in a stopping state has unique
    length, weight and endpoint among all paths to a stopping state. -/
theorem Path.terminal_unique {n w s t} (p : Path n w s t) (ht : nextC t=none)
    {m v u} (q : Path m v s u) (hu : nextC u=none) : n=m ∧ w=v ∧ t=u := by
  induction p generalizing m v u with
  | nil =>
    cases q with
    | nil => exact ⟨rfl,rfl,rfl⟩
    | cons h _ => rw [ht] at h; contradiction
  | cons h p ih =>
    cases q with
    | nil => rw [hu] at h; contradiction
    | cons h' q =>
      rw [h] at h'
      have he := Option.some.inj h'
      subst_vars
      obtain ⟨hn,hw,hu'⟩ := ih ht q hu
      subst_vars
      exact ⟨rfl,rfl,rfl⟩

#print axioms Path.terminal_unique
end BB6.Agent47ThinCounted
