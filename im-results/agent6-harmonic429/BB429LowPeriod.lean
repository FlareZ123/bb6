import BB429LowEvenTerminal

namespace BB429.LowPeriod
open LowGeneral
set_option maxHeartbeats 2000000

private theorem odd_coprime_two (n : Nat) (h : n%2=1) : Nat.Coprime 2 n := by
  change Nat.gcd 2 n=1
  rw [Nat.gcd_rec,h]
  decide

private theorem nonthree_coprime (n : Nat) (h : n%3≠0) : Nat.Coprime 3 n := by
  change Nat.gcd 3 n=1
  rw [Nat.gcd_rec]
  have hh := Nat.mod_lt n (by decide : 0<3)
  by_cases h1 : n%3=1
  · rw [h1]; decide
  · rw [show n%3=2 by omega]; decide

/-- The coefficient L-3 is invertible modulo L*K+1 whenever 3K+1
    is a power of two and L is divisible by four. -/
theorem coeff_coprime (L K e : Nat) (hL : 4≤L) (hL4 : L%4=0)
    (hK : 3*K+1=2^e) : Nat.Coprime (L-3) (L*K+1) := by
  have h := congrArg (fun n : Nat => n*K) (show L-3+3=L by omega)
  rw [Nat.add_mul] at h
  have hm : L*K+1=2^e+(L-3)*K := by omega
  change Nat.gcd (L-3) (L*K+1)=1
  rw [hm,Nat.gcd_add_mul_left_right]
  have hc : Nat.Coprime 2 (L-3) := odd_coprime_two _ (by omega)
  exact (hc.pow_left e).symm

private theorem odd_modulus (L K : Nat) (hL4 : L%4=0) : (L*K+1)%2=1 := by
  rw [Nat.add_mod,Nat.mul_mod]
  have hL : L%2=0 := by omega
  rw [hL]
  simp

private theorem c24_coprime (M : Nat) (hodd : M%2=1) (h3 : M%3≠0) : Nat.Coprime 24 M := by
  have h8 : Nat.Coprime 8 M := (odd_coprime_two M hodd).pow_left 3
  have h3c := nonthree_coprime M h3
  exact h3c.mul_left h8

/-- Exact cancellation of a coprime multiplier in natural congruences. -/
theorem cancel_mod (A M x y : Nat) (hc : Nat.Coprime A M)
    (h : (A*x)%M=(A*y)%M) : x%M=y%M := by
  suffices haux : ∀ x y, y≤x → (A*x)%M=(A*y)%M → x%M=y%M by
    by_cases hle : y≤x
    · exact haux x y hle h
    · exact (haux y x (by omega) h.symm).symm
  intro x y hle he
  obtain ⟨k1,k2,hk⟩ := Nat.mod_eq_mod_iff.mp he
  have hmul : A*y≤A*x := Nat.mul_le_mul_left A hle
  have h1 : k1*M≤k2*M := by omega
  have h2 : A*(x-y)=(k2-k1)*M := by
    rw [Nat.mul_sub_left_distrib,Nat.mul_sub_right_distrib]
    omega
  have hd : M∣A*(x-y) := ⟨k2-k1,by rw [h2,Nat.mul_comm]⟩
  obtain ⟨q,hq⟩ := hc.symm.dvd_of_dvd_mul_left hd
  apply Nat.mod_eq_mod_iff.mpr
  refine ⟨0,q,?_⟩
  rw [Nat.zero_mul,Nat.add_zero,Nat.mul_comm q M]
  omega

private theorem cancel_add (M x y b : Nat)
    (h : (x+b)%M=(y+b)%M) : x%M=y%M := by
  obtain ⟨k1,k2,hk⟩ := Nat.mod_eq_mod_iff.mp h
  exact Nat.mod_eq_mod_iff.mpr ⟨k1,k2,by omega⟩

private theorem pow_mod3 (t : Nat) (ht : t%2=0) : 2^t%3=1 := by
  have he : t=2*(t/2) := by omega
  rw [he,Nat.pow_mul,Nat.pow_mod]; simp

/-- All odd-pair terminal witnesses have modulus coprime to 3.
    This follows from the excluded j=2 mod 3 family. -/
theorem odd_terminal_coprime3 (m j t : Nat) (h : LowGeneral.TerminalHalt m j t) :
    LowGeneral.modulus j t%3≠0 := by
  have ht := (LowGeneral.modular_necessary m j t h).1
  have hP := pow_mod3 t (by omega)
  have hj : j%3≠2 := fun he => LowGeneral.no_two_mod3 m j t he h
  have hQ := LowGeneral.pow16_mod9 j
  have hK := LowGeneral.geom_eq j
  have hK9 := congrArg (fun n : Nat => n%9) hK
  rw [Nat.add_mod (3*LowGeneral.geom j),Nat.mul_mod 3 (LowGeneral.geom j),Nat.mul_mod 4 (16^j)] at hK9
  have hKmod : LowGeneral.geom j%9%3=LowGeneral.geom j%3 := Nat.mod_mod_of_dvd _ (by decide : 3∣9)
  have hK3 : LowGeneral.geom j%3≠2 := by
    have hlt := Nat.mod_lt j (by decide : 0<3)
    by_cases h0 : j%3=0
    · rw [h0] at hQ
      change 16^j%9=1 at hQ
      rw [hQ] at hK9
      omega
    · have h1 : j%3=1 := by omega
      rw [h1] at hQ
      change 16^j%9=7 at hQ
      rw [hQ] at hK9
      omega
  intro hz
  have h4P : (4*2^t)%3=1 := by omega
  unfold LowGeneral.modulus at hz
  rw [Nat.add_mod,Nat.mul_mod,h4P] at hz
  omega

/-- Direct-F terminal case excludes j=1 mod 3, and its remaining moduli
    are also coprime to 3. -/
theorem even_terminal_coprime3 (m j t : Nat) (h : LowEvenTerminal.TerminalHalt m j t) :
    LowEvenTerminal.modulus j t%3≠0 := by
  obtain ⟨ht,hmod⟩ := LowEvenTerminal.modular_necessary m j t h
  have hP := pow_mod3 t (by omega)
  have h4P : (4*2^t)%3=1 := by omega
  intro hz
  have hK3 : LowEvenTerminal.geom j%3=2 := by
    unfold LowEvenTerminal.modulus at hz
    rw [Nat.add_mod,Nat.mul_mod,h4P] at hz
    omega
  have hK := LowEvenTerminal.geom_eq j
  have hK9 := congrArg (fun n : Nat => n%9) hK
  rw [Nat.add_mod (3*LowEvenTerminal.geom j),Nat.mul_mod 3 (LowEvenTerminal.geom j)] at hK9
  have hKmod : LowEvenTerminal.geom j%9%3=LowEvenTerminal.geom j%3 := Nat.mod_mod_of_dvd _ (by decide : 3∣9)
  have hQ := LowGeneral.pow16_mod9 j
  have hj1 : j%3=1 := by
    have hlt := Nat.mod_lt j (by decide : 0<3)
    by_cases h0 : j%3=0
    · rw [h0] at hQ
      change 16^j%9=1 at hQ
      omega
    · by_cases h2 : j%3=2
      · rw [h2] at hQ
        change 16^j%9=4 at hQ
        omega
      · omega
  obtain ⟨d,v,hp⟩ := (LowEvenTerminal.terminal_parameters m j t).mp h
  have he := LowEvenTerminal.parameter_equation m j t d v hp
  have hm := congrArg (fun n : Nat => n%3) he
  rw [Nat.add_mod,Nat.mul_mod (LowEvenTerminal.modulus j t),hz,Nat.mul_mod (4*2^t),h4P] at hm
  unfold LowEvenTerminal.total LowEvenTerminal.offset at hm
  omega

/-- For fixed phase, cycle count and terminal length, two halting scales
    necessarily have identical powers of 16 modulo the phase modulus. -/
theorem same_power (L K M C0 H m n : Nat) (hL : 4≤L) (hL4 : L%4=0)
    (hM : M=L*K+1) (h3 : M%3≠0) (hK : ∃ e, 3*K+1=2^e)
    (hm : ((L-3)*(24*16^m+C0))%M=H%M)
    (hn : ((L-3)*(24*16^n+C0))%M=H%M) : 16^m%M=16^n%M := by
  obtain ⟨e,he⟩ := hK
  have hcoef : Nat.Coprime (L-3) M := hM ▸ coeff_coprime L K e hL hL4 he
  have hodd : M%2=1 := by rw [hM]; exact odd_modulus L K hL4
  have h24 := c24_coprime M hodd h3
  have h1 := cancel_mod (L-3) M _ _ hcoef (hm.trans hn.symm)
  have h2 := cancel_add M _ _ C0 h1
  exact cancel_mod 24 M _ _ h24 h2

/-- A finite pigeonhole proof supplies a positive period at most M.
    Coprime cancellation ensures it is a period of the initial power 1. -/
theorem period_exists (M : Nat) (hM : 1<M) (hc : Nat.Coprime 16 M) :
    ∃ p, 0<p ∧ p≤M ∧ 16^p%M=1 := by
  let xs := (List.range (M+1)).map (fun i => 16^i%M)
  have hsub : xs⊆List.range M := by
    intro x hx
    obtain ⟨i,hi,hx'⟩ := List.mem_map.mp hx
    rw [← hx',List.mem_range]
    exact Nat.mod_lt _ (by omega)
  have hlen : xs.length=M+1 := by simp [xs]
  have hdup : ¬xs.Nodup := by
    intro hn
    have hh := hn.length_le_of_subset hsub
    rw [hlen,List.length_range] at hh
    omega
  have hcoll : ∃ i j, i<j ∧ j≤M ∧ 16^i%M=16^j%M := by
    classical
    by_cases h : ∃ i j, i<j ∧ j≤M ∧ 16^i%M=16^j%M
    · exact h
    · exfalso
      apply hdup
      apply List.nodup_iff_eq_of_getElem_eq.mpr
      intro i j hi hj he
      have hi' : i≤M := by omega
      have hj' : j≤M := by omega
      have hpow : 16^i%M=16^j%M := by simpa [xs] using he
      by_cases hij : i=j
      · exact hij
      · by_cases hlt : i<j
        · exact False.elim (h ⟨i,j,hlt,hj',hpow⟩)
        · exact False.elim (h ⟨j,i,by omega,hi',hpow.symm⟩)
  obtain ⟨i,j,hij,hj,he⟩ := hcoll
  let p := j-i
  have hpow : 16^j=16^i*16^p := by rw [← Nat.pow_add,show i+p=j by dsimp [p]; omega]
  rw [hpow] at he
  have he' : (16^i*1)%M=(16^i*16^p)%M := by simpa using he
  have hperiod := cancel_mod (16^i) M 1 (16^p) (hc.pow_left i) he'
  rw [Nat.mod_eq_of_lt hM] at hperiod
  exact ⟨p,by dsimp [p]; omega,by dsimp [p]; omega,hperiod.symm⟩

/-- Every power reduces to the remainder exponent of a positive period. -/
theorem reduce_power (M p m : Nat) (hM : 1<M) (hp : 0<p)
    (hperiod : 16^p%M=1) : 16^m%M=16^(m%p)%M := by
  let q := m/p
  let r := m%p
  have he : m=r+p*q := (Nat.mod_add_div m p).symm
  have hpw : 16^m=16^r*(16^p)^q := by conv => lhs; rw [he,Nat.pow_add,Nat.pow_mul]
  rw [hpw,Nat.mul_mod,Nat.pow_mod (16^p),hperiod]
  simp [Nat.mod_eq_of_lt hM]
  rfl

/-- A minimal positive period gives unique discrete-log residues. -/
theorem unique_exponent (M p m n : Nat) (hM : 1<M) (hp : 0<p)
    (hc : Nat.Coprime 16 M) (hperiod : 16^p%M=1)
    (hmin : ∀ q, 0<q → q<p → 16^q%M≠1)
    (he : 16^m%M=16^n%M) : m%p=n%p := by
  rw [reduce_power M p m hM hp hperiod,reduce_power M p n hM hp hperiod] at he
  let a := m%p
  let b := n%p
  have ha : a<p := Nat.mod_lt _ hp
  have hb : b<p := Nat.mod_lt _ hp
  suffices haux : ∀ a b, a<p → b<p → a<b → 16^a%M=16^b%M → False by
    by_cases hh : a=b
    · exact hh
    · by_cases hl : a<b
      · exact False.elim (haux a b ha hb hl he)
      · exact False.elim (haux b a hb ha (by omega) he.symm)
  intro x y hx hy hxy hpow
  let q := y-x
  have hpw : 16^y=16^x*16^q := by rw [← Nat.pow_add,show x+q=y by dsimp [q]; omega]
  rw [hpw] at hpow
  have h1 : (16^x*1)%M=(16^x*16^q)%M := by simpa using hpow
  have hq := cancel_mod (16^x) M 1 (16^q) (hc.pow_left x) h1
  rw [Nat.mod_eq_of_lt hM] at hq
  exact hmin q (by dsimp [q]; omega) (by dsimp [q]; omega) hq.symm

/-- Choose a least period without any external number theory library. -/
theorem least_period (M : Nat) (hM : 1<M) (hc : Nat.Coprime 16 M) :
    ∃ p, 0<p ∧ p≤M ∧ 16^p%M=1 ∧ ∀ q, 0<q → q<p → 16^q%M≠1 := by
  obtain ⟨n,hn,hnM,hnp⟩ := period_exists M hM hc
  suffices h : ∀ n, 0<n → n≤M → 16^n%M=1 →
      ∃ p, 0<p ∧ p≤M ∧ 16^p%M=1 ∧ ∀ q, 0<q → q<p → 16^q%M≠1 by
    exact h n hn hnM hnp
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn hnM hnp
    classical
    by_cases h : ∃ q, 0<q ∧ q<n ∧ 16^q%M=1
    · obtain ⟨q,hq,hqn,hqp⟩ := h
      exact ih q hqn hq (by omega) hqp
    · exact ⟨n,hn,hnM,hnp,fun q hq hqn hp => h ⟨q,hq,hqn,hp⟩⟩

private theorem test_same_power (L C0 M m n : Nat) (h : 16^m%M=16^n%M) :
    ((L-3)*(24*16^m+C0))%M=((L-3)*(24*16^n+C0))%M := by
  have h1 : (24*16^m)%M=(24*16^n)%M := by
    rw [Nat.mul_mod 24 (16^m),Nat.mul_mod 24 (16^n),h]
  have h2 : (24*16^m+C0)%M=(24*16^n+C0)%M := by
    rw [Nat.add_mod (24*16^m),Nat.add_mod (24*16^n),h1]
  rw [Nat.mul_mod (L-3) (24*16^m+C0),Nat.mul_mod (L-3) (24*16^n+C0),h2]

/-- Given any one witness, every possible scale is in a unique residue
    modulo the multiplicative order of 16, and all sufficiently large
    scales in that residue are witnesses. -/
theorem progression_of_witness (P : Nat → Prop) (L K M C0 H m0 : Nat)
    (hL : 4≤L) (hL4 : L%4=0) (hM : M=L*K+1) (hM1 : 1<M)
    (h3 : M%3≠0) (hK : ∃ e, 3*K+1=2^e)
    (h0 : P m0)
    (hnec : ∀ m, P m → ((L-3)*(24*16^m+C0))%M=H%M)
    (hsuff : ∀ m, M*(H+28)≤24*16^m+C0 →
       ((L-3)*(24*16^m+C0))%M=H%M → P m) :
    ∃ p r, 0<p ∧ p≤M ∧ r<p ∧
      (∀ m, P m → m%p=r) ∧
      (∀ m, M*(H+28)≤24*16^m+C0 → (P m ↔ m%p=r)) := by
  have hodd : M%2=1 := by rw [hM]; exact odd_modulus L K hL4
  have hc : Nat.Coprime 16 M := (odd_coprime_two M hodd).pow_left 4
  obtain ⟨p,hp,hpM,hperiod,hmin⟩ := least_period M hM1 hc
  let r := m0%p
  have hr : r<p := Nat.mod_lt _ hp
  have hnec' : ∀ m, P m → m%p=r := by
    intro m hm
    have hpow := same_power L K M C0 H m m0 hL hL4 hM h3 hK (hnec m hm) (hnec m0 h0)
    exact unique_exponent M p m m0 hM1 hp hc hperiod hmin hpow
  refine ⟨p,r,hp,hpM,hr,hnec',?_⟩
  intro m hlarge
  refine ⟨hnec' m,?_⟩
  intro hm
  have hpw : 16^m%M=16^m0%M := by
    rw [reduce_power M p m hM1 hp hperiod,reduce_power M p m0 hM1 hp hperiod,hm]
  exact hsuff m hlarge ((test_same_power L C0 M m m0 hpw).trans (hnec m0 h0))

/-- Fixed odd-pair word: no scale, or one arithmetic progression beyond
    the explicit size threshold. This is an all-scale theorem. -/
theorem odd_progression (j t : Nat) :
    (∀ m, ¬LowGeneral.TerminalHalt m j t) ∨
    ∃ p r, 0<p ∧ p≤LowGeneral.modulus j t ∧ r<p ∧
      (∀ m, LowGeneral.TerminalHalt m j t → m%p=r) ∧
      (∀ m, LowGeneral.modulus j t*(LowGeneral.offset t+28)≤LowGeneral.total m j →
        (LowGeneral.TerminalHalt m j t ↔ m%p=r)) := by
  classical
  by_cases he : ∃ m, LowGeneral.TerminalHalt m j t
  · obtain ⟨m0,h0⟩ := he
    right
    have ht := (LowGeneral.modular_necessary m0 j t h0).1
    have h3 := odd_terminal_coprime3 m0 j t h0
    have hL : 4≤4*2^t := by have h : 0<2^t := Nat.pow_pos (by decide); omega
    have hM : 1<LowGeneral.modulus j t := by
      have h := LowGeneral.modulus_ge j t
      omega
    have hk : 3*LowGeneral.geom j+1=2^(4*j+2) := by
      rw [LowGeneral.geom_eq,Nat.pow_add,Nat.pow_mul]
      change 4*16^j=16^j*4
      exact Nat.mul_comm _ _
    exact progression_of_witness (fun m => LowGeneral.TerminalHalt m j t)
      (4*2^t) (LowGeneral.geom j) (LowGeneral.modulus j t) (8*j+6) (LowGeneral.offset t) m0
      hL (by omega) rfl hM h3 ⟨4*j+2,hk⟩ h0
      (fun m hm => by
        have h := (LowGeneral.modular_necessary m j t hm).2
        simpa only [LowGeneral.coefficient,LowGeneral.total,Nat.add_assoc] using h)
      (fun m hlarge hm => LowGeneral.modular_sufficient m j t
        (by simpa only [LowGeneral.total,Nat.add_assoc] using hlarge) ht
        (by simpa only [LowGeneral.coefficient,LowGeneral.total,Nat.add_assoc] using hm))
  · left
    intro m hm
    exact he ⟨m,hm⟩

/-- Fixed even-pair word: no scale, or one arithmetic progression beyond
    the explicit size threshold. Requires at least one full cycle. -/
theorem even_progression (j t : Nat) (hj : 1≤j) :
    (∀ m, ¬LowEvenTerminal.TerminalHalt m j t) ∨
    ∃ p r, 0<p ∧ p≤LowEvenTerminal.modulus j t ∧ r<p ∧
      (∀ m, LowEvenTerminal.TerminalHalt m j t → m%p=r) ∧
      (∀ m, LowEvenTerminal.modulus j t*(LowEvenTerminal.offset t+28)≤LowEvenTerminal.total m j →
        (LowEvenTerminal.TerminalHalt m j t ↔ m%p=r)) := by
  classical
  by_cases he : ∃ m, LowEvenTerminal.TerminalHalt m j t
  · obtain ⟨m0,h0⟩ := he
    right
    have ht := (LowEvenTerminal.modular_necessary m0 j t h0).1
    have h3 := even_terminal_coprime3 m0 j t h0
    have hL : 4≤4*2^t := by have h : 0<2^t := Nat.pow_pos (by decide); omega
    have hK : 0<LowEvenTerminal.geom j := by
      have h := LowEvenTerminal.geom_eq j
      have hp := Nat.pow_le_pow_right (n:=16) (by decide) hj
      omega
    have hM : 1<LowEvenTerminal.modulus j t := by
      unfold LowEvenTerminal.modulus
      have h := Nat.le_mul_of_pos_right (4*2^t) hK
      omega
    have hk : 3*LowEvenTerminal.geom j+1=2^(4*j) := by
      rw [LowEvenTerminal.geom_eq,Nat.pow_mul]
    exact progression_of_witness (fun m => LowEvenTerminal.TerminalHalt m j t)
      (4*2^t) (LowEvenTerminal.geom j) (LowEvenTerminal.modulus j t) (8*j) (LowEvenTerminal.offset t) m0
      hL (by omega) rfl hM h3 ⟨4*j,hk⟩ h0
      (fun m hm => (LowEvenTerminal.modular_necessary m j t hm).2)
      (fun m hlarge hm => (LowEvenTerminal.modular_classification m j t hj hlarge).mpr ⟨ht,hm⟩)
  · left
    intro m hm
    exact he ⟨m,hm⟩

#print axioms same_power
#print axioms period_exists
#print axioms unique_exponent
#print axioms odd_progression
#print axioms even_progression
end BB429.LowPeriod
