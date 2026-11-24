import Std

/- Arithmetic acceleration of BB(6) holdout F119 / upstream #417.
   The State and next definition below are transcribed from
   google-deepmind/cryptids, commit 3647718b5df22e1a61462dec0376bd204526285a,
   BusyBeaver/BB6/M_1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_HHH1LB.lean
   (Copyright 2026 Google LLC, Apache-2.0). The subsequent proofs are new. -/
namespace F119

inductive State where
  | D (a b c : Nat)
  deriving DecidableEq, Repr

open State

def next : State → Option State
  | .D _ 0 0 => none
  | .D a 0 1 => some (.D 0 (a + 3) 1)
  | .D a 0 2 => some (.D 0 (a + 2) 2)
  | .D a 0 (c + 3) => some (.D (a + 3) 0 c)
  | .D a 1 0 => some (.D (a + 1) 0 1)
  | .D a 1 (c + 1) => some (.D (a + 1) 1 c)
  | .D a 2 c => some (.D 0 a (c + 3))
  | .D a (b + 3) 0 =>
    if b % 3 = 0 then none
    else if b % 3 = 1 then some (.D (a + 1) (b + 2) 1)
    else some (.D (a + 1) b 2)
  | .D a (b + 3) (c + 1) =>
    if b % 3 = 0 then some (.D (a + 1) (b + 1) (c + 2))
    else if b % 3 = 1 then some (.D (a + 1) (b + 3) c)
    else some (.D (a + 1) b (c + 3))

inductive Steps : Nat → State → State → Prop
  | nil (s) : Steps 0 s s
  | cons {n s t u} : next s = some t → Steps n t u → Steps (n + 1) s u

theorem Steps.trans {n m s t u} (h : Steps n s t) (g : Steps m t u) :
    Steps (n + m) s u := by
  induction h with
  | nil => simpa using g
  | @cons n s t v hn _ ih =>
    have hh := Steps.cons hn (ih g)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

def Reach (s t : State) : Prop := ∃ n, Steps n s t
def Progress (s t : State) : Prop := ∃ n, 0 < n ∧ Steps n s t

theorem Reach.refl (s : State) : Reach s s := ⟨0, .nil s⟩
theorem Reach.trans {s t u} (h : Reach s t) (g : Reach t u) : Reach s u := by
  obtain ⟨n, hn⟩ := h; obtain ⟨m, hm⟩ := g
  exact ⟨n+m, hn.trans hm⟩
theorem Reach.single {s t} (h : next s = some t) : Reach s t :=
  ⟨1, .cons h (.nil t)⟩
theorem Progress.single {s t} (h : next s = some t) : Progress s t :=
  ⟨1, by decide, .cons h (.nil t)⟩
theorem Reach.progress {s t u} (h : Reach s t) (g : Progress t u) : Progress s u := by
  obtain ⟨n, hn⟩ := h; obtain ⟨m, hp, hm⟩ := g
  exact ⟨n+m, by omega, hn.trans hm⟩
theorem Progress.reach {s t u} (h : Progress s t) (g : Reach t u) : Progress s u := by
  obtain ⟨n, hp, hn⟩ := h; obtain ⟨m, hm⟩ := g
  exact ⟨n+m, by omega, hn.trans hm⟩

inductive Stops : Nat → State → Prop
  | now {s} : next s = none → Stops 0 s
  | later {n s t} : next s = some t → Stops n t → Stops (n+1) s

def Halts (s : State) : Prop := ∃ n, Stops n s

theorem Steps.stop_back {n m s t} (h : Steps n s t) (g : Stops m t) : Stops (n+m) s := by
  induction h with
  | nil => simpa using g
  | cons hn _ ih =>
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Stops.later hn (ih g)

theorem Steps.stop_forward {n m s t} (h : Steps n s t) (g : Stops m s) :
    ∃ k, m = n+k ∧ Stops k t := by
  induction h generalizing m with
  | nil => exact ⟨m, by simp, g⟩
  | @cons n s t u hn _ ih =>
    cases g with
    | now he => rw [hn] at he; contradiction
    | @later k _ v he hg =>
      have eq : t = v := Option.some.inj (hn.symm.trans he)
      subst v
      obtain ⟨j,hj,hs⟩ := ih hg
      exact ⟨j, by omega, hs⟩

theorem Reach.halts_iff {s t} (h : Reach s t) : Halts s ↔ Halts t := by
  obtain ⟨n,hn⟩ := h
  constructor
  · rintro ⟨m,hm⟩
    obtain ⟨k,_,hk⟩ := hn.stop_forward hm
    exact ⟨k,hk⟩
  · rintro ⟨m,hm⟩
    exact ⟨n+m,hn.stop_back hm⟩

-- Sweep over the b ≡ 2 mod 3 branch.
theorem strip_twos (a k c : Nat) (hc : 0 < c) :
    Progress (D a (3*k+2) c) (D 0 (a+k) (c+2*k+3)) := by
  induction k generalizing a c with
  | zero => apply Progress.single; simp [next]
  | succ k ih =>
    have hn : next (D a (3*(k+1)+2) c) = some (D (a+1) (3*k+2) (c+2)) := by
      obtain ⟨c', rfl⟩ : ∃ c', c = c'+1 := ⟨c-1, by omega⟩
      have hb : 3*(k+1)+2 = (3*k+2)+3 := by omega
      rw [hb]
      simp [next]
    obtain ⟨n,hp,hs⟩ := ih (a+1) (c+2) (by omega)
    refine ⟨n+1, by omega, .cons hn ?_⟩
    rw [show a+(k+1)=a+1+k by omega, show c+2*(k+1)+3=c+2+2*k+3 by omega]
    exact hs

-- b ≡ 1: consume c; then move to b ≡ 0 with c = 1.
theorem consume_one (a k c : Nat) : Reach (D a (3*k+1) c) (D (a+c) (3*k+1) 0) := by
  induction c generalizing a with
  | zero => simpa using Reach.refl (D a (3*k+1) 0)
  | succ c ih =>
    have hn : next (D a (3*k+1) (c+1)) = some (D (a+1) (3*k+1) c) := by
      cases k with
      | zero => rfl
      | succ k =>
        have hb : 3*(k+1)+1 = (3*k+1)+3 := by omega
        rw [hb]
        simp [next, show (3*k+1)%3 = 1 by omega]
    have h := (Reach.single hn).trans (ih (a+1))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem finish_one (a k : Nat) : next (D a (3*k+1) 0) = some (D (a+1) (3*k) 1) := by
  cases k with
  | zero => rfl
  | succ k =>
    have hb : 3*(k+1)+1 = (3*k+1)+3 := by omega
    rw [hb]
    simp [next, show (3*k+1)%3 = 1 by omega]
    rw [show 3*k+1+2=3*(k+1) by omega]

theorem collapse_three (a k c : Nat) (hc : 0 < c) :
    Reach (D a (3*(k+1)) c) (D (a+c+3) (3*k) 1) := by
  have hn : next (D a (3*(k+1)) c) = some (D (a+1) (3*k+1) (c+1)) := by
    obtain ⟨c',rfl⟩ : ∃ c', c = c'+1 := ⟨c-1, by omega⟩
    have hb : 3*(k+1) = (3*k)+3 := by omega
    rw [hb]
    simp [next, show (3*k)%3 = 0 by omega]
  have h := (Reach.single hn).trans ((consume_one (a+1) k (c+1)).trans
    (Reach.single (finish_one (a+1+(c+1)) k)))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, show 1+1+1=3 by decide] using h

theorem collapse_multiples (a k : Nat) : Reach (D a (3*k) 1) (D (a+4*k) 0 1) := by
  induction k generalizing a with
  | zero => simpa using Reach.refl (D a 0 1)
  | succ k ih =>
    have h := (collapse_three a k 1 (by decide)).trans (ih (a+1+3))
    rw [show a+4*(k+1)=a+1+3+4*k by omega]
    exact h

theorem transfer_three (a k r : Nat) : Reach (D a 0 (3*k+r)) (D (a+3*k) 0 r) := by
  induction k generalizing a with
  | zero => simpa using Reach.refl (D a 0 r)
  | succ k ih =>
    have hn : next (D a 0 (3*(k+1)+r)) = some (D (a+3) 0 (3*k+r)) := by
      have hb : 3*(k+1)+r = (3*k+r)+3 := by omega
      rw [hb]; rfl
    have h := (Reach.single hn).trans (ih (a+3))
    rw [show a+3*(k+1)=a+3+3*k by omega]
    exact h

-- x = b+1. Strip all factors of 3 while conserving c + x up to +1 per factor.
theorem strip_power (h m c : Nat) (hm : 0 < m) (hc : 0 < c) :
    Reach (D 0 (3^h*m-1) c) (D 0 (m-1) (c+(3^h*m-m)+h)) := by
  induction h generalizing c with
  | zero => simpa using Reach.refl (D 0 (m-1) c)
  | succ h ih =>
    let z := 3^h*m
    have hz : 0 < z := Nat.mul_pos (Nat.pow_pos (by decide)) hm
    have hmz : m ≤ z := by
      have h3 : 0 < 3^h := Nat.pow_pos (by decide)
      exact Nat.le_mul_of_pos_left m h3
    have eq : 3^(h+1)*m = 3*z := by simp [z, Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm]
    rw [eq]
    have hb : 3*z-1 = 3*(z-1)+2 := by omega
    rw [hb]
    obtain ⟨n,_,hn⟩ := strip_twos 0 (z-1) c hc
    have h₁ : Reach (D 0 (3*(z-1)+2) c) (D 0 (z-1) (c+2*z+1)) := by
      refine ⟨n, ?_⟩
      rw [show c+2*z+1=c+2*(z-1)+3 by omega]
      simpa using hn
    have h₂ := ih (c+2*z+1) (by omega)
    change Reach (D 0 (z-1) (c+2*z+1)) (D 0 (m-1) ((c+2*z+1)+(z-m)+h)) at h₂
    have hh := h₁.trans h₂
    rw [show c+(3*z-m)+(h+1)=(c+2*z+1)+(z-m)+h by omega]
    exact hh

-- A compressed section is parametrized by x=b+1 and c∈{1,2}.
def sec (x c : Nat) : State := D 0 (x-1) c

theorem generic_one (x c h t : Nat) (hc : 0 < c) (ht : 0 < t)
    (hx : x = 3^h * (3*t+1)) : Progress (sec x c) (sec (x+c+h+t+2) 1) := by
  have hs := strip_power h (3*t+1) c (by omega) hc
  rw [← hx] at hs
  have hx0 : 3*t+1 ≤ x := by
    rw [hx]; exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
  let C := c+(x-(3*t+1))+h
  have hC : 0 < C := by dsimp [C]; omega
  have hs' : Reach (sec x c) (D 0 (3*t) C) := by
    unfold sec
    rw [← show 3*t+1-1=3*t by omega]
    exact hs
  have h₁ := collapse_three 0 (t-1) C hC
  have h₂ := collapse_multiples (C+3) (t-1)
  have h₃ : Reach (D 0 (3*t) C) (D (C+4*t-1) 0 1) := by
    have h₁' : Reach (D 0 (3*t) C) (D (C+3) (3*(t-1)) 1) := by
      rw [← show 3*(t-1+1)=3*t by omega]
      simpa using h₁
    rw [show C+4*t-1=C+3+4*(t-1) by omega]
    exact h₁'.trans h₂
  have h₄ : Progress (D (C+4*t-1) 0 1) (sec (x+c+h+t+2) 1) := by
    apply Progress.single
    simp [next, sec]
    dsimp [C]; omega
  exact (hs'.trans h₃).progress h₄

theorem generic_two (x c h t : Nat) (hc : 0 < c)
    (hx : x = 3^h * (3*t+2)) : Progress (sec x c) (sec (x+c+h+t+3) 1) := by
  have hs := strip_power h (3*t+2) c (by omega) hc
  rw [← hx] at hs
  have hx0 : 3*t+2 ≤ x := by
    rw [hx]; exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
  let C := c+(x-(3*t+2))+h
  have hs' : Reach (sec x c) (D 0 (3*t+1) C) := by
    unfold sec
    rw [← show 3*t+2-1=3*t+1 by omega]
    exact hs
  have h₁ := (consume_one 0 t C).trans (Reach.single (finish_one (0+C) t))
  have h₂ := collapse_multiples (C+1) t
  have h₃ : Reach (D 0 (3*t+1) C) (D (C+1+4*t) 0 1) := by
    simpa using h₁.trans (by simpa using h₂)
  have h₄ : Progress (D (C+1+4*t) 0 1) (sec (x+c+h+t+3) 1) := by
    apply Progress.single
    simp [next, sec]
    dsimp [C]; omega
  exact (hs'.trans h₃).progress h₄

theorem power_section (h c : Nat) (hc : 0 < c) :
    Reach (sec (3^h) c) (D 0 0 (c+(3^h-1)+h)) := by
  simpa [sec] using strip_power h 1 c (by decide) hc

theorem power_halt (h c : Nat) (hc : 0 < c) (hr : (c+(3^h-1)+h)%3 = 0) :
    Halts (sec (3^h) c) := by
  let C := c+(3^h-1)+h
  have h₁ := power_section h c hc
  have h₂ := transfer_three 0 (C/3) 0
  have h₂' : Reach (D 0 0 C) (D (3*(C/3)) 0 0) := by
    have he : 3*(C/3)+0=C := by dsimp [C] at *; omega
    rw [← he]
    simpa using h₂
  apply (h₁.trans h₂').halts_iff.mpr
  exact ⟨0, .now rfl⟩

theorem power_return (h c r : Nat) (hc : 0 < c) (hr : r=1 ∨ r=2)
    (he : (c+(3^h-1)+h)%3 = r) :
    Progress (sec (3^h) c) (sec (3^h+c+h+4-2*r) r) := by
  let C := c+(3^h-1)+h
  have hpow : 0 < 3^h := Nat.pow_pos (by decide)
  have h₁ := power_section h c hc
  have h₂ := transfer_three 0 (C/3) r
  have h₂' : Reach (D 0 0 C) (D (C-r) 0 r) := by
    have heq : 3*(C/3)+r=C := by dsimp [C] at *; omega
    have heq2 : C-r=0+3*(C/3) := by dsimp [C] at *; omega
    rw [heq, ← heq2] at h₂
    exact h₂
  have h₃ : Progress (D (C-r) 0 r) (sec (3^h+c+h+4-2*r) r) := by
    apply Progress.single
    rcases hr with rfl|rfl <;> simp [next, sec] <;> dsimp [C] at * <;> omega
  exact (h₁.trans h₂').progress h₃


abbrev Section := Nat × Nat

def Valid (s : Section) : Prop := 4 ≤ s.1 ∧ (s.2=1 ∨ s.2=2)

def Terminal (s : Section) : Prop :=
  ∃ h, s.1=3^h ∧ (s.2+(3^h-1)+h)%3=0

inductive Edge : Section → Section → Prop
  | one {x c h t} : 0 < t → x=3^h*(3*t+1) → Edge (x,c) (x+c+h+t+2,1)
  | two {x c h t} : x=3^h*(3*t+2) → Edge (x,c) (x+c+h+t+3,1)
  | power {h c r} : (r=1 ∨ r=2) → (c+(3^h-1)+h)%3=r →
      Edge (3^h,c) (3^h+c+h+4-2*r,r)

theorem edge_progress {s t : Section} (hv : Valid s) (he : Edge s t) :
    Progress (sec s.1 s.2) (sec t.1 t.2) := by
  cases he with
  | one ht hx => exact generic_one _ _ _ _ (by have := hv.2; omega) ht hx
  | two hx => exact generic_two _ _ _ _ (by have := hv.2; omega) hx
  | power hr he => exact power_return _ _ _ (by have := hv.2; omega) hr he

theorem edge_grows {s t : Section} (hv : Valid s) (he : Edge s t) :
    s.1 < t.1 ∧ Valid t := by
  cases he with
  | one ht hx => exact ⟨by simp; omega, by unfold Valid; simp; exact by have := hv.1; simp at this; omega⟩
  | two hx => exact ⟨by simp; omega, by unfold Valid; simp; exact by have := hv.1; simp at this; omega⟩
  | power hr he =>
    have hv1 := hv.1; have hv2 := hv.2
    unfold Valid
    exact ⟨by omega, by omega, hr⟩

theorem terminal_halts {s : Section} (hv : Valid s) (ht : Terminal s) : Halts (sec s.1 s.2) := by
  obtain ⟨h,hx,hr⟩ := ht
  rw [hx]
  exact power_halt h s.2 (by have := hv.2; omega) hr

theorem factor_three (x : Nat) (hx : 0 < x) :
    ∃ h m, x=3^h*m ∧ 0<m ∧ m%3≠0 := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases hz : x%3=0
    · have hq : 0<x/3 := by omega
      have hlt : x/3<x := by omega
      obtain ⟨h,m,he,hm,hn⟩ := ih (x/3) hlt hq
      refine ⟨h+1,m,?_,hm,hn⟩
      have hh : x=3*(x/3) := by omega
      calc
        x = 3*(x/3) := hh
        _ = 3*(3^h*m) := by rw [he]
        _ = 3^(h+1)*m := by simp [Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm]
    · exact ⟨0,x,by simp,hx,hz⟩

theorem terminal_or_edge (s : Section) (hv : Valid s) : Terminal s ∨ ∃ t, Edge s t := by
  rcases s with ⟨x,c⟩
  obtain ⟨h,m,hx,hm,hn⟩ := factor_three x (by have := hv.1; simp at this; omega)
  by_cases h1 : m=1
  · subst m
    simp only [Nat.mul_one] at hx
    subst x
    let r := (c+(3^h-1)+h)%3
    have hr : r<3 := Nat.mod_lt _ (by decide)
    rcases (show r=0 ∨ r=1 ∨ r=2 by omega) with hz|hp|hp
    · exact Or.inl ⟨h,rfl,hz⟩
    · exact Or.inr ⟨(3^h+c+h+4-2*r,r),Edge.power (Or.inl hp) rfl⟩
    · exact Or.inr ⟨(3^h+c+h+4-2*r,r),Edge.power (Or.inr hp) rfl⟩
  · rcases (show m%3=1 ∨ m%3=2 by omega) with h1'|h2'
    · have ht : 0<m/3 := by omega
      have hm' : m=3*(m/3)+1 := by omega
      have he : x=3^h*(3*(m/3)+1) := by rw [← hm']; exact hx
      exact Or.inr ⟨_,Edge.one ht he⟩
    · have hm' : m=3*(m/3)+2 := by omega
      have he : x=3^h*(3*(m/3)+2) := by rw [← hm']; exact hx
      exact Or.inr ⟨_,Edge.two he⟩

inductive MacroHalts : Section → Prop
  | stop {s} : Terminal s → MacroHalts s
  | step {s t} : Edge s t → MacroHalts t → MacroHalts s

theorem macro_sound {s : Section} (hv : Valid s) (hm : MacroHalts s) : Halts (sec s.1 s.2) := by
  induction hm with
  | stop ht => exact terminal_halts hv ht
  | step he _ ih =>
    have h := edge_progress hv he
    obtain ⟨n,_,hs⟩ := h
    exact (Reach.halts_iff ⟨n,hs⟩).mpr (ih (edge_grows hv he).2)

theorem macro_complete (s : Section) (hv : Valid s) (hh : Halts (sec s.1 s.2)) : MacroHalts s := by
  obtain ⟨n,hn⟩ := hh
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    rcases terminal_or_edge s hv with ht|⟨t,he⟩
    · exact .stop ht
    · obtain ⟨k,hk,hs⟩ := edge_progress hv he
      obtain ⟨j,hj,hstop⟩ := hs.stop_forward hn
      exact .step he (ih j (by omega) t (edge_grows hv he).2 hstop)

theorem macro_halts_iff (s : Section) (hv : Valid s) : Halts (sec s.1 s.2) ↔ MacroHalts s :=
  ⟨macro_complete s hv, macro_sound hv⟩

def start : Section := (4,1)

theorem root_halts_iff : Halts (D 0 3 1) ↔ MacroHalts start :=
  macro_halts_iff start (by simp [start, Valid])


-- A power-of-three target has very restricted predecessor valuations.
theorem power_gap (i : Nat) (hi : 2 ≤ i) : 3*(i+3) < 2*3^i := by
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases h : 2 ≤ i
    · have hh := ih h
      rw [Nat.pow_succ]
      omega
    · have he : i=1 := by omega
      subst i; decide

theorem power_residue (i k : Nat) (hi : 2 ≤ i) :
    ∃ j, j ≤ i ∧ (3^k % (3*3^i+1)=3^j ∨ 3^k % (3*3^i+1)=3*3^i+1-3^j) := by
  let M := 3*3^i+1
  have hp : 9 ≤ 3^i := Nat.pow_le_pow_right (n:=3) (by decide) hi
  have hM : 3<M := by dsimp [M]; omega
  induction k with
  | zero => exact ⟨0,by omega,Or.inl (Nat.mod_eq_of_lt (by dsimp [M]; omega))⟩
  | succ k ih =>
    obtain ⟨j,hj,hr⟩ := ih
    have hq : 3^j ≤ 3^i := Nat.pow_le_pow_right (n:=3) (by decide) hj
    have hqpos : 0 < 3^j := Nat.pow_pos (by decide)
    have hnext : 3^(k+1)%M = (3*(3^k%M))%M := by
      rw [Nat.pow_succ, Nat.mul_comm (3^k) 3, Nat.mul_mod, Nat.mod_eq_of_lt hM]
    change 3^k % M = 3^j ∨ 3^k % M = M-3^j at hr
    change ∃ j, j ≤ i ∧ (3^(k+1)%M=3^j ∨ 3^(k+1)%M=M-3^j)
    rw [hnext]
    rcases hr with hr|hr
    · rw [hr, Nat.mod_eq_of_lt (by dsimp [M]; omega)]
      by_cases he : j=i
      · subst j
        exact ⟨0,by omega,Or.inr (by simp [M])⟩
      · exact ⟨j+1,by omega,Or.inl (by rw [Nat.pow_succ, Nat.mul_comm])⟩
    · rw [hr]
      have hh : 3*(M-3^j)=M*2+(M-3*3^j) := by dsimp [M]; omega
      rw [hh, Nat.mul_add_mod, Nat.mod_eq_of_lt (by dsimp [M]; omega)]
      by_cases he : j=i
      · subst j
        exact ⟨0,by omega,Or.inl (by dsimp [M]; simp)⟩
      · exact ⟨j+1,by omega,Or.inr (by rw [Nat.pow_succ, Nat.mul_comm])⟩

theorem generic_one_high_excluded (i k t : Nat) (hi : 2 ≤ i) :
    3^k ≠ 3^i*(3*t+1)+1+i+t+2 := by
  intro he
  let p := 3^i
  let M := 3*p+1
  have hg : 3*(i+3)<2*p := power_gap i hi
  have hsum : 3^k=M*t+(p+i+3) := by
    rw [he]; dsimp [p,M]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_assoc]
    rw [Nat.mul_left_comm (3^i) 3 t]
    omega
  have hmod : 3^k%M=p+i+3 := by
    rw [hsum, Nat.mul_add_mod, Nat.mod_eq_of_lt (by dsimp [M]; omega)]
  obtain ⟨j,hj,hr⟩ := power_residue i k hi
  have hjp : 3^j≤p := Nat.pow_le_pow_right (n:=3) (by decide) hj
  change 3^k%M=3^j ∨ 3^k%M=M-3^j at hr
  rw [hmod] at hr
  dsimp [M] at hr
  omega

theorem generic_two_high_excluded (i k t : Nat) (hi : 2 ≤ i) :
    3^k ≠ 3^i*(3*t+2)+1+i+t+3 := by
  intro he
  let p := 3^i
  let M := 3*p+1
  have hg : 3*(i+3)<2*p := power_gap i hi
  have hsum : 3^k=M*t+(2*p+i+4) := by
    rw [he]; dsimp [p,M]
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    rw [Nat.mul_left_comm (3^i) 3 t, Nat.mul_comm (3^i) 2]
    omega
  have hmod : 3^k%M=2*p+i+4 := by
    rw [hsum, Nat.mul_add_mod, Nat.mod_eq_of_lt (by dsimp [M]; omega)]
  obtain ⟨j,hj,hr⟩ := power_residue i k hi
  have hjp : 3^j≤p := Nat.pow_le_pow_right (n:=3) (by decide) hj
  change 3^k%M=3^j ∨ 3^k%M=M-3^j at hr
  rw [hmod] at hr
  dsimp [M] at hr
  have hjlt : j<i := by
    apply Nat.lt_of_not_ge
    intro h
    have eq : j=i := by omega
    rw [eq] at hr
    change 2*p+i+4=p ∨ 2*p+i+4=3*p+1-p at hr
    omega
  have hjp' : 3^j ≤ 3^(i-1) := Nat.pow_le_pow_right (n:=3) (by decide) (by omega)
  have hpi : p=3*3^(i-1) := by
    have he : i=(i-1)+1 := by omega
    calc
      p = 3^i := rfl
      _ = 3^((i-1)+1) := congrArg (3^·) he
      _ = 3*3^(i-1) := by rw [Nat.pow_succ, Nat.mul_comm]
  omega

theorem pow3_odd (k : Nat) : 3^k%2=1 := by
  rw [Nat.pow_mod]; simp

theorem pow3_mod10 (k : Nat) : 3^k%10 = (if k%4=0 then 1 else if k%4=1 then 3 else if k%4=2 then 9 else 7) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]
    rcases (show k%4=0 ∨ k%4=1 ∨ k%4=2 ∨ k%4=3 by omega) with h|h|h|h <;>
      simp [h, show (k+1)%4=((k%4)+1)%4 by omega]

theorem generic_one_into_power (i k t : Nat) (he : 3^k=3^i*(3*t+1)+1+i+t+2) :
    i=1 ∧ k%4=3 := by
  have hi : i<2 := by
    apply Nat.lt_of_not_ge
    intro h
    exact generic_one_high_excluded i k t (by omega) he
  have hpos : i≠0 := by
    intro hz
    subst i
    have h := pow3_odd k
    simp at he
    omega
  have h1 : i=1 := by omega
  subst i
  have h : 3^k%10=7 := by simp at he; omega
  rw [pow3_mod10] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> omega

theorem generic_two_into_power (i k t : Nat) (he : 3^k=3^i*(3*t+2)+1+i+t+3) :
    i=1 ∧ k%4=0 := by
  have hi : i<2 := by
    apply Nat.lt_of_not_ge
    intro h
    exact generic_two_high_excluded i k t (by omega) he
  have hpos : i≠0 := by
    intro hz
    subst i
    have h := pow3_odd k
    simp at he
    omega
  have h1 : i=1 := by omega
  subst i
  have h : 3^k%10=1 := by simp at he; omega
  rw [pow3_mod10] at h
  split at h <;> try omega
  split at h <;> try contradiction
  split at h <;> contradiction


-- Root-compatible tag 2 values occur only just above a power of 3.
def Invariant (s : Section) : Prop := Valid s ∧
  (s.2=1 ∨ ∃ a, 2≤a ∧ s=(3^a+a+1,2))

theorem power_exponent_ge_two {h : Nat} (hp : 4≤3^h) : 2≤h := by
  by_cases hh : h≤1
  · have he := Nat.pow_le_pow_right (n:=3) (by decide) hh
    omega
  · omega

theorem between_powers_no_power {a x : Nat} (hl : 3^a<x) (hu : x<3^(a+1)) (k : Nat) : x≠3^k := by
  intro h
  by_cases hk : k≤a
  · have hh := Nat.pow_le_pow_right (n:=3) (by decide) hk
    omega
  · have hh := Nat.pow_le_pow_right (n:=3) (by decide) (show a+1≤k by omega)
    omega

theorem tag_two_between (a : Nat) (ha : 2≤a) : 3^a<3^a+a+1 ∧ 3^a+a+1<3^(a+1) := by
  have h := power_gap a ha
  rw [Nat.pow_succ]
  omega

theorem invariant_power_tag {s : Section} (hs : Invariant s) {k : Nat} (he : s.1=3^k) : s.2=1 := by
  rcases hs.2 with h|⟨a,ha,rfl⟩
  · exact h
  · exact False.elim (between_powers_no_power (tag_two_between a ha).1 (tag_two_between a ha).2 k he)

theorem invariant_edge {s t : Section} (hs : Invariant s) (he : Edge s t) : Invariant t := by
  have hv := (edge_grows hs.1 he).2
  refine ⟨hv,?_⟩
  cases he with
  | one ht hx => exact Or.inl rfl
  | two hx => exact Or.inl rfl
  | @power h c r hr hm =>
    have hc : c=1 := invariant_power_tag hs rfl
    have hh : 2≤h := power_exponent_ge_two hs.1.1
    rcases hr with rfl|rfl
    · exact Or.inl rfl
    · right
      refine ⟨h,hh,?_⟩
      simp [hc]
      omega

theorem seven_gap (a : Nat) (ha : 2≤a) : 7*a+19<5*3^a := by
  induction a with
  | zero => omega
  | succ a ih =>
    by_cases h : 2≤a
    · have hh := ih h
      rw [Nat.pow_succ]
      omega
    · have he : a=1 := by omega
      subst a; decide

theorem generic_after_tag_two_not_power (a h t r y : Nat) (ha : 2≤a) (hr : r=1 ∨ r=2)
    (hx : 3^a+a+1=3^h*(3*t+r)) (hy : y=3^a+a+1+2+h+t+r+1) : ∀ k, y≠3^k := by
  have hbetween := tag_two_between a ha
  have hm : 0<3*t+r := by omega
  have hpow : 3^h ≤ 3^a+a+1 := by rw [hx]; exact Nat.le_mul_of_pos_right _ hm
  have hh : h≤a := by
    apply Nat.le_of_not_gt
    intro hgt
    have hh := Nat.pow_le_pow_right (n:=3) (by decide) (show a+1≤h by omega)
    omega
  have ht : 3*t+r ≤ 3^a+a+1 := by rw [hx]; exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
  have hg := seven_gap a ha
  have hlo : 3^a<y := by omega
  have hhi : y<3^(a+1) := by rw [Nat.pow_succ]; omega
  exact between_powers_no_power hlo hhi

theorem power_return_not_power (h c r : Nat) (hh : 2≤h) (hc : c=1 ∨ c=2) (hr : r=1 ∨ r=2) :
    ∀ k, 3^h+c+h+4-2*r≠3^k := by
  have hg := power_gap h hh
  have hlo : 3^h<3^h+c+h+4-2*r := by omega
  have hhi : 3^h+c+h+4-2*r<3^(h+1) := by rw [Nat.pow_succ]; omega
  exact between_powers_no_power hlo hhi

theorem incoming_power {s : Section} (hs : Invariant s) {k r : Nat}
    (he : Edge s (3^k,r)) :
    r=1 ∧ s.2=1 ∧ ((k%4=3 ∧ ∃ t, s.1=3*(3*t+1) ∧ 3^k=10*t+7) ∨
                          (k%4=0 ∧ ∃ t, s.1=3*(3*t+2) ∧ 3^k=10*t+11)) := by
  -- Generalize the target to avoid dependent elimination of a nonlinear expression.
  generalize ht : (3^k,r) = target at he
  cases he with
  | @one x c h t hpos hx =>
    have hy : 3^k=x+c+h+t+2 := congrArg Prod.fst ht
    have hr : r=1 := congrArg Prod.snd ht
    have hc : c=1 := by
      rcases hs.2 with h1|⟨a,ha,hs2⟩
      · exact h1
      · have hx' : x=3^a+a+1 := congrArg Prod.fst hs2
        have hc' : c=2 := congrArg Prod.snd hs2
        exact False.elim (generic_after_tag_two_not_power a h t 1 (3^k) ha (Or.inl rfl)
          (hx'.symm.trans hx) (by omega) k rfl)
    have hq : 3^k=3^h*(3*t+1)+1+h+t+2 := by rw [← hx, ← hc]; exact hy
    obtain ⟨hh,hk⟩ := generic_one_into_power h k t hq
    subst h
    exact ⟨hr,hc,Or.inl ⟨hk,t,by simpa using hx,by omega⟩⟩
  | @two x c h t hx =>
    have hy : 3^k=x+c+h+t+3 := congrArg Prod.fst ht
    have hr : r=1 := congrArg Prod.snd ht
    have hc : c=1 := by
      rcases hs.2 with h1|⟨a,ha,hs2⟩
      · exact h1
      · have hx' : x=3^a+a+1 := congrArg Prod.fst hs2
        have hc' : c=2 := congrArg Prod.snd hs2
        exact False.elim (generic_after_tag_two_not_power a h t 2 (3^k) ha (Or.inr rfl)
          (hx'.symm.trans hx) (by omega) k rfl)
    have hq : 3^k=3^h*(3*t+2)+1+h+t+3 := by rw [← hx, ← hc]; exact hy
    obtain ⟨hh,hk⟩ := generic_two_into_power h k t hq
    subst h
    exact ⟨hr,hc,Or.inr ⟨hk,t,by simpa using hx,by omega⟩⟩
  | @power h c j hj he =>
    have hy : 3^k=3^h+c+h+4-2*j := congrArg Prod.fst ht
    exact False.elim (power_return_not_power h c j (power_exponent_ge_two hs.1.1) hs.1.2 hj k hy.symm)

inductive MacroReach : Section → Section → Prop
  | refl (s) : MacroReach s s
  | tail {s t u} : MacroReach s t → Edge t u → MacroReach s u

theorem MacroReach.trans {s t u} (hs : MacroReach s t) (ht : MacroReach t u) : MacroReach s u := by
  induction ht with
  | refl => exact hs
  | tail _ h ih => exact .tail ih h

theorem root_invariant {s : Section} (hr : MacroReach start s) : Invariant s := by
  induction hr with
  | refl => simp [start, Invariant, Valid]
  | tail _ h ih => exact invariant_edge ih h

theorem root_not_power (k : Nat) : (4:Nat)≠3^k := by
  intro he
  have h := power_exponent_ge_two (by omega : 4≤3^k)
  have h2 := Nat.pow_le_pow_right (n:=3) (by decide) h
  omega

theorem root_power_class {k c : Nat} (hr : MacroReach start (3^k,c)) : c=1 ∧ (k%4=3 ∨ k%4=0) := by
  generalize ht : (3^k,c)=s at hr
  cases hr with
  | refl => exact False.elim (root_not_power k (congrArg Prod.fst ht).symm)
  | tail hr he =>
    rw [← ht] at he
    obtain ⟨hc,_,hp⟩ := incoming_power (root_invariant hr) he
    exact ⟨hc,hp.elim (fun h=>Or.inl h.1) (fun h=>Or.inr h.1)⟩

theorem MacroHalts.reaches_terminal {s : Section} (h : MacroHalts s) : ∃ t, MacroReach s t ∧ Terminal t := by
  induction h with
  | stop h => exact ⟨_, .refl _, h⟩
  | step he _ ih =>
    obtain ⟨u,hu,hterm⟩ := ih
    exact ⟨u, (MacroReach.tail (.refl _) he).trans hu, hterm⟩

theorem MacroReach.halts {s t : Section} (hr : MacroReach s t) (ht : MacroHalts t) : MacroHalts s := by
  induction hr with
  | refl => exact ht
  | tail _ he ih => exact ih (.step he ht)

theorem root_terminal_class {s : Section} (hr : MacroReach start s) (ht : Terminal s) :
    ∃ k, s=(3^k,1) ∧ (k%12=0 ∨ k%12=3) := by
  obtain ⟨k,hk,hm⟩ := ht
  rcases s with ⟨x,c⟩
  change x=3^k at hk
  subst x
  obtain ⟨hc,hmod4⟩ := root_power_class hr
  subst c
  have hge : 2≤k := power_exponent_ge_two (root_invariant hr).1.1
  have hp : 3^k%3=0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 3 (show 1≤k by omega))
  have h3 : k%3=0 := by simp at hm; have hpos : 0<3^k := Nat.pow_pos (by decide); omega
  exact ⟨k,rfl,by omega⟩

theorem root_halts_iff_restricted_power : Halts (D 0 3 1) ↔
    ∃ k, (k%12=0 ∨ k%12=3) ∧ MacroReach start (3^k,1) := by
  rw [root_halts_iff]
  constructor
  · intro hh
    obtain ⟨s,hs,ht⟩ := hh.reaches_terminal
    obtain ⟨k,he,hk⟩ := root_terminal_class hs ht
    exact ⟨k,hk,he ▸ hs⟩
  · rintro ⟨k,hk,hr⟩
    have hge : 2≤k := power_exponent_ge_two (root_invariant hr).1.1
    have hp : 3^k%3=0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 3 (show 1≤k by omega))
    have hterm : Terminal (3^k,1) := by
      refine ⟨k,rfl,?_⟩
      have hpos : 0<3^k := Nat.pow_pos (by decide)
      simp
      omega
    exact hr.halts (.stop hterm)

#print axioms root_halts_iff
#print axioms root_halts_iff_restricted_power
#print axioms incoming_power

end F119
