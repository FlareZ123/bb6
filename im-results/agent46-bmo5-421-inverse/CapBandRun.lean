import CapBandInverse
namespace CapSieve

/-- Positive same-band coordinate, retaining the exact index-dependent offset. -/
def Q (j x : Nat) : Nat := 2*(x-L j)+j+6

theorem q_bounds {j x : Nat} (hb : Band j x) : j+6≤Q j x ∧ Q j x≤2*P j+j+2 := by
  have h:=band_bounds hb
  have hl:=l_add j
  unfold Q
  omega

theorem q_eq {j x : Nat} (hb : Band j x) : Q j x+2*P j=2*x+3*j+12 := by
  have h:=band_bounds hb
  have hl:=l_add j
  unfold Q
  omega

theorem q_inj {j x y : Nat} (hx : Band j x) (hy : Band j y) (h : Q j x=Q j y) : x=y := by
  have h1:=q_eq hx
  have h2:=q_eq hy
  omega

theorem q_terminal (j : Nat) : Q j (T j)=2*P j+j := by
  have h:=t_add j
  have hp:=p_ge j
  have hl:=l_add j
  unfold P at h
  unfold Q P at *
  omega

theorem terminal_band (j : Nat) : Band j (T j) := by
  have h:=t_add j
  have hp:=p_ge j
  have hl:=l_add j
  have hn:=l_add (j+1)
  rw [p_succ] at hn
  unfold Band P at *
  omega

theorem q_special (j : Nat) : Q j (L j+(P j-2))=2*P j+j+2 := by
  have hp:=p_ge j
  unfold Q
  omega

theorem q_reg_step {j x y : Nat} (hr : RegFrom j x y) (hy : Band j y) : Q j y=3*Q j x := by
  obtain ⟨r,hr,rfl,rfl⟩:=hr
  have h:=q_eq hy
  unfold Q at *
  omega

inductive SameRun (j : Nat) : Nat → Nat → Nat → Prop where
  | zero {x : Nat} : Band j x → SameRun j 0 x x
  | head {n x z y : Nat} : RegFrom j x z → SameRun j n z y → SameRun j (n+1) x y

theorem same_run_bands {j n x y : Nat} (h : SameRun j n x y) : Band j x ∧ Band j y := by
  induction h with
  | zero hb => exact ⟨hb,hb⟩
  | head hr _ ih =>
    obtain ⟨r,hr,rfl,_⟩:=hr
    exact ⟨regular_band j r hr,ih.2⟩

theorem same_run_q {j n x y : Nat} (h : SameRun j n x y) : Q j y=3^n*Q j x := by
  induction h with
  | zero hb => simp
  | head hr hs ih =>
    rw [ih,q_reg_step hr (same_run_bands hs).1,Nat.pow_succ]
    exact Nat.mul_assoc _ _ _ |>.symm

theorem same_run_of_q {j n x y : Nat} (hx : Band j x) (hy : Band j y)
    (h : Q j y=3^n*Q j x) : SameRun j n x y := by
  induction n generalizing x with
  | zero =>
    have he : x=y := q_inj hx hy (by simpa using h.symm)
    subst y
    exact .zero hx
  | succ n ih =>
    have hpos : 1≤3^n := Nat.pow_pos (by decide)
    have hmul : 3*Q j x≤3^(n+1)*Q j x := by
      rw [Nat.pow_succ,Nat.mul_assoc]
      exact Nat.le_trans (by simp) (Nat.le_mul_of_pos_left _ hpos)
    have hle : 3*Q j x≤Q j y := h ▸ hmul
    have hbx := q_bounds hx
    have hby := q_bounds hy
    let r:=x-L j
    have he : x=L j+r := by have := hx.1; dsimp [r]; omega
    have hr : r+4≤P j := by unfold Q at hbx hby hle; dsimp [r]; omega
    let z:=3*r+P j+3
    have hreg : RegFrom j x z := ⟨r,hr,he,rfl⟩
    have hz : Band j z := by
      have hl := l_add j
      have hb:=band_bounds hy
      have hnext:=l_add (j+1)
      rw [p_succ] at hnext
      unfold Band
      unfold Q at hle
      dsimp [z,r]
      omega
    have hq := q_reg_step hreg hz
    have h' : Q j y=3^n*Q j z := by rw [hq,h,Nat.pow_succ,Nat.mul_assoc]
    exact .head hreg (ih hz h')

/-- Complete closed form for every length of a same-band regular run. -/
theorem same_run_iff {j n x y : Nat} : SameRun j n x y ↔
    Band j x ∧ Band j y ∧ Q j y=3^n*Q j x := by
  constructor
  · intro h
    exact ⟨(same_run_bands h).1,(same_run_bands h).2,same_run_q h⟩
  · rintro ⟨hx,hy,h⟩
    exact same_run_of_q hx hy h

/-- A target y has n same-band ancestors exactly when its Q coordinate
    is divisible by 3^n and the quotient is in the band's lower range. -/
theorem same_run_exists {j n y : Nat} (hy : Band j y) : (∃ x, SameRun j n x y) ↔
    3^n ∣ Q j y ∧ 3^n*(j+6)≤Q j y := by
  constructor
  · rintro ⟨x,h⟩
    have hq:=same_run_q h
    have hx:=q_bounds (same_run_bands h).1
    exact ⟨⟨Q j x,hq⟩,by rw [hq]; exact Nat.mul_le_mul_left _ hx.1⟩
  · rintro ⟨⟨q,hq⟩,hmin⟩
    have hpos : 0<3^n := Nat.pow_pos (by decide)
    have hlo : j+6≤q := by
      rw [hq] at hmin
      exact Nat.le_of_mul_le_mul_left hmin hpos
    have hhi : q≤2*P j+j+2 := by
      have hh:=q_bounds hy
      have hh' : q≤3^n*q := Nat.le_mul_of_pos_left _ hpos
      omega
    have hpar : q%2=j%2 := by
      have hpAll : ∀ k : Nat, 3^k%2=1 := by
        intro k
        induction k with
        | zero => decide
        | succ k ih => rw [Nat.pow_succ,Nat.mul_mod,ih]
      have hp := hpAll n
      have hh : Q j y%2=j%2 := by unfold Q; omega
      rw [hq,Nat.mul_mod,hp] at hh
      simpa using hh
    let r := (q-(j+6))/2
    let x := L j+r
    have hr : q=2*r+j+6 := by dsimp [r]; omega
    have hx : Band j x := by
      unfold Band
      rw [l_succ]
      dsimp [x]
      have := p_ge j
      omega
    have hqx : Q j x=q := by unfold Q; dsimp [x]; omega
    exact ⟨x,same_run_of_q hx hy (by rw [hqx,hq])⟩

/-- Exact same-band terminal criterion at any actual entry point. -/
theorem same_run_halt {j x : Nat} (hx : Band j x) :
    (∃ n, SameRun j n x (T j)) ↔ ∃ n, 2*P j+j=3^n*Q j x := by
  constructor
  · rintro ⟨n,h⟩
    have hq:=same_run_q h
    rw [q_terminal] at hq
    exact ⟨n,hq⟩
  · rintro ⟨n,h⟩
    exact ⟨n,same_run_of_q hx (terminal_band j) (by rw [q_terminal]; exact h)⟩

#print axioms same_run_iff
#print axioms same_run_exists
#print axioms same_run_halt
end CapSieve
