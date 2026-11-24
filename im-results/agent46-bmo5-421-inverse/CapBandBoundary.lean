import CapBandRun
namespace CapSieve

/-- Signed upper-boundary coordinate. It never vanishes on natural states. -/
def W (j x : Nat) : Int := 8*(P j:Int)-4*(x:Int)-6*(j:Int)-27

theorem w_odd (j x : Nat) : W j x%2=1 := by unfold W; omega

theorem w_ne_zero (j x : Nat) : W j x≠0 := by have := w_odd j x; omega

theorem w_bounds {j x : Nat} (hb : Band j x) :
    -(2*(j:Int)+7)≤W j x ∧ W j x≤4*(P j:Int)-2*(j:Int)-15 := by
  have h:=band_bounds hb
  have hl:=l_add j
  unfold W
  omega

theorem w_terminal (j : Nat) : W j (T j)= -(2*(j:Int)+3) := by
  have h:=t_add j
  unfold P at h
  unfold W P
  omega

theorem w_regular_same {j x y : Nat} (h : RegFrom j x y) :
    W j y=3*W j x-8*(P j:Int)+6 := by
  obtain ⟨r,hr,rfl,rfl⟩:=h
  have hl:=l_add j
  unfold W
  omega

theorem w_regular_down {j x y : Nat} (h : RegFrom j x y) :
    W (j+1) y=3*W j x := by
  obtain ⟨r,hr,rfl,rfl⟩:=h
  have hl:=l_add j
  unfold W
  rw [p_succ]
  omega

theorem w_regular_skip {j x y : Nat} (h : RegFrom j x y) :
    W (j+2) y=3*W j x+16*(P j:Int)-6 := by
  obtain ⟨r,hr,rfl,rfl⟩:=h
  have hl:=l_add j
  unfold W
  rw [show j+2=(j+1)+1 by omega,p_succ,p_succ]
  omega

theorem w_special_positive (j : Nat) : 0<W (j+1) (2*P j) := by
  have hp:=p_ge j
  unfold W
  rw [p_succ]
  omega

theorem w_skip_positive {j x y : Nat} (h : RegFrom j x y) (hb : Band (j+2) y) :
    0<W (j+2) y := by
  obtain ⟨r,hr,rfl,rfl⟩:=h
  have hp:=p_ge j
  unfold W
  rw [show j+2=(j+1)+1 by omega,p_succ,p_succ]
  omega

/-- A run of regular edges each advancing the actual band index by one. -/
inductive UpRun : Nat → Nat → Nat → Nat → Prop where
  | zero {j x : Nat} : Band j x → UpRun j 0 x x
  | head {j n x z y : Nat} : RegFrom j x z → UpRun (j+1) n z y → UpRun j (n+1) x y

theorem up_run_w {j n x y : Nat} (h : UpRun j n x y) :
    W (j+n) y=(3^n:Int)*W j x := by
  induction h with
  | zero hb => simp
  | @head j n x z y hr hs ih =>
    rw [show j+(n+1)=j+1+n by omega,ih,w_regular_down hr,Int.pow_succ]
    grind

theorem up_run_bands {j n x y : Nat} (h : UpRun j n x y) : Band j x ∧ Band (j+n) y := by
  induction h with
  | zero hb => simpa using And.intro hb hb
  | @head j n x z y hr hs ih =>
    obtain ⟨r,hr,rfl,_⟩:=hr
    exact ⟨regular_band j r hr,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih.2⟩

/-- An initial inverse run consisting only of one-band descents from terminal i
    requires 3^n | 2i+3, with no depth restriction. -/
theorem terminal_up_divides {j n x : Nat} (h : UpRun j n x (T (j+n))) :
    3^n ∣ 2*(j+n)+3 := by
  have hw:=up_run_w h
  rw [w_terminal] at hw
  have hp : 0<(3^n:Int) := Int.pow_pos (by decide)
  have hneg : W j x<0 := by
    by_cases hbad : W j x<0
    · exact hbad
    · have hn : 0≤W j x := by omega
      have hm := Int.mul_nonneg (Int.le_of_lt hp) hn
      omega
  refine ⟨(-W j x).toNat,?_⟩
  have hcast : ((-W j x).toNat:Int)= -W j x := Int.toNat_of_nonneg (by omega)
  have h' : (2*(j+n)+3:Int)=(3^n:Int)*(-W j x) := by
    rw [Int.mul_neg]
    omega
  rw [←hcast] at h'
  exact_mod_cast h'

theorem terminal_up_length {j n x : Nat} (h : UpRun j n x (T (j+n))) :
    3^n≤2*(j+n)+3 := Nat.le_of_dvd (by omega) (terminal_up_divides h)

theorem terminal_up_negative {j n x : Nat} (h : UpRun j n x (T (j+n))) : W j x<0 := by
  have hw:=up_run_w h
  rw [w_terminal] at hw
  by_cases hh : W j x<0
  · exact hh
  · have hp : 0≤(3^n:Int) := Int.pow_nonneg (by decide)
    have hm:=Int.mul_nonneg hp (show 0≤W j x by omega)
    omega

/-- Same-band inverse run can reach the exceptional low boundary only if the
    incoming Q has a 3-power divisor with a small quotient. -/
theorem boundary_run_divisor {j n x y : Nat} (h : SameRun j n x y)
    (hx : x≤P j+2) : ∃ q, Q j y=3^n*q ∧ j+6≤q ∧ q≤3*j+16 := by
  have hb:=same_run_bands h
  have hq:=same_run_q h
  have hqx:=q_eq hb.1
  have hmin:=(q_bounds hb.1).1
  exact ⟨Q j x,hq,hmin,by omega⟩

#print axioms up_run_w
#print axioms terminal_up_divides
#print axioms terminal_up_length
#print axioms boundary_run_divisor
end CapSieve
