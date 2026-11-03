import ForwardSurj

namespace BB6.Agent17Forward


private theorem mod_cancel (q x y r s t : Nat)
    (_hq : 0 < q) (_hr : r < q) (hs : s < q)
    (hxr : x % q = r)
    (hy : y + r + q = x + s + q * t) : y % q = s := by
  have hxq : x = r + q * (x / q) := by
    have h := Nat.mod_add_div x q
    omega
  have hyq : y + q = s + q * (x / q + t) := by
    rw [hxq] at hy
    rw [Nat.mul_add]
    omega
  have hyq2 : y = s + q * (x / q + t - 1) := by
    have ht : 1 ≤ x / q + t := by
      by_cases h : x / q + t = 0
      · rw [h] at hyq
        simp at hyq
        omega
      · exact Nat.one_le_iff_ne_zero.mpr h
    have hv : x / q + t = (x / q + t - 1) + 1 := by omega
    rw [hv, Nat.mul_add] at hyq
    simp only [Nat.mul_one] at hyq
    exact Nat.add_right_cancel (by simpa only [Nat.add_assoc] using hyq)
  rw [hyq2, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hs

private theorem algebra (t r s d b : Nat)
    (hds : d+s+1 = r+(2*t+1)) :
    let q := 2*t+1
    let w := 5+3*b+t*(d+8*b+11)
    let u := 1+4*w
    let x := 4^b*u
    let y := x+2*b+2*w
    x+P r (1+2*d) b = r+q*(2*(d+8*b+11))*4^b ∧
    y+r+q = x+s+q*(d+8*b+11) := by
  dsimp
  constructor
  · simp only [P]
    grind
  · grind

/-- A checked root of the modular polynomial produces a legal generic even
Sheep return between the specified residues. -/
theorem generic_edge_from_root (t r s d b : Nat)
    (hr : r < 2*t+1) (hs : s < 2*t+1)
    (hb : 1 ≤ b) (hds : d+s+1 = r+(2*t+1))
    (hroot : P r (1+2*d) b % (2*t+1) = 0) :
    let q := 2*t+1
    let w := 5+3*b+t*(d+8*b+11)
    let u := 1+4*w
    let x := 4^b*u
    let y := x+2*b+2*w
    5 ≤ u ∧ u % 4 = 1 ∧ x % 2 = 0 ∧ y % 2 = 0 ∧
    x % q = r ∧ y % q = s := by
  dsimp
  let q := 2*t+1
  let w := 5+3*b+t*(d+8*b+11)
  let u := 1+4*w
  let x := 4^b*u
  let y := x+2*b+2*w
  have hq : 0 < q := by dsimp [q]; omega
  have hu : 5 ≤ u := by dsimp [u,w]; omega
  have hu4 : u%4=1 := by dsimp [u]; simp [Nat.add_mul_mod_self_left]
  have hx2 : x%2=0 := by
    cases b with
    | zero => omega
    | succ b => simp [x, Nat.pow_succ, Nat.mul_mod]
  have hy2 : y%2=0 := by dsimp [y]; omega
  have ha := algebra t r s d b hds
  have hex : x+P r (1+2*d) b = r+q*(2*(d+8*b+11))*4^b := by
    simpa [q,w,u,x,y] using ha.1
  have hey : y+r+q = x+s+q*(d+8*b+11) := by
    simpa [q,w,u,x,y] using ha.2
  have hxq : x % q = r := by
    have hm := congrArg (fun z : Nat => z % q) hex
    have hl : (x+P r (1+2*d) b)%q = x%q := by
      calc
        (x+P r (1+2*d) b)%q = (P r (1+2*d) b + x)%q := by rw [Nat.add_comm]
        _ = (P r (1+2*d) b % q + x)%q := (Nat.mod_add_mod _ _ _).symm
        _ = (0+x)%q := by simpa [q] using congrArg (fun z : Nat => (z+x)%q) hroot
        _ = x%q := by simp
    have hrhs : (r+q*(2*(d+8*b+11))*4^b)%q = r := by
      rw [show q*(2*(d+8*b+11))*4^b = q*((2*(d+8*b+11))*4^b) by ac_rfl]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hr
    rw [hl, hrhs] at hm
    exact hm
  have hyq : y%q=s := mod_cancel q x y r s (d+8*b+11) hq hr hs hxq hey
  exact ⟨hu,hu4,hx2,hy2,hxq,hyq⟩


/-- Arbitrarily large witnesses keep the same source and target residues. -/
theorem generic_edge_from_root_unbounded (t r s d b N : Nat)
    (hr : r < 2*t+1) (hs : s < 2*t+1)
    (hb : 1 ≤ b) (hds : d+s+1 = r+(2*t+1))
    (hroot : P r (1+2*d) b % (2*t+1) = 0) :
    ∃ u x y : Nat, N ≤ x ∧ 5 ≤ u ∧ u % 4 = 1 ∧
      x = 4^b*u ∧ y = x+2*b+(u-1)/2 ∧
      x % 2 = 0 ∧ y % 2 = 0 ∧
      x % (2*t+1) = r ∧ y % (2*t+1) = s := by
  let q := 2*t+1
  let w0 := 5+3*b+t*(d+8*b+11)
  let u0 := 1+4*w0
  let x0 := 4^b*u0
  let y0 := x0+2*b+2*w0
  have hbase := generic_edge_from_root t r s d b hr hs hb hds hroot
  have hu0 : 5 ≤ u0 := hbase.1
  have hu04 : u0%4=1 := hbase.2.1
  have hx02 : x0%2=0 := hbase.2.2.1
  have hy02 : y0%2=0 := hbase.2.2.2.1
  have hx0q : x0%q=r := hbase.2.2.2.2.1
  have hy0q : y0%q=s := hbase.2.2.2.2.2
  let w := w0+q*(N+1)
  let u := 1+4*w
  let x := 4^b*u
  let y := x+2*b+2*w
  have hu : u = u0+4*q*(N+1) := by
    dsimp [u,u0,w]
    simp only [Nat.mul_add, Nat.add_mul]
    ac_rfl
  have hx : x = x0+q*(4*4^b*(N+1)) := by
    dsimp [x,x0]
    rw [hu]
    simp only [Nat.mul_add]
    ac_rfl
  have hy : y = y0+q*((4*4^b+2)*(N+1)) := by
    dsimp [y,y0,w]
    rw [hx]
    simp only [Nat.mul_add, Nat.add_mul]
    ac_rfl
  have hq : 0 < q := by dsimp [q]; omega
  have hu5 : 5 ≤ u := by rw [hu]; omega
  have hu4 : u%4=1 := by
    rw [hu]
    have hmultiple : 4*q*(N+1) = 4*(q*(N+1)) := by ac_rfl
    rw [hmultiple, Nat.add_mul_mod_self_left]
    exact hu04
  have hxn : N ≤ x := by
    have hlow : N ≤ q*(N+1) := by
      calc
        N ≤ N+1 := by omega
        _ ≤ q*(N+1) := Nat.le_mul_of_pos_left (N+1) hq
    have hlow2 : q*(N+1) ≤ 4*q*(N+1) := by
      have hh : 1 ≤ 4 := by decide
      have ht := Nat.mul_le_mul_right (q*(N+1)) hh
      simpa only [Nat.one_mul, Nat.mul_assoc] using ht
    have hlow3 : 4*q*(N+1) ≤ u := by rw [hu]; omega
    have hlow4 : u ≤ x := Nat.le_mul_of_pos_left u (Nat.pow_pos (by decide))
    omega
  refine ⟨u,x,y,hxn,hu5,hu4,rfl,?_,?_,?_,?_,?_⟩
  · dsimp [y,u,w]
    omega
  · rw [hx, show q*(4*4^b*(N+1)) = 2*(q*(2*4^b*(N+1))) by
      rw [show (4:Nat)=2*2 by decide]
      ac_rfl]
    rw [Nat.add_mul_mod_self_left]
    exact hx02
  · have hh : 4*4^b+2=2*(2*4^b+1) := by omega
    rw [hy, hh, show q*(2*(2*4^b+1)*(N+1)) = 2*(q*((2*4^b+1)*(N+1))) by ac_rfl]
    rw [Nat.add_mul_mod_self_left]
    exact hy02
  · rw [hx, Nat.add_mul_mod_self_left]
    exact hx0q
  · rw [hy, Nat.add_mul_mod_self_left]
    exact hy0q

#print axioms generic_edge_from_root_unbounded

#print axioms generic_edge_from_root
end BB6.Agent17Forward
