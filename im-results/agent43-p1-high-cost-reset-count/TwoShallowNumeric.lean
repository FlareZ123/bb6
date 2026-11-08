import TwoLayerRemainder

namespace BB6.Agent43TwoLayer

/-- The exact two-shallow wall equality, even with generous coefficient
ranges that cover both shallow types, cannot hold for any n>=48. -/
theorem no_two_shallow_numeric_48
    (n s u r p d alpha beta C1 C2 L1 L2 O1 O2 K R1 R2 E : Nat)
    (hn : 48≤n) (hs : 3*s≤n)
    (hp : (8:Nat)^s*p=2^n) (hd : (8:Nat)^s*d=14*n+92)
    (ha1 : 1≤alpha) (ha2 : alpha≤2)
    (hb1 : 1≤beta) (hb2 : beta≤2)
    (hc1min : 392≤C1) (hc2min : 392≤C2)
    (hl1min : 56≤L1) (hl1max : L1≤84)
    (hl2min : 56≤L2) (hl2max : L2≤84)
    (ho1 : O1≤232) (ho2 : O2≤232)
    (hR1 : R1+O1+d=L1*(n+6+3*s))
    (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
    (hE : E+384=112*(n+6+3*s+alpha+3*u+beta+3*r))
    (hK : K+98=C1*8^s+C2*(8^s* (2^alpha*8^u)))
    (hEq : K*p=(2^alpha*8^u)*(2^beta*8^r*E+R2)+R1) : False := by
  let q := (8:Nat)^s
  let X := n+2
  have hqpos : 0<q := Nat.pow_pos (by decide)
  have hqp : q*p=2^n := hp
  have hqd : ∃ d, q*d=14*n+92 := ⟨d,hd⟩
  have hpowq : q=2^(3*s) := by
    simpa only [show (8:Nat)=2^3 by decide] using
      (Nat.pow_mul 2 3 s).symm
  have hpsplit : q*2^(n-3*s)=2^n := by
    rw [hpowq, ←Nat.pow_add]
    have he : 3*s+(n-3*s)=n := by omega
    rw [he]
  have hpExp : p=2^(n-3*s) := by
    exact Nat.eq_of_mul_eq_mul_left hqpos (by rw [hp,hpsplit])
  have hdPos : 0<d := by
    by_cases hz : d=0
    · rw [hz] at hd
      simp at hd
    · omega
  have hqleD : q≤q*d := by
    simpa using (Nat.mul_le_mul_left q hdPos)
  have hdq : q*d=14*n+92 := by simpa only [q] using hd
  have hdle : d≤14*n+92 := by
    have hq1 : 1≤q := hqpos
    have hh : d ≤ q*d := by simpa using (Nat.mul_le_mul_right d hq1)
    omega
  have hB1lower : 56*(n+6) ≤ L1*(n+6+3*s) := by
    exact Nat.mul_le_mul hl1min (by omega)
  have hB1upper : L1*(n+6+3*s) ≤84*(n+6+3*s) := by
    exact Nat.mul_le_mul_right _ hl1max
  have hR1pos : 0<R1 := by omega
  have hR1bound : R1≤400*X := by dsimp [X]; omega
  have hB2lower : 56*(n+6) ≤L2*(n+6+3*s+alpha+3*u) := by
    exact Nat.mul_le_mul hl2min (by omega)
  have hR2pos : 0<R2 := by omega
  have hR2bound : alpha+3*u≤n-3*s → R2≤600*X := by
    intro hu
    have hB2upper : L2*(n+6+3*s+alpha+3*u) ≤
        84*(n+6+3*s+alpha+3*u) :=
      Nat.mul_le_mul_right _ hl2max
    dsimp [X]
    omega
  have hEbound : beta+3*r≤(n-3*s)-(alpha+3*u) → E≤2000*X := by
    intro hr
    have hu : alpha+3*u≤n-3*s := by omega
    dsimp [X]
    omega
  have hC1large : 98≤C1*q := by
    have hc := Nat.mul_le_mul_right q hc1min
    have hqg : 1≤q := hqpos
    have hx := Nat.mul_le_mul_left 392 hqg
    omega
  have hC2large : 392*(q*((2^alpha)*8^u)) ≤
      C2*(q*((2^alpha)*8^u)) := by
    exact Nat.mul_le_mul_right _ hc2min
  have hK' : K+98=C1*q+C2*(q*(2^alpha*8^u)) := by simpa only [q] using hK
  have hKbound : 392*(q*((2^alpha)*8^u)) ≤K := by
    omega
  exact two_layer_abstract_barrier n s u r alpha beta q p (2^alpha) (2^beta)
    K R1 R2 E hn hqp hqd rfl hpExp hs rfl rfl ha2 ha1 hb2 hb1
    hKbound hR1pos hR1bound hR2pos hR2bound hEbound hEq

#print axioms BB6.Agent43TwoLayer.no_two_shallow_numeric_48
end BB6.Agent43TwoLayer