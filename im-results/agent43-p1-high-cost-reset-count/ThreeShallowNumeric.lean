import ThreeLayerBarrier
namespace BB6.Agent43ThreeLayer

/-- No three-shallow dyadic terminal equation survives at n>=58 for any
coefficients from the two genuine shallow source profiles. -/
theorem no_three_shallow_numeric_58
 (n s u v r p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E : Nat)
 (hn : 58≤n) (hs : 3*s≤n)
 (haPos : 1≤alpha) (hbPos : 1≤beta) (hcPos : 1≤gamma)
 (hp : (8:Nat)^s*p=2^n) (hd : (8:Nat)^s*d=14*n+92)
 (hc1 : 392≤C1) (hc2 : 392≤C2) (hc3 : 392≤C3)
 (hl1min : 56≤L1) (hl1max : L1≤84)
 (hl2min : 56≤L2) (hl2max : L2≤84)
 (hl3min : 56≤L3) (hl3max : L3≤84)
 (ho1 : O1≤232) (ho2 : O2≤232) (ho3 : O3≤232)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hE : E+384=112*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*r))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+C3*(8^s*((2^alpha*8^u)*(2^beta*8^v))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*((2^gamma*8^r)*E+R3)+R2)+R1) : False := by
 let q := (8:Nat)^s
 let X := n+2
 have hqpos : 0<q := Nat.pow_pos (by decide)
 have hqp : q*p=2^n := hp
 have hqd : ∃ d, q*d=14*n+92 := ⟨d,hd⟩
 have hqpow : q=2^(3*s) := by
   simpa only [show (8:Nat)=2^3 by decide] using (Nat.pow_mul 2 3 s).symm
 have hpSplit : q*2^(n-3*s)=2^n := by
   rw [hqpow,←Nat.pow_add]
   have he : 3*s+(n-3*s)=n := by omega
   rw [he]
 have hpExp : p=2^(n-3*s) :=
   Nat.eq_of_mul_eq_mul_left hqpos (by rw [hp,hpSplit])
 have hdPos : 0<d := by
   by_cases hz : d=0
   · rw [hz] at hd
     simp at hd
   · omega
 have hdle : d≤14*n+92 := by
   have hq1 : 1≤q := hqpos
   have hh : d≤q*d := by simpa using (Nat.mul_le_mul_right d hq1)
   have hdq : q*d=14*n+92 := by simpa only [q] using hd
   rw [hdq] at hh
   exact hh
 have hR1lower : 56*(n+6) ≤ L1*(n+6+3*s) := by
   exact Nat.mul_le_mul hl1min (by omega)
 have hR1upper : L1*(n+6+3*s) ≤84*(n+6+3*s) :=
   Nat.mul_le_mul_right _ hl1max
 have hR1pos : 0<R1 := by omega
 have hR1bound : R1≤400*X := by dsimp [X]; omega
 have hR2lower : 56*(n+6) ≤ L2*(n+6+3*s+alpha+3*u) := by
   exact Nat.mul_le_mul hl2min (by omega)
 have hR2pos : 0<R2 := by omega
 have hR2bound : alpha+3*u≤n-3*s → R2≤600*X := by
   intro hu
   have hR2upper : L2*(n+6+3*s+alpha+3*u) ≤84*(n+6+3*s+alpha+3*u) :=
     Nat.mul_le_mul_right _ hl2max
   dsimp [X]
   omega
 have hR3lower : 56*(n+6) ≤ L3*(n+6+3*s+alpha+3*u+beta+3*v) := by
   exact Nat.mul_le_mul hl3min (by omega)
 have hR3pos : 0<R3 := by omega
 have hR3bound : beta+3*v≤(n-3*s)-(alpha+3*u) → R3≤600*X := by
   intro hv
   have hR3upper : L3*(n+6+3*s+alpha+3*u+beta+3*v) ≤
      84*(n+6+3*s+alpha+3*u+beta+3*v) :=
     Nat.mul_le_mul_right _ hl3max
   dsimp [X]
   omega
 have hEbound : gamma+3*r≤((n-3*s)-(alpha+3*u))-(beta+3*v) → E≤2000*X := by
   intro hr
   dsimp [X]
   omega
 have hq1 : 1≤q := hqpos
 have hC1large : 98≤C1*q := by
   have hc := Nat.mul_le_mul_right q hc1
   have hx := Nat.mul_le_mul_left 392 hq1
   omega
 have hC3large : 392*(q*((2^alpha*8^u)*(2^beta*8^v))) ≤
   C3*(q*((2^alpha*8^u)*(2^beta*8^v))) := Nat.mul_le_mul_right _ hc3
 have hKq : K+98=C1*q+C2*(q*(2^alpha*8^u))+C3*(q*((2^alpha*8^u)*(2^beta*8^v))) := by simpa only [q] using hK
 have hKbound : 392*(q*((2^alpha*8^u)*(2^beta*8^v)))≤K := by
   omega
 exact three_layer_abstract_barrier n s u v r alpha beta gamma q p (2^alpha) (2^beta) (2^gamma) K R1 R2 R3 E
   hn hqp hqd rfl hpExp rfl rfl rfl hKbound hR1pos hR1bound
   hR2pos hR2bound hR3pos hR3bound hEbound hEq

#print axioms no_three_shallow_numeric_58
end BB6.Agent43ThreeLayer
