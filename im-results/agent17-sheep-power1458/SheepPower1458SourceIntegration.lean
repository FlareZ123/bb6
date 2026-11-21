import SheepEvenReachInverse
import SheepEvenSourceAlgebra
import SheepEvenInverseAlgebra
import SheepPower1458AffineBounds

namespace SheepPower1458

/-- Affine target data with the offset split into its positive and negative
parts: C*y+c = 2^(1458*t+s)+b. Exactly one of b,c is nonzero in the
inverse-tree certificates. -/
structure AffineNode where
  s : Nat
  b : Nat
  c : Nat
  C : Nat
  r : Nat
  v3C : Nat
  deriving DecidableEq, Repr

def affineNodeValue (t : Nat) (node : AffineNode) (y : Nat) : Prop :=
  node.C*y + node.c = 2^(1458*t+node.s) + node.b

def affineBasin (t : Nat) (nodes : List AffineNode) (y : Nat) : Prop :=
  ∃ node, node ∈ nodes ∧ affineNodeValue t node y

/-- Normalized generic source case for either sign of the affine offset. -/
def GenericAffineSourceCase (d b c n x y : Nat) : Prop :=
  ∃ a h v u : Nat,
    1 ≤ a ∧ 5 ≤ v ∧ v%2=1 ∧ u%2=1 ∧
    x=2^a*v ∧ y=1+3^h*u ∧
    (d*3^h)*(2^(a+1)+1)*v + 2*a*(d*3^h) +
      2^(h+1)*(d-b+c) =
      2^(n+h+1)+3*(d*3^h)

/-- Normalized exceptional source case for either sign of the affine offset. -/
def SpecialAffineSourceCase (d b c n x y : Nat) : Prop :=
  ∃ a h u : Nat,
    1 ≤ a ∧ u%2=1 ∧ x=3*2^a ∧ y=1+3^h*u ∧
    (d*3^h)*(3*2^a+a+2) + 2^h*(d-b+c) = 2^(n+h)

/-- One source splitter for every affine node C*y+c=2^n+b with b≤C and
one-sided offset. It normalizes both the positive and negative original-source
equations to the common C-B term used by the inverse-tree certificates. -/
theorem affine_edge_inverse_cases
    {x y d b c n : Nat} (hedge : SheepEven.EvenEdge x y)
    (hb : b ≤ d) (hsign : b=0 ∨ c=0)
    (hpower : d*y+c=2^n+b) :
    GenericAffineSourceCase d b c n x y ∨
    SpecialAffineSourceCase d b c n x y := by
  have hx : x%2=0 := SheepEven.even_edge_even hedge
  have hEdge := SheepEvenSourceAlgebra.even_edge_to_algebra hx hedge
  rcases hsign with hb0 | hc0
  · subst b
    rcases SheepEvenSourceAlgebra.original_even_edge_inverse_cases hx hedge hpower with
      ⟨a,h,v,u,ha,hv,hvodd,huodd,hxdef,hydef,hEq⟩ |
      ⟨a,h,u,ha,huodd,hxdef,hydef,hEq⟩
    · apply Or.inl
      refine ⟨a,h,v,u,ha,hv,hvodd,huodd,hxdef,hydef,?_⟩
      have hmul :
          2^(h+1)*d + 2^(h+1)*c = 2^(h+1)*(d+c) := by
        rw [←Nat.mul_add]
      rw [hmul] at hEq
      simpa using hEq
    · apply Or.inr
      refine ⟨a,h,u,ha,huodd,hxdef,hydef,?_⟩
      have hmul :
          2^h*d + 2^h*c = 2^h*(d+c) := by
        rw [←Nat.mul_add]
      rw [hmul] at hEq
      simpa using hEq
  · subst c
    rcases SheepEvenInverseAlgebra.edge_inverse_cases x y d n b hEdge hpower with
      hg | hs
    · rcases hg with ⟨a,h,v,u,ha,hv,hvodd,huodd,hxdef,hydef,hEq⟩
      apply Or.inl
      refine ⟨a,h,v,u,ha,hv,hvodd,huodd,hxdef,hydef,?_⟩
      have hmul :
          2^(h+1)*d = 2^(h+1)*(d-b) + 2^(h+1)*b := by
        rw [←Nat.mul_add, Nat.sub_add_cancel hb]
      rw [hmul] at hEq
      omega
    · rcases hs with ⟨a,h,u,ha,huodd,hxdef,hydef,hEq⟩
      apply Or.inr
      refine ⟨a,h,u,ha,huodd,hxdef,hydef,?_⟩
      have hmul :
          2^h*d = 2^h*(d-b) + 2^h*b := by
        rw [←Nat.mul_add, Nat.sub_add_cancel hb]
      rw [hmul] at hEq
      omega

/-- A node's exact 3-adic valuation certificate bounds every hidden
length that can occur in an original-source inverse case. -/
theorem affine_node_hidden_bound
    (t r0 T k h y u : Nat) (node : AffineNode)
    (ht : t = r0+T*k)
    (hb : node.b ≤ node.C)
    (hval : affineNodeValue t node y)
    (hydef : y=1+3^h*u) (huodd : u%2=1)
    (hC : 3^node.v3C ∣ node.C)
    (hbase :
      2^(1458*r0+node.s) % 3^(node.r+node.v3C+1) ≠
        (node.C-node.b+node.c) % 3^(node.r+node.v3C+1))
    (hperiod :
      2^(1458*T) % 3^(node.r+node.v3C+1) = 1) :
    h ≤ node.r := by
  by_contra hnot
  have hh : node.r+1 ≤ h := by omega
  have hyminus : y-1=3^h*u := by
    rw [hydef]
    have huPos : 0 < u := by omega
    have hpos : 0 < 3^h*u :=
      Nat.mul_pos (Nat.pow_pos (by decide)) huPos
    omega
  have hY : 3^(node.r+1) ∣ y-1 := by
    refine ⟨3^(h-node.r-1)*u, ?_⟩
    have hsplit : h = (node.r+1)+(h-node.r-1) := by omega
    rw [hyminus, hsplit, Nat.pow_add]
    ring
  have hprod : 3^(node.r+node.v3C+1) ∣ node.C*(y-1) := by
    rcases hC with ⟨c0,hc0⟩
    rcases hY with ⟨y0,hy0⟩
    refine ⟨c0*y0, ?_⟩
    have hpow : 3^node.v3C * 3^(node.r+1) =
        3^(node.r+node.v3C+1) := by
      rw [←Nat.pow_add]
      congr 1 <;> omega
    calc
      node.C*(y-1) =
          (3^node.v3C*c0)*(3^(node.r+1)*y0) := by rw [hc0,hy0]
      _ = 3^(node.r+node.v3C+1)*(c0*y0) := by rw [hpow]; ring
  have hnum :
      node.C*(y-1)+(node.C-node.b+node.c)=2^(1458*t+node.s) := by
    have hyone : y=1+(y-1) := by omega
    unfold affineNodeValue at hval
    rw [hyone, Nat.mul_add] at hval
    omega
  let m := 3^(node.r+node.v3C+1)
  have hmod :
      2^(1458*t+node.s)%m=(node.C-node.b+node.c)%m := by
    calc
      2^(1458*t+node.s)%m =
          (node.C*(y-1)+(node.C-node.b+node.c))%m := by rw [hnum]
      _ = ((node.C*(y-1))%m + (node.C-node.b+node.c)%m)%m := by
          rw [Nat.add_mod]
      _ = (node.C-node.b+node.c)%m := by
          rw [Nat.mod_eq_zero_of_dvd hprod]
          simp
  have hm : 1 < m := by
    dsimp [m]
    have hexp : 1 ≤ node.r+node.v3C+1 := by omega
    have hpow : 3 ≤ 3^(node.r+node.v3C+1) := by
      calc
        3 = 3^1 := by norm_num
        _ ≤ 3^(node.r+node.v3C+1) :=
          Nat.pow_le_pow_right (by decide) hexp
    omega
  have hp' : 2^(1458*T)%m=1 := by
    simpa [m] using hperiod
  have hc' :
      2^(1458*r0+node.s)%m ≠
        (node.C-node.b+node.c)%m := by
    simpa [m] using hbase
  have hno := no_hit_fixed_period m (1458*r0+node.s)
      (node.C-node.b+node.c) (1458*T) k hm hp' hc'
  have hexp : 1458*t+node.s =
      (1458*r0+node.s)+(1458*T)*k := by rw [ht]; ring
  rw [hexp] at hmod
  exact hno hmod

/-- Positive-offset counterpart of blank_even_inverse_cases. It uses the
original EvenReach last edge and the source-checked positive-offset algebra
split, and is uniform in b (hence covers all positive nodes in the mixed tree). -/
theorem blank_even_inverse_cases_pos
    {y d b n : Nat} (hy : SheepEven.EvenReach 10 y)
    (hnot : y ≠ 10) (hpower : d*y = 2^n+b) :
    (∃ x a h v u : Nat,
      SheepEven.EvenReach 10 x ∧
      1 ≤ a ∧ 5 ≤ v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧ y=1+3^h*u ∧
      (d*3^h)*(2^(a+1)+1)*v + 2*a*(d*3^h) + 2^(h+1)*d =
        2^(n+h+1)+2^(h+1)*b+3*(d*3^h)) ∨
    (∃ x a h u : Nat,
      SheepEven.EvenReach 10 x ∧
      1 ≤ a ∧ u%2=1 ∧ x=3*2^a ∧ y=1+3^h*u ∧
      (d*3^h)*(3*2^a+a+2)+2^h*d = 2^(n+h)+2^h*b) := by
  obtain ⟨x,hreach,hedge⟩ :=
    SheepEvenReachInverse.reach_last_edge hy (by omega)
  have hx : x%2=0 :=
    SheepEvenReachInverse.even_reach_preserves_even hreach (by decide)
  have hEdge := SheepEvenSourceAlgebra.even_edge_to_algebra hx hedge
  rcases SheepEvenInverseAlgebra.edge_inverse_cases x y d n b hEdge hpower with
    hg | hs
  · rcases hg with ⟨a,h,v,u,ha,hv,hvodd,huodd,hxdef,hydef,hEq⟩
    exact Or.inl ⟨x,a,h,v,u,hreach,ha,hv,hvodd,huodd,hxdef,hydef,hEq⟩
  · rcases hs with ⟨a,h,u,ha,huodd,hxdef,hydef,hEq⟩
    exact Or.inr ⟨x,a,h,u,hreach,ha,huodd,hxdef,hydef,hEq⟩

/-- Reverse-closed affine basins pull back along every original EvenReach
path. This is the finite-graph induction used by the five inverse trees. -/
theorem evenReach_parent_closed {P : Nat → Prop}
    {x y : Nat}
    (hclosed : ∀ {x y}, P y → SheepEven.EvenEdge x y → P x)
    (h : SheepEven.EvenReach x y) (hy : P y) : P x := by
  induction h with
  | refl x => exact hy
  | @cons x y z edge tail ih => exact hclosed (ih hy) edge

/-- A node-wise predecessor classifier induces reverse closure of the
finite affine basin. -/
theorem affineBasin_parent_closed
    {t : Nat} {nodes : List AffineNode}
    (hnode : ∀ node, node ∈ nodes →
      ∀ {x y}, affineNodeValue t node y →
        SheepEven.EvenEdge x y → affineBasin t nodes x) :
    ∀ {x y}, affineBasin t nodes y →
      SheepEven.EvenEdge x y → affineBasin t nodes x := by
  intro x y hy hedge
  rcases hy with ⟨node,hmem,hval⟩
  exact hnode node hmem hval hedge

/-- Once the affine basin is reverse-closed and excludes 10, no node in it
can be reached from the blank even root. -/
theorem no_evenReach_of_affineBasin
    {t y : Nat} {nodes : List AffineNode}
    (hclosed : ∀ {x y}, affineBasin t nodes y →
      SheepEven.EvenEdge x y → affineBasin t nodes x)
    (hnot10 : ¬ affineBasin t nodes 10)
    (hroot : affineBasin t nodes y) :
    ¬ SheepEven.EvenReach 10 y := by
  intro hreach
  have h10 := evenReach_parent_closed hclosed hreach hroot
  exact hnot10 h10

#print axioms blank_even_inverse_cases_pos
#print axioms evenReach_parent_closed
#print axioms affineBasin_parent_closed
#print axioms no_evenReach_of_affineBasin

end SheepPower1458
