import SignedRayBlock

namespace BB6.Agent32EightRayWindow
open BB6.Agent32SignedRayBlock

/-- Every coefficient pair of the eight-ray gate satisfies Q ≡ P mod 3.
    This signed form equals twice the original ray residual and uses
    smaller coefficients than the sixfold residual. -/
theorem primitive_form (P Q B L m gamma x y : Int)
    (hB : 3*B=4*P-Q) (hx : x=2*(L-4*m)-gamma) (hy : y=6*m) :
    P*x+B*y+P*gamma=2*(P*L-Q*m) := by
  have h := ray_form P Q L m gamma x y hx hy
  have hm : 3*(P*x+B*y+P*gamma) = 3*P*x+(4*P-Q)*y+3*P*gamma := by
    simp only [Int.mul_add, ← Int.mul_assoc, hB]
  omega

/-- For the transported ray index, all eight two-sided residuals are
    dominated by 2*(237*ell+2536). The original correction-only mass
    buffer, with one additional low digit, already dominates this. -/
theorem buffer_dominates (ell k : Nat) (hell : 5 ≤ ell)
    (hk : 34*ell+122 < 3^k) : 2*(237*ell+2536) < 3^(k+3) := by
  rw [Nat.pow_add]
  change 2*(237*ell+2536) < 3^k*27
  omega

def coeffs : List (Int × Int) := [(1,-39),(40,39),(13,-3),(16,3),(4,-21),(25,21),(7,-12),(19,12)]

/-- Integer formulation of Agent27's eightRayCone with N=n+3. -/
def gate (n L m : Int) : Prop :=
  (L≤121*m+(214*(n+3)+23*n+1183) ∧ 121*m≤L+(2*(n+3)+3*n+225)) ∨
  (40*L≤43*m+(45*(n+3)+3*n+321) ∧ 43*m≤40*L+(93*(n+3)+23*n+541)) ∨
  (13*L≤61*m+(94*(n+3)+3*n+501) ∧ 61*m≤13*L+(26*(n+3)+23*n+283)) ∨
  (16*L≤55*m+(81*(n+3)+23*n+523) ∧ 55*m≤16*L+(33*(n+3)+3*n+219)) ∨
  (4*L≤79*m+(136*(n+3)+10*n+743) ∧ 79*m≤4*L+(8*(n+3)+10*n+200)) ∨
  (25*L≤37*m+(45*(n+3)+10*n+314) ∧ 37*m≤25*L+(57*(n+3)+10*n+335)) ∨
  (7*L≤64*m+(106*(n+3)+10*n+584) ∧ 64*m≤7*L+(14*(n+3)+10*n+203)) ∨
  (19*L≤40*m+(54*(n+3)+10*n+353) ∧ 40*m≤19*L+(42*(n+3)+10*n+266))

def safeBlock (b d x y gamma : Int) : Prop :=
  ∀ (P B : Int), (P,B) ∈ coeffs →
    ((P*x+B*y+P*gamma)/b)%d ≠ 0 ∧ ((P*x+B*y+P*gamma)/b)%d ≠ d-1

/-- Exact eight-ray avoidance follows from the eight finite signed-block
    tests at any valid depth; no independent per-ray carry assumptions. -/
theorem safe_block_excludes_gate (n ell L m gamma x y b d : Int)
    (hn : 0≤n) (hindex : n≤ell+3)
    (hx : x=2*(L-4*m)-gamma) (hy : y=6*m)
    (hb : 2*(237*ell+2536)<b) (hbp : 0<b) (hd : 0<d)
    (hs : safeBlock b d x y gamma) : ¬gate n L m := by
  intro h
  unfold gate at h
  rcases h with h|h|h|h|h|h|h|h
  all_goals
    obtain ⟨hl,hu⟩ := h
    have he : ∃ P B Q : Int, (P,B)∈coeffs ∧ 3*B=4*P-Q ∧
        -2*(237*ell+2536)≤2*(P*L-Q*m) ∧ 2*(P*L-Q*m)≤2*(237*ell+2536) := by
      first
      | exact ⟨1,-39,121, by decide, by decide, by omega, by omega⟩
      | exact ⟨40,39,43, by decide, by decide, by omega, by omega⟩
      | exact ⟨13,-3,61, by decide, by decide, by omega, by omega⟩
      | exact ⟨16,3,55, by decide, by decide, by omega, by omega⟩
      | exact ⟨4,-21,79, by decide, by decide, by omega, by omega⟩
      | exact ⟨25,21,37, by decide, by decide, by omega, by omega⟩
      | exact ⟨7,-12,64, by decide, by decide, by omega, by omega⟩
      | exact ⟨19,12,40, by decide, by decide, by omega, by omega⟩
    obtain ⟨P,B,Q,hmem,hB,hlo,hhi⟩ := he
    have hh := hs P B hmem
    have hf := primitive_form P Q B L m gamma x y hB hx hy
    rcases small_signed_block (P*x+B*y+P*gamma) b d hbp hd (by omega) (by omega) with hz|hz
    · exact hh.1 hz
    · exact hh.2 hz

#print axioms safe_block_excludes_gate
end BB6.Agent32EightRayWindow
