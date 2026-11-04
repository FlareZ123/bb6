import SecondGap
import ReverseResidue

namespace CascadeSecondGapBand
open CascadeSource CascadeSweep CascadeTwoLevelGap

private theorem pow_dominates : ∀ m:Nat, m+1 ≤2^m := by
  intro m
  induction m with
  | zero => decide
  | succ m ih =>
    rw [Nat.pow_succ]
    omega

/-- In the dyadic scale of every surviving fatal-index class n≡4 or5 (mod6),
    a genuine even-return predecessor two generations earlier has the
    same non-odd residue class 1 (mod3). -/
private theorem mod_parent (n h x : Nat) (hn : 4 ≤ n)
  (hc:n%6=4∨n%6=5) (hh:h%3=1)
  (hrel:2*h=8*2^(n-2)+x+(n-2)) : x%3=1 := by
  have hn2 : (n-2)+2=n := by omega
  have hmod := congrArg (fun u:Nat=>u%3) hrel
  rcases hc with hc4|hc5
  · have hpar : (n-2)%2=0 := by omega
    have hpow := (ReverseResidue.pow3_parity (n-2)).1 hpar
    omega
  · have hpar : (n-2)%2=1 := by omega
    have hpow := (ReverseResidue.pow3_parity (n-2)).2 hpar
    omega

/-- An *infinite interval family* of genuine blank-root reset heights is
    unreachable: in the middle of the scale-(n-2) even-return band,
    all heights congruent to 1 modulo 3 have a unique required parent
    in the adjacent dyadic gap. They cannot occur at any depth of the
    true post-initial C(2,0) orbit.

    The condition is scale-uniform, for every n≥6 with n%6∈{4,5},
    and excludes the entire arithmetic-progression slice of the middle
    interval 12*2^(n-2)+(n-2) ≤ 2*h ≤
    14*2^(n-2)+(n-2)-2.

    This is a new root-structural obstruction for reset states, separate
    from the finite-height target certificates. It does not exclude the
    entire complementary fatal index family. -/
theorem middle_band_forbidden (n h : Nat) (hn : 6 ≤ n)
  (hc : n%6=4 ∨ n%6=5)
  (hmod : h%3=1)
  (hl : 12*2^(n-2)+(n-2) ≤ 2*h)
  (hu : 2*h+2 ≤ 14*2^(n-2)+(n-2)) :
  ¬ ReachC (2,0) (h,0) := by
  let m := n-2
  let p := 2^m
  have hm : 4 ≤ m := by dsimp [m]; omega
  have hp4 : 4 ≤ p := by
    have hp := Nat.pow_le_pow_right (by decide : 0<2) (show 2≤m by omega)
    simpa [p] using hp
  have hmp : m ≤ p := by
    have hh := pow_dominates m
    dsimp [p]
    omega
  have hl' : 12*p+m ≤2*h := by simpa [m,p] using hl
  have hu' : 2*h+2 ≤14*p+m := by simpa [m,p] using hu
  let x : Nat := 2*h-(8*p+m)
  have he : 2*h=8*p+x+m := by dsimp [x];omega
  have hb : 6*p-1 ≤h ∧ h ≤8*p-3 := by omega
  have hxlo:4*p-3 < x := by omega
  have hxhi:x<6*p-1 := by omega
  have hxmod:x%3=1 := by
    have hr:2*h=8*2^(n-2)+x+(n-2) := by simpa [m,p] using he
    exact mod_parent n h x (by omega) hc hmod hr
  exact root_excludes_two_level_gap m h x (by omega)
    (by omega) (by simpa [p] using hb)
    (by simpa [p] using he) (by omega)
    (by simpa [p] using hxlo) (by simpa [p] using hxhi)

#print axioms middle_band_forbidden
end CascadeSecondGapBand
