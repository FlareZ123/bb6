import PlaneTileCover
import PlaneReverseSource
import ReverseBlockCompose

namespace BB6.Agent43WordPlane
open BB6.Agent43Matrix64 (Rows)
open BB6.Agent9PlaneReverse
open BB6.Agent45ReverseBlock

def ReverseCover (q : Nat) (ys : List Nat) (starts ends : Nat → Prop) : Prop :=
  ∀ z c, Walk (q+ys.length) z ys c → ends z → starts c

theorem reverseCover_append (q : Nat) (xs ys : List Nat) (starts mid ends : Nat → Prop)
    (h1 : ReverseCover q xs starts mid) (h2 : ReverseCover (q+xs.length) ys mid ends) :
    ReverseCover q (xs++ys) starts ends := by
  intro z c hw hz
  have hw' : Walk (q+xs.length+ys.length) z (xs++ys) c := by simpa [Nat.add_assoc] using hw
  obtain ⟨d,ht,hp⟩ := walk_split _ _ _ _ hw'
  have he : q+xs.length+ys.length-ys.length=q+xs.length := by omega
  rw [he] at hp
  exact h1 d c hp (h2 z d ht hz)

/-- Direct transport to the existing exact reverse Walk. No evaluation of
    a global bitset or assumption of an exact (rather than covering) image. -/
theorem reverseCover_plane (q : Nat) (ys : List Nat) (ends starts : Rows) (lane : Nat → Rows)
    (hk : 6≤ys.length) (hys : ∀ y∈ys,y≤1) (he : Words64 ends)
    (hchecks : PlaneChecks (2^ys.length) (digits ys) q (q+ys.length) (wordWeight q ys.length) ends lane)
    (houtput : OutputChecks (2^(ys.length-6)) q lane starts) :
    ReverseCover q ys (WordMem starts) (WordMem ends) := by
  intro z c hw hz
  have h := (walk_iff_planes q c ys (WordMem ends) hys).1 ⟨z,hz,hw⟩
  have hm := plane_checks_cover _ _ _ _ _ _ _ _ (Nat.two_pow_pos _) (target_lt ys hys) he hchecks h
  have hM : 2^ys.length=64*2^(ys.length-6) := by
    calc
      2^ys.length = 2^(6+(ys.length-6)) := congrArg (fun j : Nat => 2^j) (by omega)
      _ = _ := by rw [Nat.pow_add]; rfl
  rw [hM] at hm
  have hc := walk_bound hw
  rw [Nat.add_sub_cancel] at hc
  exact output_checks_cover _ _ _ _ _ (Nat.two_pow_pos _) hc houtput hm

/-- Sparse stages can use a different checker while retaining the same
    composable interface. -/
theorem reverseCover_sparse (q : Nat) (ys : List Nat) (starts ends : Nat → Prop)
    (hfit : 2^(ys.length+1)≤q+ys.length)
    (hc : ∀ z, z<q+ys.length → ends z →
      match fast (q+ys.length) ys.length (2^ys.length*z+digits ys) with
      | none => True
      | some r => starts r) :
    ReverseCover q ys starts ends := by
  intro z c hw hz
  have h := hc z (start_bound hw) hz
  rw [fast_eq_some hw hfit] at h
  exact h

#print axioms reverseCover_append
#print axioms reverseCover_plane
#print axioms reverseCover_sparse
end BB6.Agent43WordPlane
