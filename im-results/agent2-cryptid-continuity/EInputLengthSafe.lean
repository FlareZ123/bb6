import Lean.Elab.Tactic.Omega
import EAllDepthSafe

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace BB6.EInputLengthSafe
open CryptidBoundary BB6.Agent31SecondSource
open BB6.EAllDepthSafe

/-- A concrete syntactic representation of the regular initial right tape
    X(k,q)=I_(3k+4)((01)^q 1), for q>=1. -/
def regularInput (k q : Nat) : Cfg :=
  init (List.replicate (3*k+2) true ++
    false :: (pairs (q-1) ++ [true,true]))

theorem start_is_regular (t h : Nat) :
    start t h = regularInput (3*t+1) (h+3) := by
  have hh : h+3-1=h+2 := by omega
  simp [start,regularInput,hh]

theorem pair_length (n : Nat) : (pairs n).length=2*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [pairs,ih]
    omega

theorem regular_right_length (k q : Nat) (hq : 0<q) :
    (regularInput k q).r.length = 3*k+4+2*q+1 := by
  have hdec : q-1+1=q := by omega
  simp [regularInput, init, pair_length, List.length_append]
  omega

theorem start_right_length (t h : Nat) :
    (start t h).r.length = 3*(3*t+1)+4+2*(h+3)+1 := by
  rw [start_is_regular]
  exact regular_right_length (3*t+1) (h+3) (by omega)

/-- Quantitative source-level theorem directly stated over the actual Cfg
    tape length, so no informal connection from a symbolic input k,q to
    a shorter real machine input is needed. Every m>0 admits a finite
    prepared physical F/0 section with ≤120*3^m tape cells and no raw
    original-TM halting at any time t≤64^m. -/
theorem bounded_tape_unbounded_raw_runtime (m : Nat) (hm : 0<m) :
    ∃ c : Cfg,
      c.st=5 ∧ c.l=[] ∧ c.h=false ∧
      c.r.length ≤ 120*3^m ∧
      ∀ t, t≤64^m → (run t c).st≠6 := by
  obtain ⟨k,q,U,p,_,_,hsize,hcases⟩ :=
    regular_prepared_no_halt_through_64pow m hm
  rcases hcases with he | ho
  · obtain ⟨r,v,hme,hke,hqe,hpe,hsafe⟩ := he
    refine ⟨start (3*v+2) (3*r), rfl, rfl, rfl, ?_, hsafe⟩
    have hlen := start_right_length (3*v+2) (3*r)
    rw [hke,hqe] at hsize
    rw [hlen]
    omega
  · obtain ⟨r,v,hmo,hko,hqo,hpo,hsafe⟩ := ho
    refine ⟨start (3*v+1) (3*r+3), rfl, rfl, rfl, ?_, hsafe⟩
    have hlen := start_right_length (3*v+1) (3*r+3)
    rw [hko,hqo] at hsize
    rw [hlen]
    omega

#print axioms start_is_regular
#print axioms pair_length
#print axioms regular_right_length
#print axioms bounded_tape_unbounded_raw_runtime
end BB6.EInputLengthSafe
