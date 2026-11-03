import Lean.Elab.Tactic.Omega

namespace BB6.Agent31PacketRank

structure Packet where
  a : Nat
  q : Nat
  p : Nat
  deriving Repr, DecidableEq

def rank (c : Packet) : Nat := c.q + c.p

/-- Abstract source-macro continuation of M(a,q,p), only while the next
    endpoint stays in M. none represents exit from this shape grammar or
    an unclassified low-p E boundary; it never means machine halt. -/
def advance (c : Packet) : Option Packet :=
  if c.a % 3 = 2 then
    if c.q = 0 then none
    else some ⟨8 * ((c.a-2)/3) + 10, c.q-1, c.p⟩
  else if c.a % 3 = 1 then
    if c.p < 3 then none
    else some ⟨8 * ((c.a-4)/3) + 9, c.q+2, c.p-3⟩
  else none

/-- Every B/E source-macro recurrence inside M reduces q+p by exactly one. -/
theorem advance_rank {c d : Packet} (h : advance c = some d) :
    rank d + 1 = rank c := by
  unfold advance at h
  split at h
  · split at h
    · contradiction
    · have hq : c.q ≠ 0 := by assumption
      injection h with heq
      subst d
      simp only [rank]
      omega
  · split at h
    · split at h
      · contradiction
      · have hp : ¬c.p < 3 := by assumption
        injection h with heq
        subst d
        simp only [rank]
        omega
    · contradiction

/-- The well-founded recursion is accepted by the Lean termination checker.
    No infinite run can remain in the guarded packet-only recurrence. -/
def normalizeWithCount (c : Packet) : Nat × Packet :=
  match h : advance c with
  | none => (0, c)
  | some d =>
      let (n, endpoint) := normalizeWithCount d
      (n+1, endpoint)
termination_by rank c
decreasing_by
  have hr := advance_rank h
  omega

#print axioms advance_rank
#print axioms normalizeWithCount
end BB6.Agent31PacketRank
