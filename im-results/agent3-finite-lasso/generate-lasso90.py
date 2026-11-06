"""Generate a source-checkable list of all read-one, three-row finite lassos.

The bounded DFS branches on the first *physically read* unassigned slot.
Each positive certificate has an exact whole-tape repeated configuration.
The enumeration cutoffs are limits on discovery, not nonhalting proofs.
"""
from collections import Counter
from pathlib import Path
import fcntl
import os
import tempfile
import sys

MOVES = [(w, direction, state) for w in range(2) for direction in (-1, 1) for state in range(6)]
MAX_STEPS = 20
patterns = []
rules = {}
seen = {}

def search(state, head, ones, step):
    cfg = (state, head, frozenset(ones))
    prior = seen.get(cfg)
    if prior is not None:
        if len(rules) == 3 and any(slot[1] == 1 for slot in rules):
            patterns.append((tuple(rules.items()), prior, step - prior))
        return
    if step == MAX_STEPS:
        return
    slot = (state, int(head in ones))
    if slot not in rules:
        if len(rules) == 3:
            return
        for move in MOVES:
            rules[slot] = move
            advance(state, head, ones, step, move)
            del rules[slot]
    else:
        advance(state, head, ones, step, rules[slot])

def advance(state, head, ones, step, move):
    cfg = (state, head, frozenset(ones))
    seen[cfg] = step
    write, direction, newstate = move
    was_marked = head in ones
    if write:
        ones.add(head)
    else:
        ones.discard(head)
    search(newstate, head + direction, ones, step + 1)
    if was_marked:
        ones.add(head)
    else:
        ones.discard(head)
    del seen[cfg]

search(0, 0, set(), 0)
assert len(patterns) == 90, len(patterns)
assert len(set(patterns)) == 90

def conflicting(first, second):
    a = dict(first[0]); b = dict(second[0])
    return any(key in b and b[key] != value for key, value in a.items())
assert all(conflicting(p, q) for i, p in enumerate(patterns) for q in patterns[i + 1 :])

header = '''import Agent3FiniteLasso
import Lean.Elab.Tactic.Omega

namespace BB6Coverage

/-- Every row is an actual ordinary instruction; the source's actual
    blank run follows only these rows before an exact finite lasso. -/
structure LassoTriple where
  first : Slot × Move
  second : Slot × Move
  third : Slot × Move
  entry : Nat
  period : Nat

/-- A deterministic original-blank DFS: three physically encountered
    distinct slots, first exact recurring finite-tape configuration by
    20 ordinary moves, and at least one visited read-one input. -/
def readOneTriples : Array LassoTriple := #[
'''

def as_lean(slotmove):
    (s, bit), (write, direction, nxt) = slotmove
    return f'(({s},{"true" if bit else "false"}), ⟨{"true" if write else "false"},{"true" if direction > 0 else "false"},{nxt}⟩)'

entries = []
for moves, entry, period in patterns:
    entries.append('  { first := ' + as_lean(moves[0]) + ', second := ' + as_lean(moves[1]) +
        ', third := ' + as_lean(moves[2]) + f', entry := {entry}, period := {period}' + ' }')

footer = '''
]

def tripleAt (i : Fin readOneTriples.size) : LassoTriple := readOneTriples[i]

def tripleTable (s : LassoTriple) : PartialMachine := fun slot =>
  if slot = s.first.1 then some (some s.first.2)
  else if slot = s.second.1 then some (some s.second.2)
  else if slot = s.third.1 then some (some s.third.2)
  else none

/-- Kernel-checked finite full-tape lasso for *all ninety* generated
    witnesses. Every total compatible table consequently never halts. -/
theorem every_triple_lasso (i : Fin readOneTriples.size) :
    finiteLassoCheck (tripleTable (tripleAt i))
      (tripleAt i).entry (tripleAt i).period = true := by
  revert i
  decide

theorem every_triple_period_positive (i : Fin readOneTriples.size) :
    0 < (tripleAt i).period := by
  revert i
  decide

theorem every_triple_cover (i : Fin readOneTriples.size) (bound : Nat) :
    Cover (DecidedBelow bound) (tripleTable (tripleAt i)) :=
  finiteLassoCheck_sound _ _ _ _ (every_triple_period_positive i)
    (every_triple_lasso i)

theorem every_triple_mass (i : Fin readOneTriples.size) :
    cylinderMass (tripleTable (tripleAt i)) = 25^9 := by
  revert i
  decide

/-- Finite explicit overlap witness. A checked conflicting assigned row
    makes intersection of compatible full-table cylinders impossible. -/
def tripleConflict (a b : LassoTriple) : Bool :=
  auditSlots.any (fun slot =>
    match tripleTable a slot, tripleTable b slot with
    | some t, some u => decide (t ≠ u)
    | _,_ => false)

theorem tripleConflict_sound (a b : LassoTriple) (m : Machine)
    (ha : compatible (tripleTable a) m)
    (hb : compatible (tripleTable b) m) :
    tripleConflict a b = false := by
  apply List.any_eq_false.mpr
  intro slot _
  cases h1 : tripleTable a slot with
  | none => simp [h1]
  | some t =>
      cases h2 : tripleTable b slot with
      | none => simp [h1,h2]
      | some u =>
          have he : t = u := (ha slot t h1).symm.trans (hb slot u h2)
          simp [h1,h2,he]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem all_triples_conflict (i j : Fin readOneTriples.size)
    (h : i ≠ j) : tripleConflict (tripleAt i) (tripleAt j) = true := by
  revert i j
  decide

theorem all_triples_disjoint (i j : Fin readOneTriples.size)
    (h : i ≠ j) (m : Machine) :
    ¬ (compatible (tripleTable (tripleAt i)) m ∧
       compatible (tripleTable (tripleAt j)) m) := by
  rintro ⟨hi,hj⟩
  have hc := all_triples_conflict i j h
  have hn := tripleConflict_sound (tripleAt i) (tripleAt j) m hi hj
  simp [hn] at hc

theorem readOneTriples_size : readOneTriples.size = 90 := by decide

#print axioms every_triple_lasso
#print axioms every_triple_cover
#print axioms every_triple_mass
#print axioms all_triples_conflict
#print axioms all_triples_disjoint
end BB6Coverage
'''

source = header + ',\n'.join(entries) + footer
out = Path(sys.argv[1]) if len(sys.argv) > 1 else Path('im-results/agent3-finite-lasso/Agent3Lasso90.lean')
lock = out.with_suffix('.lean.lock')
with lock.open('w') as lk:
    fcntl.flock(lk, fcntl.LOCK_EX)
    fd, tmp = tempfile.mkstemp(dir=out.parent, prefix='.lasso90-')
    try:
        with os.fdopen(fd, 'w', encoding='utf-8') as f:
            f.write(source)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, out)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)
print('certificates', len(patterns), 'source bytes', len(source.encode()))
