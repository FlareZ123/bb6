"""Generate Lean-kernel-checkable D-machine E-seam finite-invariant proofs.

Input: the existing Agent31 ESeamClosedStates.txt certificate.
Generated proof modules check every leaf under the exact literal D table.
Lean, rather than this generator, establishes all member-safety and closure
facts. Requires Python 3.10+ and filelock.
"""
from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path
from filelock import FileLock

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "agent31-d-exceptional" / "ESeamClosedStates.txt"
BLOCK_SIZE = 32


def write_atomic(path: Path, content: str) -> None:
    with tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", newline="\n", dir=path.parent,
        prefix=path.name + ".", suffix=".tmp", delete=False,
    ) as temporary:
        temporary.write(content)
        temporary.flush()
        os.fsync(temporary.fileno())
        temporary_name = temporary.name
    os.replace(temporary_name, path)


def balanced_tree(numbers: list[int]) -> str:
    if len(numbers) == 1:
        return f"(Tree.leaf {numbers[0]})"
    midpoint = len(numbers) // 2
    return (
        f"(Tree.branch {numbers[midpoint]} "
        f"{balanced_tree(numbers[:midpoint])} "
        f"{balanced_tree(numbers[midpoint:])})"
    )


def block_tree(blocks: list[list[int]], indices: list[int]) -> str:
    if len(indices) == 1:
        return f"block{indices[0]}"
    midpoint = len(indices) // 2
    return (
        f"(Tree.branch {blocks[indices[midpoint]][0]} "
        f"{block_tree(blocks, indices[:midpoint])} "
        f"{block_tree(blocks, indices[midpoint:])})"
    )


LEAN_BASE = r'''import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.TreeCert

inductive Tree where
  | leaf : Nat → Tree
  | branch : Nat → Tree → Tree → Tree
  deriving Repr

def member : Tree → Nat → Bool
  | .leaf k, v => k == v
  | .branch threshold lo hi, v =>
      if v < threshold then member lo v else member hi v

__BLOCKS__

def root : Tree := __ROOT__

def encode (off state tape : Nat) : Nat := 256*tape + 8*off + state

-- Original D 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.
-- (write, moveLeft, nextState), states A..F indexed 0..5.
def table (s bit : Nat) : Nat × Bool × Nat :=
  if s == 0 then if bit == 0 then (1,false,1) else (0,false,4)
  else if s == 1 then if bit == 0 then (1,true,2) else (0,false,0)
  else if s == 2 then if bit == 0 then (1,true,0) else (1,true,3)
  else if s == 3 then if bit == 0 then (1,true,2) else (1,true,5)
  else if s == 4 then if bit == 0 then (0,true,2) else (0,true,1)
  else (1,true,4)

-- Low 18 tape bits cover [-10,7]; bit offset 10 represents position 0.
-- Marker first contact is at -9 / offset 1 and must be C/1.
def safe (v : Nat) : Bool :=
  let state := v % 8
  let off := (v / 8) % 32
  let bits := v / 256
  (1 <= off && off <= 17 && state <= 5 && bits < 262144) &&
  (off != 1 || (state == 2 && bits.testBit 1))

-- Nondeterministic right-excursion return allows all six live states.
-- Halt F/1 and physical blank-left F/0 are terminating events.
def successors (v : Nat) : List Nat := Id.run do
  let state := v % 8
  let off := (v / 8) % 32
  let bits := v / 256
  let scanned := if bits.testBit off then 1 else 0
  if off == 1 then return []
  if state == 5 && scanned == 1 then return []
  if state == 5 && scanned == 0 && bits.land ((1 <<< off) - 1) == 0 then return []
  let (write, moveLeft, nextState) := table state scanned
  let mask := 1 <<< off
  let nextBits := if write == 1 then bits.lor mask else bits.land (262143 - mask)
  let nextOff := if moveLeft then off - 1 else off + 1
  if nextOff == 18 then
    return (List.range 6).map (fun s => encode 17 s nextBits)
  return [encode nextOff nextState nextBits]

def validAndClosed (v : Nat) : Bool :=
  safe v && (successors v).all (member root)

def allGood : Tree → Bool
  | .leaf k => validAndClosed k
  | .branch _ lo hi => allGood lo && allGood hi

/-- A generic soundness proof for any binary-tree finite certificate. -/
theorem certified_member {t : Tree} (h : allGood t = true) {v : Nat}
    (hv : member t v = true) : validAndClosed v = true := by
  induction t with
  | leaf k =>
      simp only [allGood] at h
      simp only [member, beq_iff_eq] at hv
      cases hv
      exact h
  | branch threshold lo hi ihLo ihHi =>
      have hp : allGood lo = true ∧ allGood hi = true := by
        simpa only [allGood, Bool.and_eq_true] using h
      simp only [member] at hv
      split at hv
      · exact ihLo hp.1 hv
      · exact ihHi hp.2 hv

end BB6.TreeCert
'''


def master_file(count: int) -> str:
    imports = "".join(f"import ESeamTreeBlock{i}\n" for i in range(count))
    lemmas = ",\n".join(f"    block{i}_good" for i in range(count))
    return imports + r'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.TreeCert

theorem root_good : allGood root = true := by
  simp only [root, allGood]
  simp only [
''' + lemmas + r'''
  ]
  decide

private def allSeeds : Bool :=
  (List.range 128).all (fun r => member root (encode 10 4 (171+2048*r)))
theorem all_seeds : allSeeds = true := by decide

theorem members_validAndClosed (v : Nat) (h : member root v = true) :
    validAndClosed v = true := certified_member root_good h

theorem safe_member (v : Nat) (h : member root v = true) :
    safe v = true :=
  (show safe v = true ∧ (successors v).all (member root) = true by
    simpa only [validAndClosed, Bool.and_eq_true] using
      (members_validAndClosed v h)).1

theorem successor_closed (v w : Nat) (h : member root v = true)
    (hw : w ∈ successors v) : member root w = true := by
  have hp : safe v = true ∧ (successors v).all (member root) = true := by
    simpa only [validAndClosed, Bool.and_eq_true] using
      (members_validAndClosed v h)
  exact (List.all_eq_true.mp hp.2) w hw

#print axioms root_good
#print axioms all_seeds
#print axioms members_validAndClosed
#print axioms safe_member
#print axioms successor_closed
end BB6.TreeCert
'''


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python make_e_seam_kernel.py OUTPUT_DIRECTORY")
    numbers = [
        int(line) for line in SOURCE.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    if len(numbers) != 6399 or numbers != sorted(set(numbers)):
        raise ValueError("Expected 6399 distinct, sorted certificate states")
    blocks = [numbers[i:i + BLOCK_SIZE] for i in range(0, len(numbers), BLOCK_SIZE)]
    output = Path(sys.argv[1]).resolve()
    output.mkdir(parents=True, exist_ok=True)
    with FileLock(str(output / ".generate.lock")):
        body = "\n".join(
            f"def block{i} : Tree := {balanced_tree(b)}"
            for i, b in enumerate(blocks)
        )
        base = LEAN_BASE.replace("__BLOCKS__", body).replace(
            "__ROOT__", block_tree(blocks, list(range(len(blocks))))
        )
        write_atomic(output / "ESeamTreeBase.lean", base)
        for i in range(len(blocks)):
            block_source = (
                "import ESeamTreeBase\n"
                "set_option maxRecDepth 100000\n"
                "set_option maxHeartbeats 0\n"
                "namespace BB6.TreeCert\n"
                f"theorem block{i}_good : allGood block{i} = true := by decide\n"
                f"#print axioms block{i}_good\n"
                "end BB6.TreeCert\n"
            )
            write_atomic(output / f"ESeamTreeBlock{i}.lean", block_source)
        write_atomic(output / "ESeamTreeMaster.lean", master_file(len(blocks)))
    print(f"Generated {len(blocks)} Lean proof blocks, {len(numbers)} states")


if __name__ == "__main__":
    main()
