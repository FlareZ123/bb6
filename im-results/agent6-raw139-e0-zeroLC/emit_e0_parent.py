"""Compose the 24 D0 branches into the complete E0=0LC residual Cover."""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parent
for path in (
    ROOT.parent / "agent48-raw139-f1-oneLA",
    ROOT.parent / "agent48-raw139-f1-oneRA",
):
    sys.path.insert(0, str(path))
sys.path.insert(0, str(ROOT))

from scan import scan
from emit_family import code_name, bl

BASE_PARENT = [7, 24, 11, 24, 14, 24, 24, 16, 8, 11, 24, 24]
BROAD_CODES = [0, 1, 2, 3, 5, 6, 7, 11, 20, 21, 22, 23]
SPECIAL_CODE = 9  # D0=0RC, source-accepted at weighted bound 775.
GLOBAL_BOUND = 80377


def move_expr(code: int) -> str:
    return f"⟨{bl(code & 2)},{bl(code & 1)},{code // 4}⟩"


def branch_proof(code: int, cycle_data: dict[int, tuple]) -> str:
    move = move_expr(code)
    if code in BROAD_CODES:
        name = code_name(code)
        ns = f"BB6.Agent6E0ZeroLC.D0{name}"
        return f"""    · have he : child {move} = {ns}.parent := by
        apply BB6.Agent31ThreeHole.tableOK_sound
        decide
      rw [he]
      exact Cover.leaf _ (fun m hm k d hk hd =>
        Nat.le_trans ({ns}.all_completions_weighted m hm k d hk hd) (by omega))
"""
    if code == SPECIAL_CODE:
        ns = "BB6.Agent14Raw139D0ZeroRC"
        return f"""    · have he : child {move} = {ns}.parent := by
        apply BB6.Agent31ThreeHole.tableOK_sound
        decide
      rw [he]
      exact Cover.leaf _ (fun m hm k d hk hd =>
        Nat.le_trans ({ns}.all_completions_weighted m hm k d hk hd) (by omega))
"""
    entry, period, right, boundary = cycle_data[code]
    return (
        f"    · exact cycleCover B _ {entry} {period} {bl(right)} "
        f"({boundary}) (by decide) (by decide)\n"
    )


def main():
    if len(sys.argv) != 3:
        raise SystemExit("usage: emit_e0_parent.py WORKDIR OUTPUT_DIR")
    work = Path(sys.argv[1])
    out = Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)

    summary = json.loads((work / "broad_specs_summary.json").read_text())
    branch_bounds = [row["weighted_bound"] for row in summary["branches"]]
    if len(branch_bounds) != 12 or max(branch_bounds) != GLOBAL_BOUND:
        raise AssertionError(f"unexpected broad branch bounds: {branch_bounds}")
    if any(bound > GLOBAL_BOUND for bound in branch_bounds):
        raise AssertionError(f"broad branch exceeds parent bound: {branch_bounds}")

    first = scan(BASE_PARENT, 250)
    if first[0] != "hole" or first[2] != 6:
        raise AssertionError(f"E0 parent does not first query D0: {first}")
    query_step = int(first[1])

    direct_codes = [
        code for code in range(24)
        if code not in BROAD_CODES and code != SPECIAL_CODE
    ]
    cycle_data = {}
    for code in direct_codes:
        child = BASE_PARENT.copy()
        child[6] = code
        result = scan(child, 250)
        if result[0] != "cycle":
            raise AssertionError(f"D0 code {code} was expected to be a direct cycle: {result}")
        cycle_data[code] = tuple(result[1:])

    for code in BROAD_CODES + [SPECIAL_CODE]:
        child = BASE_PARENT.copy()
        child[6] = code
        result = scan(child, 250)
        if result[0] != "hole":
            raise AssertionError(f"D0 code {code} should enter a covered child: {result}")

    if len(direct_codes) != 11:
        raise AssertionError(f"expected 11 direct cycle children, got {direct_codes}")

    imports = [
        "import FastThreeHoleAudit",
        "import A6ChunkSupport",
        "import Raw139D0ZeroRCCover",
    ]
    imports += [
        "import A6E0LCD0" + code_name(code) + "Cover"
        for code in BROAD_CODES
    ]

    source = "\n".join(imports) + """
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent6E0ZeroLC
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay
open BB6.Agent31ThreeHole BB6.Agent10FastAudit BB6.Agent50TNFPilot
open BB6Coverage.Agent50SideCycle

def parent : PartialMachine := fromCodes [7,24,11,24,14,24,24,16,8,11,24,24]
def child (mv : Move) : PartialMachine := refine parent (3,false) (some mv)

theorem cycleCover (B : Nat) (mv : Move) (e k : Nat) (r : Bool) (x : Int)
    (hk : 0 < k) (h : fastSideCycleCheck (child mv) e k r x = true) :
    Cover (WeightedBound B) (child mv) :=
  Cover.leaf _ (fun m hm =>
    weighted_never B m (fastSideCycleCheck_sound (child mv) e k r x hk h m hm))

theorem ordinary (B : Nat) (hB : 80377 ≤ B) (mv : Move) :
    Cover (WeightedBound B) (child mv) := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
"""
    for code in range(24):
        source += branch_proof(code, cycle_data)

    source += f"""
theorem cover (B : Nat) (hB : 80377 ≤ B) : Cover (WeightedBound B) parent := by
  apply Cover.branch parent (3,false) (by decide)
  intro t
  cases t with
  | some mv => exact ordinary B hB mv
  | none =>
    let c : Config := (knownRun parent {query_step}).getD blank
    have hr : knownRun parent {query_step} = some c := by rfl
    have hs : readSlot c = (3,false) := by decide
    have hw : ∀ d ∈ possibleDelays (refine parent (readSlot c) none) 0,
        d + {query_step} + 1 ≤ B := by
      intro d hd
      have h6 : d < 6 := by
        unfold possibleDelays at hd
        exact Nat.lt_of_lt_of_le (List.mem_filter.mp hd).1 (by decide)
      omega
    have hc := first_hole_weighted_halt B parent {query_step} c (by decide) hr hs hw
    simpa only [hs] using hc

theorem all_completions_weighted :
    ∀ m, compatible parent m → WeightedBound {GLOBAL_BOUND} m := by
  intro m hm
  exact (cover {GLOBAL_BOUND} (by decide)).sound m hm

#print axioms all_completions_weighted
end BB6.Agent6E0ZeroLC
"""
    (out / "Raw139E0ZeroLC.lean").write_text(source)
    (out / "e0_parent_summary.json").write_text(json.dumps({
        "parent": BASE_PARENT,
        "first_hole": first,
        "broad_codes": BROAD_CODES,
        "special_d0_zeroRC_code": SPECIAL_CODE,
        "direct_cycle_codes": direct_codes,
        "direct_cycles": {str(k): list(v) for k, v in cycle_data.items()},
        "weighted_bound": GLOBAL_BOUND,
    }, indent=2))
    print(
        "E0=0LC parent generated:",
        "first-hole-step=", query_step,
        "broad=", len(BROAD_CODES),
        "D0=0RC=1",
        "direct-cycles=", len(direct_codes),
        "bound=", GLOBAL_BOUND,
        flush=True,
    )


if __name__ == "__main__":
    main()
