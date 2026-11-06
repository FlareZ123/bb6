"""Generate q=37 row-grouped shadow certificates and Lean proof modules."""
from pathlib import Path
import os

from exact_fixed_shadow import fixed_shadow

Q = 37
B = 250
K = 10
EXPECTED = ((3927, 250, 9), (3823, 250, 9))


def atomic_write(path: Path, content: str) -> None:
    lock = path.with_suffix(path.suffix + ".lock")
    fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    try:
        temporary = path.with_suffix(path.suffix + ".tmp")
        with temporary.open("w", encoding="utf-8", newline="\n") as stream:
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        os.close(fd)
        lock.unlink()


def render_rows(name: str, rows: list[list[int]]) -> str:
    rendered = ["  [" + ", ".join(map(str, row)) + "]" for row in rows]
    return (
        f"def {name} : Array (List Nat) := #[\n"
        + ",\n".join(rendered)
        + "\n]\n"
    )


def render_proof(feeder: int, L: int, root: int) -> str:
    suffix = str(feeder)
    rows_name = "rows" + suffix
    small = f"small{suffix}"
    root_name = f"root{suffix}"
    closed = f"closed{suffix}"
    no_cutoff = f"noCutoff{suffix}"
    check_all = f"checkRowAll{suffix}"
    parts = [
        f"import Q37Rows{suffix}",
        "import QBudgetRows",
        "set_option maxRecDepth 8192",
        "set_option maxHeartbeats 0",
        f"namespace BB6.Agent9Q37Rows{suffix}",
        "open BB6.Agent9BudgetRows",
        "",
    ]
    for m in range(B + 1):
        parts.append(
            f"theorem checkRow_{m} : checkRow {B} {K} {L} {m} {rows_name} = true := by decide"
        )
    parts.extend([
        "",
        f"theorem {check_all} (m : Nat) (hm : m≤{B}) : checkRow {B} {K} {L} m {rows_name} = true := by",
        "  match m with",
    ])
    for m in range(B + 1):
        parts.append(f"  | {m} => exact checkRow_{m}")
    parts.append(f"  | n+{B + 1} => omega")
    parts.extend([
        "",
        f"def S{suffix} (m z : Nat) : Prop := m≤{B} ∧ z∈{rows_name}[m]!",
        f"theorem {root_name} : S{suffix} 0 {root} := by",
        "  constructor",
        "  · omega",
        "  · decide",
        f"theorem {small} (m z : Nat) (hm : S{suffix} m z) : m≤{B} := hm.1",
        f"theorem {no_cutoff} (m z : Nat) (hm : S{suffix} m z) : ¬2^{K}∣z := by",
        f"  have hcheck := {check_all} m hm.1",
        f"  have hbound := bounds_of_checkRow {B} {K} {L} m {rows_name} hcheck z hm.2",
        "  intro hdiv",
        f"  have hle : 2^{K}≤z := Nat.le_of_dvd hbound.1 hdiv",
        "  omega",
        f"theorem {closed} (m z t v zp : Nat) (hm : S{suffix} m z)",
        f"    (hd:z=2^t*v) (hn:2*zp+1={L}+m+t+v) : S{suffix} (m+t+1) zp := by",
        f"  rcases closed_of_checkRow {B} {K} {L} m {rows_name} ({check_all} m hm.1)",
        "      z t v zp hm.2 hd hn with ⟨hm',hmem⟩",
        "  exact ⟨hm',hmem⟩",
        f"#print axioms {root_name}",
        f"#print axioms {closed}",
        f"end BB6.Agent9Q37Rows{suffix}",
        "",
    ])
    return "\n".join(parts)


def main() -> None:
    directory = Path(__file__).parent
    results = [fixed_shadow(Q, feeder) for feeder in (0, 1)]
    observed = tuple(
        (result["count"], result["max_cost"], result["max_v2_z"])
        for result in results
        if result["status"] == "closed"
    )
    if len(observed) != 2 or observed != EXPECTED:
        raise RuntimeError(f"q={Q} census changed or incomplete: {results!r}")
    if B + K + 3 > 15 * Q:
        raise RuntimeError("the source theorem's budget inequality fails")

    row_sets: list[list[list[int]]] = []
    for result in results:
        rows = [[] for _ in range(B + 1)]
        for m, z in result["nodes"]:
            if m > B or z <= 0 or z >= 2**K:
                raise RuntimeError(f"state outside certified box: {(m, z)}")
            rows[m].append(z)
        row_sets.append(rows)

    L0, L1 = 16 * Q + 8, 16 * Q + 9
    roots = (12 * Q + 4, 10 * Q + 4)
    for feeder, rows in enumerate(row_sets):
        atomic_write(
            directory / f"Q37Rows{feeder}.lean",
            "\n".join([
                "import Lean",
                "set_option maxRecDepth 8192",
                "set_option maxHeartbeats 0",
                f"namespace BB6.Agent9Q37Rows{feeder}",
                render_rows(f"rows{feeder}", rows),
                f"end BB6.Agent9Q37Rows{feeder}",
                "",
            ]),
        )
        atomic_write(
            directory / f"Q37Proof{feeder}.lean",
            render_proof(feeder, L0 + feeder, roots[feeder]),
        )

    budget_source = "\n".join([
        "import Q37Proof0",
        "import Q37Proof1",
        "import UniformUniversalParamK",
        "set_option maxRecDepth 8192",
        "set_option maxHeartbeats 0",
        "namespace BB6.Agent9Q37",
        "theorem blank_no_critical_594_plus_2pow264 (r : Nat) :",
        "    ¬ BB6.Agent1.Reach 2",
        "      (14*2^(16*(37+2^(10+250)*r)+2) -",
        "       2*(16*(37+2^(10+250)*r)+2)-10) := by",
        "  exact BB6.Agent9UniformParamK.universal_blank_critical_cylinder_param_K_of_predicates",
        "    10 250 37 (by decide) (by decide)",
        "    BB6.Agent9Q37Rows0.S0 BB6.Agent9Q37Rows1.S1",
        "    BB6.Agent9Q37Rows0.root0 BB6.Agent9Q37Rows1.root1",
        "    BB6.Agent9Q37Rows0.closed0 BB6.Agent9Q37Rows1.closed1",
        "    BB6.Agent9Q37Rows0.small0 BB6.Agent9Q37Rows1.small1",
        "    BB6.Agent9Q37Rows0.noCutoff0 BB6.Agent9Q37Rows1.noCutoff1 r",
        "#print axioms blank_no_critical_594_plus_2pow264",
        "end BB6.Agent9Q37",
        "",
    ])
    atomic_write(directory / "Q37Budget.lean", budget_source)


if __name__ == "__main__":
    main()
