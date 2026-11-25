#!/usr/bin/env python3
"""Generate packed first-hole WeightedTNFCertificate modules for all long Raw118 leaves."""
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
BOUND = 756496


def parse_table(table: str):
    return [row for pair in table.split("_") for row in (pair[:3], pair[3:])]


def runlen(x: int, bit: int) -> int:
    y = x if bit == 0 else ~x
    return (y & -y).bit_length() - 1 if y else 0


def simulate(rows):
    q = left = right = n = 0
    trace = []
    checkpoints = [(0, 0, 0)]
    while (action := rows[q * 2 + left % 2]) != "---":
        write, direction, target = int(action[0]), action[1], ord(action[2]) - 65
        bit = left % 2
        if target == q:
            stack = left if direction == "L" else right
            k = runlen(stack, bit)
            if direction == "R":
                k += 1
            if k > 1:
                if direction == "L":
                    left, right = left >> k, (right << k) + write * ((1 << k) - 1)
                    instruction = (".left", k)
                else:
                    tail = right >> (k - 1)
                    left, right = tail % 2 + 2 * ((left // 2 << k) + write * ((1 << k) - 1)), tail // 2
                    instruction = (".right", k - 1)
                trace.append(instruction)
                n += k
                checkpoints.append((q, left, right))
                continue
        if direction == "L":
            left, right = left // 2, write + 2 * right
        else:
            left, right = right % 2 + 2 * (write + 2 * (left // 2)), right // 2
        q = target
        n += 1
        if trace and trace[-1][0] == ".ordinary":
            trace[-1] = (".ordinary", trace[-1][1] + 1)
            checkpoints[-1] = (q, left, right)
        else:
            trace.append((".ordinary", 1))
            checkpoints.append((q, left, right))
    return n, (q, left % 2), trace, checkpoints


def emit_one(index: int, table_string: str, expected_n: int, expected_slot: int):
    rows = parse_table(table_string)
    assert len(rows) == 12 and table_string.count("---") == 1
    n, slot, trace, checkpoints = simulate(rows)
    assert n == expected_n, (index, n, expected_n)
    assert slot == (expected_slot // 2, bool(expected_slot % 2)), (index, slot, expected_slot)
    q, bit = slot
    bit = bool(bit)  # Lean slot symbol is Bool, not an integer literal.

    lines = [
        "import PackedSweep",
        "import ZipThreeHoleAudit",
        "set_option maxRecDepth 1000000",
        "set_option maxHeartbeats 0",
        "set_option exponentiation.threshold 4096",
        f"namespace BB6.Agent16Raw118Late.M{index}",
        "open BB6Coverage BB6Coverage.Agent16Packed BB6Coverage.Agent10ZipAudit",
        "open BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit",
        "def table : PartialMachine := fun s =>",
        "  match s.1.val,s.2 with",
    ]
    for j, action in enumerate(rows):
        if action != "---":
            write = str(action[0] == "1").lower()
            direction = str(action[1] == "R").lower()
            target = ord(action[2]) - 65
            lines.append(f"  | {j // 2},{str(bool(j % 2)).lower()} => some (some ⟨{write},{direction},{target}⟩)")
    lines.append("  | _,_ => none")

    def state_at(i):
        state, left, right = checkpoints[i]
        return f"⟨{state}, {left}, {right}⟩"

    chunks = []
    for start in range(0, len(trace), 100):
        end = min(start + 100, len(trace))
        chunk = trace[start:end]
        chunk_index = len(chunks)
        cost = sum(k + (op == ".right") for op, k in chunk)
        chunks.append((chunk_index, cost))
        body = ", ".join(f"{op} {k}" for op, k in chunk)
        lines.append(f"def block{chunk_index} : List Instr := [{body}]")
        lines.append(
            f"theorem proof{chunk_index} : prun table {cost} {state_at(start)} = some {state_at(end)} :=\n"
            f"  execList_sound table block{chunk_index} _ _ (by rfl)"
        )
    assert chunks
    lines.append(f"theorem longRun : prun table {n} ⟨0,0,0⟩ = some {state_at(len(trace))} := by")
    lines.append("  have h0 := proof0")
    for chunk_index, _cost in chunks[1:]:
        lines.append(f"  have h{chunk_index} := prun_join h{chunk_index - 1} proof{chunk_index}")
    lines.append(f"  exact h{chunks[-1][0]}")
    lines.extend([
        f"theorem longRead : zipRead table {n} = some ({q},{str(bit).lower()}) := by",
        "  rw [←packedRead_eq, packedRead]",
        f"  change (prun table {n} ⟨0,0,0⟩).map (fun z => (z.q,z.l % 2 == 1)) = _",
        "  rw [longRun]",
        "  rfl",
        f"theorem longCheck : zipCheck {BOUND} table (.last {n} ({q},{str(bit).lower()})) = true := by",
        "  simp only [zipCheck,zipQueryOK,longRead]",
        "  decide",
        "theorem nohalt : weightedTNFNoAssignedHalt table := by",
        "  intro s",
        "  rcases s with ⟨q,b⟩",
        "  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega",
        "  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl",
        "  all_goals cases b <;> decide",
        f"noncomputable def longCertificate : WeightedTNFCertificate {BOUND} table 6 :=",
        f"  certifiedZip {BOUND} table (.last {n} ({q},{str(bit).lower()})) (by decide) nohalt longCheck",
        f"theorem longAttained : ∃ m, compatible table m ∧ HaltsAfter m {n} := by",
        f"  let m := weightedTNFDefaultCompletion (refine table ({q},{str(bit).lower()}) none)",
        f"  have hr : (knownRun table {n}).map readSlot = some ({q},{str(bit).lower()}) := by",
        "    rw [← zipRead_eq]",
        "    exact longRead",
        f"  have hh : table ({q},{str(bit).lower()}) = none := by decide",
        f"  have hm : compatible (refine table ({q},{str(bit).lower()}) none) m :=",
        "    weightedTNFDefaultCompletion_compatible _",
        f"  refine ⟨m, refine_preserves_compat table m ({q},{str(bit).lower()}) none hh hm, ?_⟩",
        f"  cases hrun : knownRun table {n} with",
        "  | none => simp [hrun] at hr",
        "  | some c =>",
        f"    have hs : readSlot c = ({q},{str(bit).lower()}) := by simpa [hrun] using hr",
        f"    apply first_hole_halts table {n} c hrun",
        "    · simpa [hs] using hh",
        "    · simpa [hs] using hm",
        "#print axioms longAttained",
        "#print axioms longRead",
        "#print axioms longCertificate",
        f"end BB6.Agent16Raw118Late.M{index}",
    ])
    return "\n".join(lines) + "\n", {
        "index": index,
        "table": table_string,
        "steps_to_hole": n,
        "slot": expected_slot,
        "trace_instructions": len(trace),
        "chunks": len(chunks),
    }


def main(work: Path):
    raw = (work / "open.txt").read_bytes()
    rows = raw.decode().splitlines()
    candidates = json.loads((work / "candidates.json").read_text())
    late_long = [
        (int(i), int(v[0]), int(v[1]))
        for i, v in candidates["late"].items() if int(v[0]) > 10000
    ]
    assert len(late_long) == 6, late_long
    modules = []
    manifest = []
    for index, n, slot in sorted(late_long):
        source, record = emit_one(index, rows[index], n, slot)
        name = f"Raw118Late{index}"
        (HERE / f"{name}.lean").write_text(source)
        modules.append(name)
        manifest.append(record)
        print(f"LATE {index} steps={n} slot={slot} chunks={record['chunks']} "
              f"instructions={record['trace_instructions']}")
    (HERE / "Raw118Late.lean").write_text(
        "\n".join(f"import {name}" for name in modules) + "\n"
    )
    (HERE / "Raw118Late.json").write_text(json.dumps({
        "open_sha256": hashlib.sha256(raw).hexdigest(),
        "bound": BOUND,
        "count": len(manifest),
        "modules": modules,
        "leaves": manifest,
    }, indent=2) + "\n")
    print(f"Raw118 late source certificates: {len(manifest)}")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: generate_late_traces.py WORKDIR")
    main(Path(sys.argv[1]))
