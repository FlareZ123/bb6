"""Generate weight-only subproofs from the audited LF1 Kid source files.

Pass the merged shard directory (containing all 24 original Kid .lean files)
and an output directory. The existing proof partition is preserved; all leaf
weights and split query weights are independently checked in Lean.
"""
import argparse
import pathlib
import re

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("shards", type=pathlib.Path)
    ap.add_argument("out", type=pathlib.Path)
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    for i in range(24):
        p = args.shards / f"Raw58LF1Kid{i:02}.lean"
        t = p.read_text()
        blocks = re.findall(r"(?ms)^theorem (\w+) : (.*?) := by(.*?)(?=^def |^theorem |^end )", t)
        assert blocks and blocks[-1][0] == f"check{i:02}", p
        out = [f"import {p.stem}\nimport ZipWeightTighten\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent4Raw58LF1\nopen BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath\nopen BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent4ZipWeightTighten\n"]
        for name, stmt, proof in blocks:
            assert stmt.startswith("zipCheck 3055750 "), (p, name)
            stmt = stmt.replace("zipCheck 3055750", "weights 3055746")
            if "  change " in proof:
                proof = proof.replace("zipCheck 3055750", "weights 3055746").replace("zipQueryOK 3055750", "queryWeight 3055746")
                proof = re.sub(r"(?<=exact )(kid\d+_part\d+_checked)\b", r"\1_weight", proof)
            else:
                proof = " rfl\n\n"
            out.append(f"theorem {name}_weight : {stmt} := by{proof}")
        out.append("end BB6.Agent4Raw58LF1\n")
        (args.out / f"{p.stem}Weight.lean").write_text("".join(out))

if __name__ == "__main__":
    main()
