#!/usr/bin/env python3
"""Turn accepted original-Coq MITM artifacts into exact source queue consumers."""
from pathlib import Path
import argparse
import json
import re
import shutil
from block_phase_dfa import CASES

PIN = "33209bc7dc282b38c8cd6be507bfc551fea56108"
TABLES = {k: v[0] for k, v in CASES.items()}
TABLES["3500"] = "1RB0RC_1LC1RD_---1RB_0LD0RE_1LE0LF_1RA1LF"
TABLE_RE = re.compile(r"^(?:(?:[01][LR][A-F]|---){2}_){5}(?:[01][LR][A-F]|---){2}$")


def accepted_phase(root, out):
    accepted = {}
    for verdict in sorted(root.rglob("verdicts.txt")):
        for line in verdict.read_text().splitlines():
            label, status = line.split()
            if status != "ACCEPTED":
                continue
            base = verdict.parent / label
            cert = json.loads((base / f"phase-{label}.json").read_text())
            if cert["table"] != TABLES[label]:
                raise ValueError(f"unexpected phase table: {label}")
            name = f"Agent5PhaseMITM_{label}"
            source = base / "Agent5PhaseMITM.v"
            obj = base / (name + ".vo")
            if not source.is_file() or not obj.is_file():
                raise ValueError(f"accepted source/object missing: {label}")
            shutil.copyfile(source, out / (name + ".v"))
            shutil.copyfile(obj, out / (name + ".vo"))
            accepted[label] = cert
    if not accepted:
        raise ValueError("no accepted MITM artifacts")
    return dict(sorted(accepted.items(), key=lambda p: (int(p[0].rstrip("ab")), p[0])))


def exact_checkpoints(root, offsets, out):
    selected = {}
    for manifest in root.rglob("manifest.tsv"):
        base = manifest.parent
        if (base / "original-revision.txt").read_text().strip() != PIN:
            raise ValueError("wrong original source revision")
        rows = manifest.read_text().splitlines()
        if rows[0] != "offset\tsize\tfuel\tstatus":
            raise ValueError("invalid checkpoint manifest")
        for row in rows[1:]:
            offset, size, fuel, status = row.split("\t")
            if status != "verified" or int(offset) not in offsets:
                continue
            offset, size, fuel = map(int, (offset, size, fuel))
            name = f"Agent8Batch_{offset}_{size}_{fuel}"
            if not (base / (name + ".vo")).exists():
                raise ValueError("verified checkpoint missing object")
            log = (base / (name + ".log")).read_text()
            counts = re.findall(r"=\s*\((\d+),\s*(\d+)\)", log)
            parts = re.split(r"\]\s*,\s*\[", log.rsplit("chunk_data =", 1)[1].split("\n     :", 1)[0])
            if len(parts) != 2 or not counts:
                raise ValueError("invalid packed checkpoint log: " + name)
            nodes = [[(s, int(h), int(f)) for s,h,f in
                      re.findall(r'\("([01LRABCDEF_-]+)",\s*(\d+),\s*(\d+)\)', part)]
                     for part in parts]
            if list(map(len, nodes)) != list(map(int, counts[-1])):
                raise ValueError("checkpoint count mismatch: " + name)
            for s, h, f in nodes[0] + nodes[1]:
                if not TABLE_RE.fullmatch(s) or s.count("---") != h:
                    raise ValueError("malformed packed node")
            old = selected.get(offset)
            if old and fuel == old["fuel"] and nodes != old["nodes"]:
                raise ValueError("conflicting exact checkpoint")
            if old is None or fuel > old["fuel"]:
                selected[offset] = dict(offset=offset, size=size, fuel=fuel,
                                        name=name, nodes=nodes, base=base)
    for row in selected.values():
        for suffix in (".v", ".vo"):
            shutil.copyfile(row["base"] / (row["name"] + suffix), out / (row["name"] + suffix))
    return dict(sorted(selected.items()))


def refines(child, parent):
    c, p = child.replace("_", ""), parent.replace("_", "")
    return all(p[i:i+3] == "---" or p[i:i+3] == c[i:i+3] for i in range(0, 36, 3))


def emit_roster(accepted, out):
    names = " ".join(f"Agent5PhaseMITM_{label}" for label in accepted)
    tables = ";\n  ".join(f'TM_from_str "{row["table"]}"' for row in accepted.values())
    body = [
        "From BusyCoq Require Import Individual62 Enumerate62 SourceResidualRoster Agent5RosterComplement.",
        f"From BusyCoq Require {names}.",
        "From Coq Require Import List Strings.String.",
        "Import ListNotations.",
        "Open Scope string_scope.",
        f"Definition phase_roster : list TM := [\n  {tables}\n].",
        "Theorem phase_roster_safe bound : Forall (source_table_safe bound) phase_roster.",
        "Proof. unfold phase_roster."
    ]
    for label in accepted:
        body += [f"  constructor. apply source_nonhalt_cylinder, Agent5PhaseMITM_{label}.phase_nonhalt_{label}."]
    body += ["  constructor.", "Qed.", "Print Assumptions phase_roster_safe."]
    (out / "Agent5PhaseRoster.v").write_text("\n".join(body) + "\n")


def emit_checkpoint(row, accepted, out):
    offset, size, fuel, name = (row[k] for k in ("offset", "size", "fuel", "name"))
    roster = [v["table"] for v in accepted.values()]
    active, held = row["nodes"]
    removed = [sum(any(refines(s, p) for p in roster) for s,_,_ in nodes)
               for nodes in (active, held)]
    ac, hc = removed
    body = [
        "From BusyCoq Require Import Individual62 Enumerate62 Agent8AdaptiveSource",
        "  Agent8QueueCheckpoint Agent8WeightedSource SourceResidualRoster Agent5RosterComplement Agent5PhaseRoster.",
        f"From BusyCoq Require {name}.",
        "From Coq Require Import List NArith Bool.",
        "Import ListNotations TNF_Node.",
        "Open Scope nat_scope.",
        f"Definition phase_queue_{offset} := decode_queue {name}.chunk_data.",
        f"Definition phase_remaining_{offset} := roster_remaining phase_roster",
        f"  (fst phase_queue_{offset} ++ snd phase_queue_{offset}).",
        f"Theorem phase_consume_{offset} bound :",
        f"  Forall (source_weighted_safe bound) (adaptive_obligations decider",
        f"    (AP_advance {fuel}%N AP_stop) (q_i {offset} {size})) <->",
        f"  Forall (source_weighted_safe bound) phase_remaining_{offset}.",
        "Proof.",
        f"  apply roster_checkpoint_consumption; [apply phase_roster_safe|exact {name}.chunk_data_exact].",
        "Qed.",
        f"Definition phase_counts_{offset} : nat * nat * nat * nat :=",
        f"  (length (fst phase_queue_{offset}), length (snd phase_queue_{offset}),",
        f"   length (filter (source_roster_covers phase_roster) (fst phase_queue_{offset})),",
        f"   length (filter (source_roster_covers phase_roster) (snd phase_queue_{offset}))).",
        f"Theorem phase_counts_{offset}_exact : phase_counts_{offset} = ({len(active)}, {len(held)}, {ac}, {hc}).",
        "Proof. vm_compute. reflexivity. Qed.",
        f"Print Assumptions phase_consume_{offset}.",
        f"Print Assumptions phase_counts_{offset}_exact."
    ]
    (out / f"Agent5PhaseConsume_{offset}.v").write_text("\n".join(body) + "\n")
    return (offset, size, fuel, len(active), len(held), ac, hc, name)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--phase-dir", type=Path, required=True)
    p.add_argument("--checkpoint-dir", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    a = p.parse_args()
    a.out.mkdir(parents=True, exist_ok=True)
    accepted = accepted_phase(a.phase_dir, a.out)
    offsets = {int(k.rstrip("ab")) for k in accepted}
    checkpoints = exact_checkpoints(a.checkpoint_dir, offsets, a.out)
    emit_roster(accepted, a.out)
    rows = [emit_checkpoint(v, accepted, a.out) for v in checkpoints.values()]
    (a.out / "phase-accepted-labels.txt").write_text("\n".join(accepted) + "\n")
    header = "offset\tsize\tfuel\tactive\theld\tactive_consumed\theld_consumed\tmodule\n"
    (a.out / "phase-consumption.tsv").write_text(header + "".join("\t".join(map(str, r))+"\n" for r in rows))
    print("Accepted original-source MITM labels:", ",".join(accepted))
    print("Exact checkpoint offsets available:", ",".join(map(str, checkpoints)))
    print("Candidate consumed counts (must compile Coq consumers):",
          sum(r[5] for r in rows), sum(r[6] for r in rows))


if __name__ == "__main__":
    main()
