#!/usr/bin/env python3
"""Generate an original-semantics Lean *conditional* Cover for Raw139 D0=1LF.

The ~730k-node finite TNF tree is reduced to only nine explicit split nodes,
206 ordinary subtree Audit/check hypotheses, and the F067 3506 Cover. The
228-digit leaf2265 Cover is imported as a fully source-proved premise.
The generator is untrusted: Lean rechecks every special split query, table
identity and the conditional Cover theorem from original source.
"""
import json
from pathlib import Path
import sys

from_codes = lambda codes: "fromCodes [" + ",".join(map(str, codes)) + "]"
L = "finiteBound"
B = "largeBound"
NS = "BB6.Agent3D0LF1Spine"
ORDER = [4*q+2*w+r for w in range(2) for r in range(2) for q in range(6)]

def bit(v):
    return str(bool(v)).lower()

def slot(s):
    return f"({s//2},{bit(s%2)})"

def move(code):
    return f"⟨{bit(code&2)},{bit(code&1)},{code//4}⟩"

def hname(i):
    return f"hSpine{i}"

def tname(i):
    return f"tSpine{i}"

def pname(i):
    return f"pSpine{i}"

def build(plan):
    regions = plan["ordinary_regions"]
    spines = plan["spine"]
    assert len(regions)==206 and len(spines)==9
    assert set(plan["exception_paths"])=={"2265","3506"}
    exceptions = {tuple(v):int(k) for k,v in plan["exception_paths"].items()}
    r_index = {tuple(v["path"]):i for i,v in enumerate(regions)}
    s_index = {tuple(v["path"]):i for i,v in enumerate(spines)}
    assert tuple() in s_index

    lines=[
        "import TwoBoundAudit",
        "import Leaf2265TwoBoundTarget",
        "set_option maxRecDepth 1000000",
        "set_option maxHeartbeats 0",
        "",
        f"namespace {NS}",
        "open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay",
        "open BB6.Agent8TNFPath BB6.Agent50TNFPilot BB6.Agent31ThreeHole",
        "open BB6.Agent3PackedAudit BB6.Agent48PackedPrefix",
        "open BB6Coverage.Agent10ZipAudit",
        "open BB6.Agent3TwoBoundAudit",
        "open BB6.Agent3Raw139D0OneLFTarget",
        "",
        "/-! These 206 table branches and 9 spines are computed from the",
        "exact checksum-checked cutoff-100 source tree. No finite child Audit",
        "or F067 nonhalting/halting theorem is assumed to be proved here. -/",
        f"def pF067 : PartialMachine := {from_codes(plan['exception_tables']['3506'])}",
        f"def pRoot : PartialMachine := {from_codes(plan['parent'])}",
        "def regionCodes : Array (List Nat) := #[",
    ]
    for r in regions:
        lines.append("  [" + ",".join(map(str,r["table"])) + "],")
    lines += [
        "]",
        f"def regionTable (i : Fin {len(regions)}) : PartialMachine :=",
        "  fromCodes (regionCodes[i.val]!)",
        "",
        "theorem safe2265 : ∀ m, compatible BB6.Agent3Leaf2265Bridge.ctr m →",
        "    WeightedBound largeBound m :=",
        "  BB6.Agent3Raw139D0OneLFTarget.leaf2265_cover_at_large.sound",
        "",
    ]
    for i,sp in enumerate(spines):
        lines.append(f"def {pname(i)} : PartialMachine := {from_codes(sp['table'])}")
    lines += ["",
        f"abbrev Audits := Fin {len(regions)} → Audit",
        "abbrev Safe3506 := ∀ m, compatible pF067 m → WeightedBound largeBound m",
        "abbrev CheckedAudits (audits : Audits) : Prop :=",
        f"  ∀ i : Fin {len(regions)}, packedPrefixCheck finiteBound (regionTable i) (audits i) = true",
        ""]
    # Define child subtrees from the deepest spine up, never a circular import.
    for i in sorted(range(len(spines)),key=lambda j:len(spines[j]["path"]),reverse=True):
        sp=spines[i]
        path=tuple(sp["path"])
        step,read=sp["query_step"],sp["query_slot"]
        childs=[]
        refs=[]
        for j,code in enumerate(ORDER):
            p=path+(j,)
            if p in s_index:
                k=s_index[p]
                body=f"{tname(k)} audits safe3506"
                where=pname(k)
                goal="spine"
                needed=k
            elif p in r_index:
                k=r_index[p]
                body=f".ordinary (audits {k})"
                where=f"regionTable {k}"
                goal="ordinary"
                needed=k
            elif p in exceptions:
                k=exceptions[p]
                body=f".bounded BB6.Agent3Leaf2265Bridge.ctr safe2265" if k==2265 else ".bounded pF067 safe3506"
                where="BB6.Agent3Leaf2265Bridge.ctr" if k==2265 else "pF067"
                goal="bounded"
                needed=k
            else:
                raise AssertionError(f"child {p} unrepresented")
            childs.append(body)
            refs.append((code,where,goal,needed,body))
        assert len(refs)==24
        lines += [
            f"def {tname(i)} (audits : Audits) (safe3506 : Safe3506) :",
            "    TwoBoundAudit finiteBound largeBound :=",
            f"  .split {step} {slot(read)} (byTwoBoundMove [",
            "    "+",\n    ".join(childs)+"])",
            "",
            f"theorem {hname(i)} (audits : Audits) (hOrd : CheckedAudits audits)",
            "    (safe3506 : Safe3506) :",
            f"    check finiteBound largeBound {pname(i)} ({tname(i)} audits safe3506) = true := by",
            f"  simp only [{tname(i)}, check, Bool.and_eq_true]",
            "  refine ⟨by decide +kernel, allMoves_of _ ?_⟩",
            "  intro mv",
            "  rcases mv with ⟨w,r,q⟩",
            "  cases w <;> cases r",
            "  all_goals",
            "    have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by",
            "      have hlt := q.isLt",
            "      simp only [Fin.ext_iff]",
            "      omega",
            "    rcases hcases with h | h | h | h | h | h",
            "    all_goals subst q",
        ]
        for code,where,goal,needed,body in refs:
            if goal=="spine":
                target=f"check finiteBound largeBound (refine {pname(i)} {slot(read)} (some {move(code)})) ({body}) = true"
            elif goal=="ordinary":
                target=f"packedPrefixCheck finiteBound (refine {pname(i)} {slot(read)} (some {move(code)})) (audits {needed}) = true"
            else:
                target=f"tableOK (refine {pname(i)} {slot(read)} (some {move(code)})) {where} = true"
            lines += [
                "  · change "+target,
                f"    have hp : refine {pname(i)} {slot(read)} (some {move(code)}) = {where} :=",
                "      tableOK_sound _ _ (by decide +kernel)",
                "    rw [hp]",
            ]
            if goal=="spine":
                lines.append(f"    exact {hname(needed)} audits hOrd safe3506")
            elif goal=="ordinary":
                lines.append(f"    exact hOrd {needed}")
            else:
                lines.append("    decide +kernel")
        lines.append("")
    root=s_index[tuple()]
    lines += [
        f"theorem initial_rule : {pname(root)} initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel",
        f"theorem no_assigned_halt : weightedTNFNoAssignedHalt {pname(root)} := by",
        "  intro s",
        f"  unfold {pname(root)} fromCodes",
        f"  cases h : ({plan['parent']} : List Nat)[2 * s.1.val + s.2.toNat]? with",
        "  | none => simp [h]",
        "  | some n => by_cases hn : n < 24 <;> simp [h, hn]",
        "",
        "/-- Every physical completion of this Raw139 parent is champion-bounded,",
        "    conditional on 206 original finite Audit checks and the separate",
        "    F067 source bound; the 228-digit child was proved unconditionally. -/",
        "theorem parent_cover_conditional (audits : Audits)",
        "    (hOrd : CheckedAudits audits) (safe3506 : Safe3506) :",
        f"    Cover (WeightedBound largeBound) {pname(root)} :=",
        f"  BB6.Agent3TwoBoundAudit.sound finiteBound largeBound finite_le_large {pname(root)}",
        f"    ({tname(root)} audits safe3506) initial_rule no_assigned_halt",
        f"    ({hname(root)} audits hOrd safe3506)",
        "",
        "#print axioms parent_cover_conditional",
        f"end {NS}",
        ""
    ]
    return "\n".join(lines)


if __name__=="__main__":
    if len(sys.argv)!=3:
        raise SystemExit("usage: emit-two-bound-spine.py plan.json output.lean")
    plan=json.loads(Path(sys.argv[1]).read_text())
    out=Path(sys.argv[2])
    source=build(plan)
    out.write_text(source)
    print("Wrote",out,len(source),"bytes",
          len(plan["spine"]),"checked split nodes",
          len(plan["ordinary_regions"]),"ordinary checker hypotheses")
