#!/usr/bin/env python3
"""Emit a Lean *checked* finite-control certificate from the untrusted q0-151
macro discovery closure. The generated Lean file recomputes every abstract
transition and every member/push/pop closure, rather than trusting edges from
this Python program. Original TM macro refinement is a separate obligation.
"""
import argparse
import pathlib
from q151_macro_certificate import certificate, transitions, typ, TYPES, EMPTY, app

def first(p):
    if len(p) > 1:
        raise AssertionError(("non-singleton prefix", p))
    return p[0] if p else 0

def right(r):
    p, t = r
    return f"⟨{first(p)}, {t}⟩"

def segment(s):
    p, f, c = s
    return f"⟨{first(p)}, {f[0]}, {f[1]}, {c}⟩"

def ctrl(st):
    q, r, s = st
    return f"⟨{'true' if q == 'B' else 'false'}, {right(r)}, {segment(s)}⟩"

def certify_python_consistency(controls, symbols):
    ss = set(controls)
    sy = set(symbols)
    assert EMPTY in sy
    assert ('B', ((),4), ((),(0,1),1)) in ss
    for st in controls:
        assert typ(st[1]) in TYPES
        for op, nxt, sym in transitions(st):
            if op == 'bad':
                raise AssertionError(('bad', st))
            if op == 'stay':
                assert nxt in ss, ('stay', st, nxt)
            elif op == 'push':
                assert nxt in ss and sym in sy, ('push', st, nxt, sym)
            elif op == 'pop':
                for saved in symbols:
                    restored = ('B', nxt, app(saved, '1111'))
                    assert restored in ss, ('pop', st, nxt, saved, restored)
            else:
                raise AssertionError(op)

def generate(path):
    controls, symbols, requests = certificate()
    controls = sorted(controls)
    symbols = sorted(symbols)
    certify_python_consistency(controls, symbols)

    lines = [
        "import Q0151FiniteModel",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 100000",
        "namespace BB6.Agent5Q0151FiniteCertificate",
        "open BB6.Agent5Q0151FiniteModel",
        "open BB6.Agent5Q0151StackSaturation",
        "",
        "-- Data are proposed by Python; Lean recomputes transitions independently.",
        "def knownControls : List Control := [",
    ]
    lines.extend("  " + ctrl(x) + ("," if i + 1 < len(controls) else "")
                 for i,x in enumerate(controls))
    lines += ["]", "def knownSegments : List SegmentSummary := ["]
    lines.extend("  " + segment(x) + ("," if i + 1 < len(symbols) else "")
                 for i,x in enumerate(symbols))
    lines += [
        "]",
        "",
        "def goodAction : Action Control SegmentSummary RightSummary → Prop",
        "  | .stay d => d ∈ knownControls",
        "  | .push d s => d ∈ knownControls ∧ s ∈ knownSegments",
        "  | .pop r => ∀ s ∈ knownSegments, resume r s ∈ knownControls",
        "  | .bad => False",
        "",
        "theorem seed_mem : seed ∈ knownControls := by decide +kernel",
        "theorem blank_mem : emptySegment ∈ knownSegments := by decide +kernel",
        "theorem finite_closed :",
        "    ∀ c ∈ knownControls, ∀ a ∈ delta c, goodAction a := by",
        "  decide +kernel",
        "",
        "theorem semantic_closed :",
        "    ∀ c, c ∈ knownControls → ∀ a, a ∈ delta c →",
        "      SafeAction (fun d => d ∈ knownControls)",
        "        (fun s => s ∈ knownSegments) resume a := by",
        "  intro c hc a ha",
        "  have hf := finite_closed c hc a ha",
        "  cases a with",
        "  | stay d => exact hf",
        "  | push d s => exact hf",
        "  | pop r => exact hf",
        "  | bad => exact hf",
        "",
        "theorem abstract_never_bad {c : Control} {stack : List SegmentSummary}",
        "    (h : Reach delta resume emptySegment seed c stack) :",
        "    Action.bad ∉ delta c := by",
        "  exact reachable_no_bad semantic_closed blank_mem seed_mem h",
        "",
        "#print axioms seed_mem",
        "#print axioms blank_mem",
        "#print axioms finite_closed",
        "#print axioms semantic_closed",
        "#print axioms abstract_never_bad",
        "end BB6.Agent5Q0151FiniteCertificate",
        "",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")
    print(f"LEAN_CERT controls={len(controls)} symbols={len(symbols)} pop_results={len(requests)} "
          f"file={path} lines={len(lines)}")

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('output', type=pathlib.Path)
    args = parser.parse_args()
    generate(args.output)
