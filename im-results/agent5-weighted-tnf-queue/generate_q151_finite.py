#!/usr/bin/env python3
"""Produce a *kernel-checkable* factorized q0-151 macro-stack invariant.

The Python exploration is only a witness generator: generated Lean independently
recomputes every transition, the finite closure, and the stack-pop restorations.
No native_decide, sorry, axioms, or trusted external Boolean decisions are used.
Original-machine macro refinement remains a separate proof obligation.
"""
import argparse
import pathlib
from collections import defaultdict
from q151_macro_certificate import certificate, transitions, typ, TYPES, EMPTY, app

def emit_right(x):
    p, t = x
    assert len(p) <= 1
    return f"⟨{p[0] if p else 0}, {t}⟩"

def emit_segment(x):
    p, image, last = x
    assert len(p) <= 1 and len(image) == 2
    return f"⟨{p[0] if p else 0}, {image[0]}, {image[1]}, {last}⟩"

def emit_control(x):
    q, r, s = x
    return f"⟨{'true' if q == 'B' else 'false'}, {emit_right(r)}, {emit_segment(s)}⟩"

def define_list(lines, name, typ, entries, encode):
    lines.append(f"def {name} : List {typ} := [")
    lines.extend(f"  {encode(x)}{',' if i+1<len(entries) else ''}"
                 for i,x in enumerate(entries))
    lines += ["]", ""]

def discover():
    controls0, saved0, pop0 = certificate()
    controls = set(controls0)
    saved = sorted(set(saved0))
    pops = sorted(set(pop0))
    bstates = {(r,s) for q,r,s in controls if q == 'B'}
    cstates = {(r,s) for q,r,s in controls if q == 'C'}
    rights = sorted({r for r,s in bstates})
    by_seg = defaultdict(set)
    for r,s in bstates:
        by_seg[s].add(r)
    core = sorted(s for s,rs in by_seg.items() if len(rs) == len(rights))
    extra = sorted(s for s,rs in by_seg.items() if len(rs) == 12)
    singles = sorted(s for s,rs in by_seg.items() if len(rs) == 1)
    assert len(rights) == 17, len(rights)
    assert len(core) == 28, len(core)
    assert len(extra) == 21, len(extra)
    assert len(singles) == 1, len(singles)
    assert len(saved) == 50, len(saved)
    assert len(pops) == 12, len(pops)
    assert (('B', ((),4), ((),(0,1),1)) in controls)
    seed_seg = ((),(0,1),1)
    assert singles == [seed_seg]
    assert by_seg[seed_seg] == {((),4)}
    restricted = sorted(by_seg[extra[0]])
    assert len(restricted) == 12
    assert all(by_seg[s] == set(restricted) for s in extra)
    csegments = sorted({s for r,s in cstates})
    assert len(csegments) == 5 and all(s[2] == 3 for s in csegments)
    assert {r for r,s in cstates} == set(rights)
    assert cstates == {(r,s) for r in rights for s in csegments}
    expected = ({('B',r,s) for r in rights for s in core}
              | {('B',r,s) for r in restricted for s in extra}
              | {('B',((),4),seed_seg)}
              | {('C',r,s) for r in rights for s in csegments})
    assert expected == controls, (len(expected-controls),len(controls-expected))
    assert len(controls) == 17*28 + 12*21 + 1 + 17*5 == 814
    assert EMPTY in saved
    for st in controls:
        assert typ(st[1]) in TYPES
        for op,nxt,sym in transitions(st):
            assert op != "bad", st
            if op == "stay":
                assert nxt in controls, (op,st,nxt)
            elif op == "push":
                assert nxt in controls and sym in saved, (op,st,nxt,sym)
            elif op == "pop":
                assert nxt in pops, (op,st,nxt)
                for sv in saved:
                    assert ('B',nxt,app(sv,'1111')) in controls
            else:
                raise AssertionError(op)
    return rights,restricted,core,extra,csegments,saved,pops

def generate(path):
    rights,restricted,core,extra,csegments,saved,pops = discover()
    lines = [
        "import Q0151FiniteModel",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 100000",
        "namespace BB6.Agent5Q0151FiniteCertificate",
        "open BB6.Agent5Q0151FiniteModel",
        "open BB6.Agent5Q0151StackSaturation",
        "",
        "-- Finite rectangular relation; all Lean transitions are recomputed.",
    ]
    for name,kind,entries,encode in [
        ("allRights","RightSummary",rights,emit_right),
        ("restrictedRights","RightSummary",restricted,emit_right),
        ("bCore","SegmentSummary",core,emit_segment),
        ("bExtra","SegmentSummary",extra,emit_segment),
        ("cSegments","SegmentSummary",csegments,emit_segment),
        ("savedSegments","SegmentSummary",saved,emit_segment),
        ("popResults","RightSummary",pops,emit_right),
    ]:
        define_list(lines,name,kind,entries,encode)
    lines += [
        "def Good (c : Control) : Prop :=",
        "  if c.isB then",
        "    (c.right ∈ allRights ∧ c.segment ∈ bCore) ∨",
        "    (c.right ∈ restrictedRights ∧ c.segment ∈ bExtra) ∨ c = seed",
        "  else c.right ∈ allRights ∧ c.segment ∈ cSegments",
        "",
        "instance instDecidableGood (c : Control) : Decidable (Good c) := by",
        "  unfold Good",
        "  infer_instance",
        "",
        "def actionCheck : Action Control SegmentSummary RightSummary → Bool",
        "  | .stay d => decide (Good d)",
        "  | .push d s => decide (Good d ∧ s ∈ savedSegments)",
        "  | .pop r => decide (r ∈ popResults)",
        "  | .bad => false",
        "",
        "def checkOne (c : Control) : Bool :=",
        "  decide (delta c ≠ []) && (delta c).all actionCheck",
        "",
        "def checkBAll (r : RightSummary) : Bool :=",
        "  bCore.all (fun s => checkOne ⟨true,r,s⟩)",
        "def checkBExtra (r : RightSummary) : Bool :=",
        "  bExtra.all (fun s => checkOne ⟨true,r,s⟩)",
        "def checkC (r : RightSummary) : Bool :=",
        "  cSegments.all (fun s => checkOne ⟨false,r,s⟩)",
        "",
        "-- Source-independent finite proof: saved/restored correlated pop requests.",
        "private theorem popChecked :",
        "  popResults.all (fun r => savedSegments.all",
        "    (fun s => decide (Good (resume r s)))) = true := by",
        "  decide +kernel",
        "",
        "private theorem seedChecked : checkOne seed = true := by",
        "  decide +kernel",
        "",
    ]
    for label,rows,list_name in [
        ("checkBAll",rights,"allRights"),
        ("checkBExtra",restricted,"restrictedRights"),
        ("checkC",rights,"allRights"),
    ]:
        labels = []
        for i,r in enumerate(rows):
            theorem = f"row_{label}_{i}"
            labels.append(theorem)
            lines.extend([
                f"private theorem {theorem} : {label} {emit_right(r)} = true := by",
                "  decide +kernel",
                "",
            ])
        lines.extend([
            f"private theorem all_{label} : {list_name}.all {label} = true := by",
            f"  simp [{list_name}, List.all, {', '.join(labels)}]",
            "",
        ])
    lines += [
        "-- Small source-level reflection lemmas, not trusted native evaluation.",
        "private theorem allMem {α : Type} (f : α → Bool) :",
        "    ∀ xs : List α, xs.all f = true → ∀ x, x ∈ xs → f x = true := by",
        "  intro xs",
        "  induction xs with",
        "  | nil =>",
        "      intro h x hx",
        "      cases hx",
        "  | cons y ys ih =>",
        "      intro h x hx",
        "      change (f y && ys.all f) = true at h",
        "      have hfy : f y = true := by",
        "        cases hy : f y <;> simp [hy] at h ⊢",
        "      have hys : ys.all f = true := by",
        "        cases hy : ys.all f <;> simp [hy] at h ⊢",
        "      simp only [List.mem_cons] at hx",
        "      rcases hx with he | he",
        "      · subst x",
        "        exact hfy",
        "      · exact ih hys x he",
        "",
        "private theorem actionSound (a : Action Control SegmentSummary RightSummary)",
        "    (ha : actionCheck a = true) :",
        "    SafeAction Good (fun s => s ∈ savedSegments) resume a := by",
        "  cases a with",
        "  | stay d =>",
        "      change Good d",
        "      simpa [actionCheck] using ha",
        "  | push d s =>",
        "      change Good d ∧ s ∈ savedSegments",
        "      simpa [actionCheck] using ha",
        "  | pop r =>",
        "      have hr : r ∈ popResults := by simpa [actionCheck] using ha",
        "      intro s hs",
        "      have hrow := allMem (fun r => savedSegments.all",
        "          (fun s => decide (Good (resume r s)))) popResults",
        "          popChecked r hr",
        "      have hentry := allMem (fun s => decide (Good (resume r s)))",
        "          savedSegments hrow s hs",
        "      simpa using hentry",
        "  | bad => simp [actionCheck] at ha",
        "",
        "theorem allChecked (c : Control) (hc : Good c) : checkOne c = true := by",
        "  rcases c with ⟨q,r,s⟩",
        "  cases q with",
        "  | false =>",
        "      change r ∈ allRights ∧ s ∈ cSegments at hc",
        "      have hr := allMem checkC allRights all_checkC r hc.1",
        "      exact allMem (fun s => checkOne ⟨false,r,s⟩) cSegments hr s hc.2",
        "  | true =>",
        "      change (r ∈ allRights ∧ s ∈ bCore) ∨",
        "        (r ∈ restrictedRights ∧ s ∈ bExtra) ∨",
        "        (Control.mk true r s = seed) at hc",
        "      rcases hc with h | h | h",
        "      · have hr := allMem checkBAll allRights all_checkBAll r h.1",
        "        exact allMem (fun s => checkOne ⟨true,r,s⟩) bCore hr s h.2",
        "      · have hr := allMem checkBExtra restrictedRights",
        "            all_checkBExtra r h.1",
        "        exact allMem (fun s => checkOne ⟨true,r,s⟩) bExtra hr s h.2",
        "      · simpa [h] using seedChecked",
        "",
        "theorem finite_closed (c : Control) (hc : Good c)",
        "    (a : Action Control SegmentSummary RightSummary) (ha : a ∈ delta c) :",
        "    SafeAction Good (fun s => s ∈ savedSegments) resume a := by",
        "  have hh := allChecked c hc",
        "  unfold checkOne at hh",
        "  have hall : (delta c).all actionCheck = true := by",
        "    cases h : (delta c).all actionCheck <;> simp [h] at hh ⊢",
        "  exact actionSound a (allMem actionCheck (delta c) hall a ha)",
        "",
        "theorem finite_progress (c : Control) (hc : Good c) : delta c ≠ [] := by",
        "  have hh := allChecked c hc",
        "  unfold checkOne at hh",
        "  have hnonempty : decide (delta c ≠ []) = true := by",
        "    cases h : decide (delta c ≠ []) <;> simp [h] at hh ⊢",
        "  simpa using hnonempty",
        "",
        "-- Source refinement: every abstract Good control has a live right mask.",
        "private theorem allRightsLive :",
        "  allRights.all (fun r => decide (rightType r ≠ 0)) = true := by",
        "  decide +kernel",
        "private theorem restrictedRightsLive :",
        "  restrictedRights.all (fun r => decide (rightType r ≠ 0)) = true := by",
        "  decide +kernel",
        "theorem good_live_right (c : Control) (hc : Good c) :",
        "    rightType c.right ≠ 0 := by",
        "  rcases c with ⟨q,r,s⟩",
        "  cases q with",
        "  | false =>",
        "      change r ∈ allRights ∧ s ∈ cSegments at hc",
        "      have h := allMem (fun r => decide (rightType r ≠ 0))",
        "        allRights allRightsLive r hc.1",
        "      simpa using h",
        "  | true =>",
        "      change (r ∈ allRights ∧ s ∈ bCore) ∨",
        "        (r ∈ restrictedRights ∧ s ∈ bExtra) ∨",
        "        (Control.mk true r s = seed) at hc",
        "      rcases hc with h | h | h",
        "      · have hh := allMem (fun r => decide (rightType r ≠ 0))",
        "          allRights allRightsLive r h.1",
        "        simpa using hh",
        "      · have hh := allMem (fun r => decide (rightType r ≠ 0))",
        "          restrictedRights restrictedRightsLive r h.1",
        "        simpa using hh",
        "      · have hh : rightType (Control.mk true r s).right ≠ 0 := by",
        "          rw [h]",
        "          decide +kernel",
        "        exact hh",
        "",
        "-- Source refinement: actual saved and current summaries never have out-of-range modes.",
        "private theorem bCoreLower :",
        "  bCore.all (fun s => decide (-1 ≤ s.imageN ∧ -1 ≤ s.imageP)) = true := by",
        "  decide +kernel",
        "private theorem bExtraLower :",
        "  bExtra.all (fun s => decide (-1 ≤ s.imageN ∧ -1 ≤ s.imageP)) = true := by",
        "  decide +kernel",
        "private theorem cSegmentsLower :",
        "  cSegments.all (fun s => decide (-1 ≤ s.imageN ∧ -1 ≤ s.imageP)) = true := by",
        "  decide +kernel",
        "private theorem savedSegmentsLower :",
        "  savedSegments.all (fun s => decide (-1 ≤ s.imageN ∧ -1 ≤ s.imageP)) = true := by",
        "  decide +kernel",
        "theorem good_segment_lower (c : Control) (hc : Good c) :",
        "    -1 ≤ c.segment.imageN ∧ -1 ≤ c.segment.imageP := by",
        "  rcases c with ⟨q,r,s⟩",
        "  cases q with",
        "  | false =>",
        "      change r ∈ allRights ∧ s ∈ cSegments at hc",
        "      have h := allMem (fun s => decide (-1 ≤ s.imageN ∧ -1 ≤ s.imageP))",
        "        cSegments cSegmentsLower s hc.2",
        "      simpa using h",
        "  | true =>",
        "      change (r ∈ allRights ∧ s ∈ bCore) ∨",
        "        (r ∈ restrictedRights ∧ s ∈ bExtra) ∨",
        "        (Control.mk true r s = seed) at hc",
        "      rcases hc with h | h | h",
        "      · have hh := allMem (fun s => decide (-1 ≤ s.imageN ∧ -1 ≤ s.imageP))",
        "          bCore bCoreLower s h.2",
        "        simpa using hh",
        "      · have hh := allMem (fun s => decide (-1 ≤ s.imageN ∧ -1 ≤ s.imageP))",
        "          bExtra bExtraLower s h.2",
        "        simpa using hh",
        "      · have hh : -1 ≤ (Control.mk true r s).segment.imageN ∧",
        "            -1 ≤ (Control.mk true r s).segment.imageP := by",
        "          rw [h]",
        "          decide +kernel",
        "        exact hh",
        "theorem saved_segment_lower (s : SegmentSummary)",
        "    (hs : s ∈ savedSegments) :",
        "    -1 ≤ s.imageN ∧ -1 ≤ s.imageP := by",
        "  have h := allMem (fun s => decide (-1 ≤ s.imageN ∧ -1 ≤ s.imageP))",
        "    savedSegments savedSegmentsLower s hs",
        "  simpa using h",
        "",
        "theorem seedGood : Good seed := by decide +kernel",
        "theorem blankMem : emptySegment ∈ savedSegments := by decide +kernel",
        "",
        "theorem abstract_never_bad {c : Control} {stack : List SegmentSummary}",
        "    (hr : Reach delta resume emptySegment seed c stack) :",
        "    Action.bad ∉ delta c := by",
        "  exact reachable_no_bad finite_closed blankMem seedGood hr",
        "",
        "#print axioms finite_closed",
        "#print axioms finite_progress",
        "#print axioms abstract_never_bad",
        "end BB6.Agent5Q0151FiniteCertificate",
        "",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")
    print("LEAN_FACTOR_CERT", "controls=814", "rights=17", "bCore=28",
          "bExtra=21", "restricted=12", "cSegments=5", "saved=50",
          "popRequests=12", "rowChecks=46", "lines="+str(len(lines)),
          "output="+str(path))

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("output",type=pathlib.Path)
    generate(parser.parse_args().output)
