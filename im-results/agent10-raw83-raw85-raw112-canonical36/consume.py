#!/usr/bin/env python3
"""Consume accepted Raw83, Raw85, Raw112 together on accepted Canonical39."""
import argparse, json, shutil, subprocess, sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
SIBLINGS=HERE.parent
REPO=HERE.parents[1]
A32=SIBLINGS/"agent32-raw42"
A11=SIBLINGS/"agent11-raw39"
A31=SIBLINGS/"agent31-shared-core"
A17=SIBLINGS/"agent17-raw112-canonical58"
for p in (A32,A31,A17): sys.path.insert(0,str(p))
import check_canonical39_after_raw39 as raw39
import assemble_canonical59_five_parent as five
import assemble_canonical_selected as selected
from assemble_canonical58_raw112_graft import verify_raw112_parent

ALLOWED={"propext","Classical.choice","Quot.sound"}
RAW83_SPEC={"label":"raw83","run_id":45755362807,"revision":"8d8a3fcc59600146fb25eb70afc2f34a31c99cb3","artifact_id":15087730774,"artifact_name":"raw83-parent-proof","digest":"89ea0f6ae8f0da2d11f86c959b1d848d7c4ef44e933899bfc2654c7dc1a9a1a2","root":"A10Raw83Exact","theorem":"BB6.Agent10Raw83.all_completions","table":"1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RA","bound":514,"size":9709805}
RAW85_SPEC={"label":"raw85","run_id":45585065939,"revision":"52ea69fba34b5f37bbc630392d2dc6dc1d3affbe","artifact_id":15008641615,"artifact_name":"raw85-bound-certified","digest":"a9ff7c78fb926a7a4c172b9a76c2e5a3681268943e312a3adb306930153798c7","root":"Raw85Bound","theorem":"BB6.Agent21Raw85.all_completions","table":"1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1RA","bound":7014,"size":9435332}
NS="BB6.Agent10Raw83Raw85Raw112Canonical36AfterRaw39"
TARGETS=[NS+x for x in [".p83_count39",".p85_count39",".p112_count39",".parents_pairwise",".p83_cover",".p85_cover",".p112_cover",".count36",".raw83_removed",".raw85_removed",".raw112_removed",".sound_integrated",".sound_at",".exact_at_champion_score"]]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work",type=Path,required=True)
    ap.add_argument("--raw112-run-id",type=int,default=46146501930)
    ap.add_argument("--onele-run",type=int,default=46114235329)
    ap.add_argument("--chunk-size",type=int,default=64)
    a=ap.parse_args()
    work=a.work.resolve(); work.mkdir(parents=True,exist_ok=False)
    evidence=work/"evidence"; evidence.mkdir()

    canonical, predecessor=raw39.canonical_source(work/"canonical")
    parent_linked,parent=raw39.accepted_parent(work/"raw39-parent",a.onele_run)
    assert parent["bound"]==28311 and len(parent["producers"])==11
    tool=raw39.compile_stage_kernel(work,canonical)
    transport,staged_objects,staged_names=raw39.relocate_chunked(
        producer_files=sorted(parent_linked.glob("*.olean")),base=canonical,
        work=work/"raw39-staged",root_module="Raw39CompleteJoin",
        root_names=["BB6.Agent11Raw39Closed.parent_bound"],
        prefix="A10Raw39Raw83Raw85Raw112Slice",tool=tool,
        comparator_batch=A11/"CompareKernelImportsBatch.lean",
        allow_compatible=True,chunk_size=a.chunk_size)
    assert transport["complete"] and "BB6.Agent11Raw39Closed.parent_bound" in staged_names
    for f in sorted(staged_objects.glob("*.olean")):
        d=canonical/f.name
        if d.exists(): assert raw39.sha(d)==raw39.sha(f),f.name
        else: shutil.copy2(f,d)
    bridge=raw39.generated_bridge(work,transport["staged_root"],staged_names,
        namespace="A10Raw39Raw83Raw85Raw112Slice",
        compatible=(transport.get("mode")=="authenticated-original-compatible-link"))
    profiles={}; roots={}
    for source,targets in ((bridge,raw39.RAW39_BRIDGE),(A11/"Raw39Canonical39Successor.lean",raw39.RAW39_SUCCESSOR)):
        root,p=raw39.source_check(source,canonical,evidence,targets)
        roots[root.name]=raw39.sha(root); profiles.update(p)

    family_reports={}
    for spec,key in ((RAW83_SPEC,"raw83"),(RAW85_SPEC,"raw85")):
        w=work/(key+"-parent"); w.mkdir()
        dirs,meta=five.download_parent(spec,w)
        copied=[]; audit={}
        selected.add_family(spec,dirs,canonical,copied,audit)
        assert (canonical/(spec["root"]+".olean")).is_file()
        family_reports[key]={"spec":spec,"artifact":meta,"link_audit":audit,"copied_modules":[str(p) for p in copied]}

    w=work/"raw112-parent"; w.mkdir()
    m112,d112,s112=verify_raw112_parent(w,a.raw112_run_id)
    c112=[]; a112={}
    selected.add_family({"root":"Raw112ClosedCover"},d112,canonical,c112,a112)
    assert (canonical/"Raw112ClosedCover.olean").is_file()

    source=HERE/"Raw83Raw85Raw112Canonical36AfterRaw39.lean"
    root,p=raw39.source_check(source,canonical,evidence,TARGETS)
    roots[root.name]=raw39.sha(root); profiles.update(p)
    assert all(set(ax)<=ALLOWED for ax in profiles.values()),profiles

    report={
      "status":"source-checked Raw83 plus Raw85 plus Raw112 successor of accepted Raw39 Canonical39",
      "source_revision":subprocess.check_output(["git","rev-parse","HEAD"],cwd=REPO,text=True).strip(),
      "accepted_predecessor":predecessor,"raw39_parent":parent,
      "raw39_transport_mode":transport["mode"],"raw39_transport_affected_modules":transport["affected_modules"],
      "previous_residual_count":39,"remaining_residual_count":36,
      **family_reports,
      "raw112_run_id":a.raw112_run_id,"raw112_artifact_name":m112["artifact_name"],
      "raw112_artifact_id":m112["artifact_id"],"raw112_artifact_sha256":m112["artifact_digest"],
      "raw112_parent_table":"1RB---_1RC---_0RD---_1LD1RE_---1LC_------",
      "raw112_parent_theorem":"BB6.Agent47Raw112.parent_cover","raw112_weighted_bound":100000,
      "raw112_retry_summary":s112,"raw112_link_audit":a112,
      "theorems":profiles,"roots":roots,"exact_at_champion_score":NS+".exact_at_champion_score"}
    (evidence/"raw83-raw85-raw112-after-raw39-canonical36.json").write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print("PASS: accepted Raw39 Canonical39 -> Raw83 + Raw85 + Raw112 -> Canonical36; exactly 36 Cover obligations remain",flush=True)

if __name__=="__main__": main()
