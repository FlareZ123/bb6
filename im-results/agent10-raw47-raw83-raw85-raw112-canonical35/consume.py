#!/usr/bin/env python3
"""Consume accepted Raw47, Raw83, Raw85, Raw112 together after accepted Raw39."""
import argparse,json,shutil,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent; SIBLINGS=HERE.parent; REPO=HERE.parents[1]
A9=SIBLINGS/"agent9-canonical38-official"; A11=SIBLINGS/"agent11-raw39"; A31=SIBLINGS/"agent31-shared-core"; A17=SIBLINGS/"agent17-raw112-canonical58"
for p in (A9,A31,A17): sys.path.insert(0,str(p))
import consume as official
import assemble_canonical59_five_parent as five
import assemble_canonical_selected as selected
from assemble_canonical58_raw112_graft import verify_raw112_parent
c=official.c; raw47=official.raw47
ALLOWED={"propext","Classical.choice","Quot.sound"}
RAW83_SPEC={"label":"raw83","run_id":45755362807,"revision":"8d8a3fcc59600146fb25eb70afc2f34a31c99cb3","artifact_id":15087730774,"artifact_name":"raw83-parent-proof","digest":"89ea0f6ae8f0da2d11f86c959b1d848d7c4ef44e933899bfc2654c7dc1a9a1a2","root":"A10Raw83Exact","theorem":"BB6.Agent10Raw83.all_completions","table":"1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RA","bound":514,"size":9709805}
RAW85_SPEC={"label":"raw85","run_id":45585065939,"revision":"52ea69fba34b5f37bbc630392d2dc6dc1d3affbe","artifact_id":15008641615,"artifact_name":"raw85-bound-certified","digest":"a9ff7c78fb926a7a4c172b9a76c2e5a3681268943e312a3adb306930153798c7","root":"Raw85Bound","theorem":"BB6.Agent21Raw85.all_completions","table":"1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1RA","bound":7014,"size":9435332}
NS="BB6.Agent10Raw47Raw83Raw85Raw112Canonical35AfterRaw39"
TARGETS=[NS+x for x in [".p47_count39",".p83_count39",".p85_count39",".p112_count39",".p47_cover",".p83_cover",".p85_cover",".p112_cover",".count35",".raw47_removed",".raw83_removed",".raw85_removed",".raw112_removed",".sound_integrated",".sound_at",".exact_at_champion_score"]]

def main():
 ap=argparse.ArgumentParser(description=__doc__); ap.add_argument("--work",type=Path,required=True); ap.add_argument("--direct38-run-id",type=int,required=True); ap.add_argument("--raw112-run-id",type=int,default=46146501930); a=ap.parse_args()
 work=a.work.resolve(); work.mkdir(parents=True,exist_ok=False); evidence=work/"evidence"; evidence.mkdir()
 accepted39=official.authenticate_accepted39(evidence)
 linked,_,_,base_report=c.base.verify_base(work,c.base.BASE_RUN)
 sharp=c.resume.restore_sharp(work,linked,base_report)
 ready,_,ready_pin=c.extra.restore_ready(work,linked,sharp,46031670976); assert ready["remaining_residual_count"]==46
 prior41,pin41=c.restore_extra(work,linked,ready,ready_pin); assert prior41["remaining_residual_count"]==41
 prior40,pin40=raw47.restore_canonical40(work,linked,prior41,pin41); assert prior40["remaining_residual_count"]==40
 transport_report,transport_pin,_=official.restore_transport(work,linked,prior40,pin40,a.direct38_run_id)
 profiles={}; roots={}
 root39,ax39=official.source_check(A11/"Raw39Canonical39Successor.lean",linked,evidence,official.RAW39_TARGETS)
 roots[root39.name]=c.a68.sha(root39); profiles.update(ax39)
 families={}
 for spec,key in ((RAW83_SPEC,"raw83"),(RAW85_SPEC,"raw85")):
  w=work/(key+"-parent"); w.mkdir(); dirs,meta=five.download_parent(spec,w); copied=[]; audit={}
  selected.add_family(spec,dirs,linked,copied,audit); assert (linked/(spec["root"]+".olean")).is_file()
  families[key]={"spec":spec,"artifact":meta,"link_audit":audit,"copied_modules":[str(p) for p in copied]}
 w=work/"raw112-parent"; w.mkdir(); m112,d112,s112=verify_raw112_parent(w,a.raw112_run_id); c112=[]; a112={}
 selected.add_family({"root":"Raw112ClosedCover"},d112,linked,c112,a112); assert (linked/"Raw112ClosedCover.olean").is_file()
 source=HERE/"Raw47Raw83Raw85Raw112Canonical35AfterRaw39.lean"; root,p=official.source_check(source,linked,evidence,TARGETS)
 roots[root.name]=c.a68.sha(root); profiles.update(p); assert all(set(v)<=ALLOWED for v in profiles.values()),profiles
 report={"status":"source-checked Raw47 plus Raw83 plus Raw85 plus Raw112 successor of accepted Raw39 Canonical39","source_revision":subprocess.check_output(["git","rev-parse","HEAD"],cwd=REPO,text=True).strip(),"accepted_canonical39":accepted39,"canonical40_delta":pin40,"canonical40_root_sha256":prior40["root_sha256"],"raw47_transport_carrier":transport_pin,"raw47_transport_status":transport_report["status"],"previous_residual_count":39,"remaining_residual_count":35,**families,"raw112_run_id":a.raw112_run_id,"raw112_artifact_name":m112["artifact_name"],"raw112_artifact_id":m112["artifact_id"],"raw112_artifact_sha256":m112["artifact_digest"],"raw112_parent_table":"1RB---_1RC---_0RD---_1LD1RE_---1LC_------","raw112_parent_theorem":"BB6.Agent47Raw112.parent_cover","raw112_weighted_bound":100000,"raw112_retry_summary":s112,"raw112_link_audit":a112,"theorems":profiles,"roots":roots,"exact_at_champion_score":NS+".exact_at_champion_score"}
 (evidence/"raw47-raw83-raw85-raw112-after-raw39-canonical35.json").write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
 print("PASS: accepted Raw39 Canonical39 -> Raw47 + Raw83 + Raw85 + Raw112 -> Canonical35; exactly 35 Cover obligations remain",flush=True)
if __name__=="__main__": main()
