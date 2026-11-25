#!/usr/bin/env bash
set -euo pipefail
mkdir -p run-old run-q0 run-results
gh run download 45609016982 --repo FlareZ123/bb6 --pattern 'fast-source-*' --dir run-old
gh run download 45607737965 --repo FlareZ123/bb6 --name phase-mitm-certificates --dir run-q0
old_dir=$(dirname "$(find run-old -name Agent5FastResume_0_20000.vo -print -quit)")
q0_dir=$(dirname "$(find run-q0 -name Agent5PhaseMITM_0.vo -print -quit)")
[[ -f "$old_dir/Agent5FastResume_0_20000.vo" ]]
[[ -f "$q0_dir/Agent5PhaseMITM_0.vo" ]]
cp "$old_dir/"*.v "$old_dir/"*.vo .
cp "$q0_dir/Agent5PhaseMITM_0.vo" .
if [[ -f "$q0_dir/Agent5PhaseMITM.v" ]]; then cp "$q0_dir/Agent5PhaseMITM.v" Agent5PhaseMITM_0.v; fi
python3 "$GITHUB_WORKSPACE/research/im-results/agent5-weighted-tnf-queue/run_residue_mitm.py" "$old_dir/Agent5FastResume_0_20000.log" run-results --exclude 1RB1RD_1RC0LD_0LA0RE_1LA1LB_0RF---_0LA1RA
cp run-results/Agent5RunMITM.v .
coqc -Q . BusyCoq -native-compiler no Agent5RunMITM.v 2>&1 | tee run-results/run-cert.log
cat > Agent5FastHeldDischarge.v <<'COQ'
From BusyCoq Require Import Enumerate62 Individual62 Agent8QueueCheckpoint Agent8WeightedSource
  Agent32SourceBackwards SourceResidualRoster Agent5RosterComplement Agent5RunMITM
  Agent5FastResume_0_20000 Agent5PhaseMITM_0.
From Coq Require Import List Bool NArith.
Import ListNotations TNF_Node.
Open Scope nat_scope.
Open Scope string_scope.

Definition fast_complete_roster : list TM :=
  TM_from_str "1RB1RD_1RC0LD_0LA0RE_1LA1LB_0RF---_0LA1RA" :: run_certified.
Theorem fast_complete_roster_safe bound :
  Forall (source_table_safe bound) fast_complete_roster.
Proof.
  constructor.
  - apply source_nonhalt_cylinder, phase_nonhalt_0.
  - apply run_certified_safe.
Qed.
Definition fast_queue := decode_queue fast_packed.
Theorem fast_held_checked :
  forallb (source_roster_covers fast_complete_roster) (snd fast_queue) = true.
Proof. vm_compute. reflexivity. Qed.
Theorem fast_held_closed bound :
  Forall (source_weighted_safe bound) (snd fast_queue).
Proof.
  eapply source_obligations_from_roster; [apply fast_complete_roster_safe|exact fast_held_checked].
Qed.
Definition fast_active_remaining := roster_remaining fast_complete_roster (fst fast_queue).
Theorem fast_reduced_source_covered bound :
  (N.to_nat 1000000 + 6 <= bound)%nat ->
  Forall (source_weighted_safe bound) fast_active_remaining ->
  safeQ (source_weighted_safe bound) (q_i 0 100).
Proof.
  intros HB H. apply fast_source_covered; [exact HB|].
  split.
  - apply (proj2 (roster_remaining_safe_iff bound _ _ (fast_complete_roster_safe bound))). exact H.
  - apply fast_held_closed.
Qed.
Print Assumptions fast_held_closed.
Print Assumptions fast_reduced_source_covered.
Eval vm_compute in (List.length (fst fast_queue), List.length (snd fast_queue), List.length fast_active_remaining).
COQ
coqc -Q . BusyCoq -native-compiler no Agent5FastHeldDischarge.v 2>&1 | tee run-results/fast-held.log
cp Agent5RunMITM.vo Agent5FastHeldDischarge.v Agent5FastHeldDischarge.vo run-results/
cp "$old_dir/"*.v "$old_dir/"*.vo run-results/
cp Agent5PhaseMITM_0.vo run-results/
echo "summary=all-held-discharged" >> "$GITHUB_OUTPUT"
