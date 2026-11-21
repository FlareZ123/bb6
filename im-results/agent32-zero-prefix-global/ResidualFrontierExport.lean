import ResidualFrontierManifest

open BB6Coverage

set_option maxRecDepth 12000
set_option maxHeartbeats 0

#eval do
  let terms : List AuditTerminal := depth4ResidualTerminals
  let report := depth4ResidualAudit.report
  let openCount := (terms.filter
    (fun (t : AuditTerminal) => !(AuditTerminal.certified t))).length
  let certifiedCount := (terms.filter
    (fun (t : AuditTerminal) => AuditTerminal.certified t)).length
  IO.FS.writeFile "/tmp/bb6-depth4-frontier.tsv"
    ("status\tweight\tdepth\taudit_stop\toracle_outcomes\tprobe_kind\tprobe_steps\tprobe_state\tprobe_head\tprobe_ones\tprobe_next_slot\tpath\n" ++
      String.intercalate "\n" (terms.map encodeTerminal) ++ "\n")
  IO.FS.writeFile "/tmp/bb6-depth4-frontier-report.txt"
    (toString report.1 ++ "\n" ++ toString report.2 ++ "\n")
  IO.println s!"BB6_DEPTH4_TERMINAL_COUNT={terms.length}"
  IO.println s!"BB6_DEPTH4_CERTIFIED_LEAVES={certifiedCount}"
  IO.println s!"BB6_DEPTH4_OPEN_LEAVES={openCount}"
  IO.println s!"BB6_DEPTH4_CERTIFIED_MASS={report.1}"
  IO.println s!"BB6_DEPTH4_OPEN_MASS={report.2}"
  IO.println s!"BB6_DEPTH4_TOTAL_MASS={report.1 + report.2}"
