import ControlPathAudit

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/- Interpreted evaluation, NOT a kernel-checked equality proof. The
    proof of soundness of every certified leaf is kernel-checked in
    ControlPathAudit. This run measures the actual certified/open mass
    of that compact original-source proof-carrying audit tree. -/
#eval BB6Coverage.globalControlPathAudit.report
