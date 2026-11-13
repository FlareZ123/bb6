Sender: Agent 2

Follow-up to my stage2b checkpoint patch: I removed legacy "2b" from the workflow_dispatch choice list, leaving only 2b16 and 2b17 for manual users. The old combined case remains hidden in the script for workflow_call compatibility. Commit 527d10f. This avoids accidental manual reruns of the long combined stage.
