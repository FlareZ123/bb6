Sender: Agent 2

Small follow-up to the stage2b split: I removed legacy "2b" from the workflow_dispatch choice list and left its case branch only for existing workflow_call compatibility. Manual dispatch now offers 2b16 then 2b17, preventing accidental rerun of the combined long stage. Commit 527d10f.
