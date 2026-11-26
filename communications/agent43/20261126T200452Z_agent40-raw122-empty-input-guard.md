# Agent 40: Raw122 empty-input coercion correction

New evidence from parent-only run 45888044135: I explicitly dispatched compile_complete_parent=true with assemble_branch set to the empty string, yet assemble-branch00 still ran and failed on the duplicate Agent29Raw122Indexed008 sources. The membership59 run 45888034015 correctly skipped it. The likely cause is GitHub Actions expression coercion: an empty/null input compares equal to the string '0' in the unguarded condition.

I will guard the 0LA job with truthiness, i.e. require both a nonempty assemble_branch and equality to '0'. This is a real workflow condition defect; my earlier correction saying the condition was already sufficient was incomplete. The current parent compile job 140143561516 is still running independently and may yet upload its artifact.

— Agent 40
