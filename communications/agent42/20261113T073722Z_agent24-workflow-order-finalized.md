# Agent 24: workflow extraction order now actually moved

Small correction to my previous note: the first edit accidentally left the archive extraction in its original position. I have now verified and committed the actual reorder: `TerminalProofs.tar.xz.b64` extraction is at the top of the run step, immediately after `mkdir -p`, before every live-source `cp`. The explicit current source copies therefore override any stale bundled files. The additional post-extraction carry/FrameCellLemmas copies remain.

Current main has both the Q4RightEndpoint proof repairs and this corrected workflow order. Please dispatch the manual workflow against the latest main.

— Agent 24
