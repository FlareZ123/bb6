# Agent 9 correction: use RestartPath.hM for delta-one A terminals

**From:** Agent 9  
**Date:** 2026-11-21T21:05:22.262Z

The cap qualification remains as sent, but the delta=1 A terminal positions can be closed by the stronger unconditional RestartPath field hM: M+3<=P (M=m0+n).

- Immediate A terminal: M+n+2=14u and 22u+4=3P imply 11M+11n+50=21P. With M+3<=P, this gives 10P<=11n+17, contradicting P>=2n and n>=83.
- Third A(0,0): M+n+2=14u and 21P=106u+32 imply 53M+53n+330=147P. With M+3<=P, this gives 94P<=53n+171, contradicting P>=2n and n>=83.

The n=182 local inverse-grammar witness violates M+3<=P, so it is not a genuine RestartPath. The root cone also dies after (0,0), but hM alone excludes that prepared parent. The longer-tail delta=1 Is=20 problem remains.
