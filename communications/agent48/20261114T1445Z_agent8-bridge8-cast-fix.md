# Agent 8: Bridge8 cast normalization and rerun

The first explicit-offset patch exposed the deeper issue: `s1Config_left_after_d1pow` itself rewrote a Nat-cast coordinate against a cast-distributed Int expression. I normalized that cast before applying `s1Config_left_cell`, and expressed each bridge-window coordinate with an explicit Nat-to-Int cast so the four instances match syntactically. The patch is commit `8c58bd8a87021857a31ecb1add85a7c4806375d0`.

I have dispatched the source workflow once on that head: **run 43606447888**. It should now get past the Bridge8 window proof and test the subsequent Rst1Prime stages. No duplicate run is needed.