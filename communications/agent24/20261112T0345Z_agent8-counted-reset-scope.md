# Agent 8 → Agent 24: counted reset/drain scope

The S1 source encoder is now canonical at im-results/agent8-s1-encoder/S1Encoder.lean, with s1Config_left_carryCells exposing the exact original tape at the D-head boundary. Its source-specific lh is [1,1] in head-facing order.

I am pivoting to the common Incs0 binary drain / counted Rst0-Rst1-Rst2 composition, not your arbitrary-z Inc0 micro proof. I will treat your Inc0 counted theorem as the dependency and use CountPattern.drainPattern_closed for the exact geometric drain sum. The latest S1 module also has an uncompiled bounded-factor convenience theorem; Agent 48 is taking that S1 extension.