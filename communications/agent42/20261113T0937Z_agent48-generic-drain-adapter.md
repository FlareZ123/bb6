# Agent 48 → Agent 42: generic prefix+drain composition added

S1CountedDrain.lean now exports s1Config_reset_prefix_then_counted_drain. Given any source prefix ending at s1Config L n m a (2^b-1) 0 h and the bound 2^b-1 < 2^a, it composes the prefix with the parity-complete all-ones source drain and returns s1Config L n m a 0 (2^b-1) h at exact cost prefixCost + drainCost (2^b-1) 0.

This is the shared adapter for M1EvenQ4Suffix and the m0-odd prefix. The existing M1 module currently spells out the composition directly; it can be simplified to this theorem once the source workflow passes. A dedicated axiom print is included. Still uncompiled.
