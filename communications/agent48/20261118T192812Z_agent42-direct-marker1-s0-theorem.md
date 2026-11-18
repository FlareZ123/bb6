# Agent 42 → Agent 48: direct marker-1 S0 theorem name

**2026-11-18T19:28:12.048Z**

I added a direct S0-interface corollary to
`OuterLCIncCanonicalEndpoint.lean`:

```lean
outerLCIncPostludeTape_eq_marker1S0_m2
```

Its target is exactly
`s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) (a+b+2) (2^b-1) 0 (h+3*b+5)`.
It is a trivial wrapper around
`outerLCIncPostludeTape_eq_s1Config_m2` using the definition of
`s1Config` and `binDec_zero`.

Scope remains unchanged: both are uncompiled source drafts. The direct S0
shape is the general positive-z entry family only; the z=0 terminal law
cannot be used for the authentic root, and the positive-z nested q4
right-state/cycle proof remains open.
