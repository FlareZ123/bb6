# Agent 18: rooted #429 terminal residue 253 modulo 1024

**Status, 2026-11-04:** the standalone inverse proof compiled locally in Lean 4.36.0-rc2 with exact arithmetic and imported-theorem signature stubs; the genuine, unchanged-repository source audit is **pending** in [manual run 41864904707](https://github.com/FlareZ123/bb6/actions/runs/41864904707). This file remains an intermediate result. BB(6) and the complete #429 root remain unresolved.

## Mathematical claim

[BB429No253.lean](BB429No253.lean) contains an all-natural exact inverse certificate:

    theorem blank_halt_not_253_mod1024 (n q : Nat)
      (hr : BB429.run n (0,0) =
        some (1024*q+253,2048*q+505)) : False

    theorem blank_halt_mod1024_ne_253 (n a b : Nat)
      (hr : BB429.run n (0,0)=some (a,b))
      (hg : b+1=2*a) : a%1024 ≠ 253

The excluded 253 modulo 1024 terminal family is inside the 125 modulo 128 sector which survives Agent6's earlier original-source-certified six-lift necessary halt filter ([CI 41847807220](https://github.com/FlareZ123/bb6/actions/runs/41847807220)). It removes one proper infinite family, without deciding the other possible terminals.

The exhaustive backward predecessor tree, beginning with T(q)=(1024q+253,2048q+505), is:

    T(q)
    └─ (512q+125,3072q+758)
       ├─ (1280q+308,1536q+381) [positive even u, w%4=1: forbidden]
       └─ (256q+61,3584q+883)
          └─ (128q+29,3840q+944)
             └─ (64q+13,3968q+973)
                └─ (32q+5,4032q+986)
                   ├─ (16q+1,4064q+991) [u%8=1,w%4=3: forbidden]
                   └─ (1040q+245,2016q+495)
                      └─ (520q+121,3056q+740)
                         └─ (260q+59,3576q+861)
                            └─ (130q+28,3836q+920)
                               [positive even u,w%4=0: forbidden]

Every edge is an *all-input, all-natural, exhaustive* inverse step of the exact high-level function, checked through case-splitting the entire original model. No synthetic inverse is assumed reachable. An actual reached positive-u node has a reached predecessor, which the proof forces along these branches. The forbidden leaves use precisely two existing genuine-blank-root, all-time theorems: Agent6's positive-even-first-counter implies second-counter 2 modulo 4, and Agent6's mod8/mod4 allowed-orbit invariant. The proof includes q=0.

## Native source transport

[SourceRawHaltNo253.lean](SourceRawHaltNo253.lean) composes the result with the original-pinned Cryptids source via existing unchanged source-to-local equalities and Agent6's exact raw-machine six-lift equivalence. Once source CI succeeds, it will give the original raw-TM halting iff the existence of a *genuine blank-reachable* remaining terminal that also has first counter different from 253 modulo 1024. An equivalence of halting to candidate terminals is **not** an assertion of a halt.

The committed Lean inverse module has SHA-256 01ede4c48007ffcc6b310b786117536f3fa9306a3617b22d16bc4eaa4191faa1. Local axioms on leaf classification are only Lean fundamentals; the local final theorem *additionally depends on two theorem-signature stubs*, because checked-in prerequisites were not locally compiled in that test. The manual-only [full source workflow](../../.github/workflows/agent6-429-source-chain.yml) compiles all three real checked-in modules without stubs and builds pinned original Cryptids. Do not claim the full integration until its jobs pass.

## Follow-up

An exploratory symbolic-backward test suggested that other classes under the 125 modulo128 sector could close, especially first-counter 125,381,509 modulo1024. These are *unproven*. For 125 modulo1024 the small parameter q=0 may require a separate finite true-root argument. Check overlap with Agent6's concurrent #429 work before extending; aim ultimately at a complete surviving family or actual halting witness.
