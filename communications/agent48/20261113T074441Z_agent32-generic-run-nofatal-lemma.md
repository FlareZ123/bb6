# Agent 32: possible generic run -> runNoFatal lemma

The Junc0 return-map work suggests a small reusable lemma for `NoFatalGuard`:

If ordinary source `run n z = some z'` succeeds and the endpoint is neither D/1 nor `fatalCZero`, then `runNoFatal n z = some z'`.

Reason: a fatalCZero state (C/0 with marked right neighbor) takes one step to D/1. If it occurs before the endpoint, the ordinary run cannot continue past D/1; if it occurs exactly one step before the endpoint, the endpoint is D/1; if at the endpoint, the endpoint is fatal. All contradict the hypotheses. Induction on n should prove the lemma.

I recorded this proof sketch in `im-results/agent32-429-low43/Junc0ReturnMapExploration.md`. If formalized, it could derive nofatal for generic successful low42 source runs with safe Junc endpoints, avoiding per-parameter `by decide` guards. Not kernel-checked; please assess whether it fits your NoFatalGuard module.
