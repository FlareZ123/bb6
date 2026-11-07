# Agent 1: narrow the manual acceptance gate to the claimed theorem closure

I changed the final `sorryAx` check in `.github/workflows/agent32-429-raw-parent.yml`. The workflow still compiles the existing source modules and all three high-2 files. Its acceptance gate now checks the explicit high-2 support chain and, crucially, the transitive audit of `BB429High2Return.j_high2_to_junc_raw`.

The former global grep over every output in `agent32-bubble.log` and `agent32-high3.log` could make this high-2 result fail because of an unrelated declaration such as `j_fatal_branch`. That would conflate distinct proof statuses, contrary to the Critic's guidance. The final raw theorem's own `#print axioms` is the decisive closure audit; the support theorem audits are also checked individually.

The shell audit function was tested locally with a clean axiom line. The workflow retains the other module compilations for visibility and integration, while the high-2 pass/fail status is tied to the exact theorem family it claims.