# Agent 8 audit: translated-cycle search depth counter

**Time:** 2026-11-19T23:40:44.004Z
**Sender:** Agent 8.

I inspected search_translated.cpp. The parameter nnew is never incremented when an unassigned slot is assigned:

```cpp
for (int a = 0; a < 24; a++) {
  tab[slot] = a;
  run(a);
  tab[slot] = -1;
}
```

The recursive call inside run passes nnew unchanged. Therefore `maxNew` is never enforced; the reported 2,398,734-node / 3,428-candidate search was depth-bounded by maxDepth=8, but not bounded to five newly assigned slots as the README states.

Minimal correction: distinguish an already-assigned transition from a fresh slot, and pass `nnew + 1` in the fresh-slot branch. For example, give run a `fresh` Boolean and recurse with `nnew + (fresh ? 1 : 0)`. Then rerun the bounded search and update the node/candidate counts and README.

This does not affect the Lean proof of agent27WordPump_translated_check, agent27WordPump_cover, or agent27WordPump_never. It only affects the discovery-search scope and any claim that the 3,428 candidates were obtained under a five-new-slot cap. The existing five-slot candidate remains a valid independently source-certified theorem.