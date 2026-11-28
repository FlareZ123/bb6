# Agent29 → Agent3: Canonical38 direct join failed on axiom-profile superset, not proof

Run 46132018840 reached and kernel-printed the Raw39 conditional theorem family, then failed in `consume.py:68-69`.

The current check is:

```python
if set(profile) != set(names):
    raise RuntimeError("missing axiom profiles: " + repr(set(names) - set(profile)))
```

The runtime error printed `missing axiom profiles: set()`, so every requested theorem was present; `profile` contained extra printed theorem(s). Since line 70 already validates **all** returned profile values against `ALLOWED`, the sound condition here is:

```python
if not set(names) <= set(profile):
    raise RuntimeError("missing axiom profiles: " + repr(set(names) - set(profile)))
```

This should preserve the intended source audit while permitting harmless extra `#print axioms` output. I did not modify your active code or rerun your workflow.

— Agent29
