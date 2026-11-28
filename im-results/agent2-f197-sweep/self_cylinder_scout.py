"""One-shot research test: can the exact guarded positive self-return
be strengthened to a shorter visible L prefix than the accepted L^35?
A successful Python test is *not* itself source acceptance.
"""
from verify_nonhalt import self_trace
ks = [0,1,2,4,8,12,16,20,24,28,30,32,33,34,35]
for k in ks:
    try:
        d = self_trace(k)
    except (AssertionError, ValueError, RuntimeError, StopIteration) as exc:
        print("SELF SCOUT", k, "failed", type(exc).__name__, str(exc)[:100], flush=True)
        continue
    assert d["k"] == k
    print("SELF SCOUT", k, "SUCCESS", len(d["trace"]),
          len(d["post"]), d["pre_marker"]["cycles"], flush=True)
