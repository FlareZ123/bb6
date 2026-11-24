"""Emit kernel-checkable certificates for the generalized affine family search.

The untrusted search proposes trees. Lean checks every tree with symCheck and
the original-source adapter proves the all-n, all-return-index exclusion.
"""
from fitfamilies import cert, match
from near_power import initial, stats
from symbolic_exclusion import verify

lines = []
names = []
totalnodes = 0
maxdepth = 0
for coeff in range(2, 32, 2):
    if coeff % 3 == 0:
        continue
    for R in (30, 31):
        for off in range(-100, 102, 2):
            cs = [cert(initial(coeff * 3**r + off)) for r in (R, R + 2, R + 4)]
            if any(c is None for c in cs):
                continue
            t = match(cs, R, coeff=coeff)
            if t is None:
                continue
            try:
                nodes, depth = verify(t, R, off, coeff=coeff)
            except (AssertionError, RecursionError):
                continue
            totalnodes += nodes
            maxdepth = max(maxdepth, depth)

            def ser(tree, d=0):
                if tree is None:
                    return "SymCert.stop"
                refs, weights = [], []
                for _, w, _, child in tree[1]:
                    refs.append(ser(child, d + 1))
                    weights.append(f"⟨{w[0] * 3**(R-d-1)},0,{w[1]}⟩")
                return f"(SymCert.fork {weights[0]} {weights[1]} {refs[0]} {refs[1]})"

            suffix = f"m{-off}" if off < 0 else f"p{off}"
            name = f"fA{coeff}R{R}{suffix}"
            names.append(name)
            lines.append(
                f"def {name} : CertifiedGeneralFamily := "
                f"⟨{coeff},{R},{off},{ser(t)},by decide +kernel⟩"
            )
    stats.cache_clear()

assert len(names) == 1355 and totalnodes == 3650, (len(names), totalnodes, maxdepth)
print("""import NearPowerGeneralFamilyCore
namespace BB6.Agent41NearPower
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
""")
print("\n\n".join(lines))
print("def allGeneralFamilies : List CertifiedGeneralFamily := [" + ",".join(names) + "]")
print("#print axioms allGeneralFamilies\nend BB6.Agent41NearPower")
