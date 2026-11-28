"""Context-congruent quotient minimization for exact two-stack certificates.

Input is a finite relation certificate from an untrusted abstract search.  Two
left stack states may initially be identified only when they occur beside
EXACTLY the same (control, scanned bit, right-stack-state) contexts in the
relation; the right-side condition is symmetric.  Refine those partitions by
each observed deterministic push successor until congruent.  Project the
relation, inverse-pop edges and push maps, then independently recheck every
projected transition.  This cannot justify a nonhalting claim by itself:
the unchanged Lean `TwoSidedAutomata.check` still checks the emitted finite
relation and `Agent4Automata.never` connects it to the source TM.

Unlike generic DFA minimization, initial context signatures retain the full
opposite-side state, preventing accidental cross-product saturation.  The
post-quotient closure check is essential: no unchecked homomorphism is trusted.
"""
from collections import defaultdict


def _colors(signatures):
    classes = {}
    result = []
    for signature in signatures:
        if signature not in classes:
            classes[signature] = len(classes)
        result.append(classes[signature])
    return result


def minimize(p, cert):
    """Return a strict, independently closure-checked smaller certificate.

    `p` is the 12-entry original TM transition array (3-character bbchallenge
    codes).  `cert` is (ok, n, edges, seen, D, T), as emitted by the
    original two-sided abstract exploration.  No proof axiom is introduced.
    """
    ok, count, edges, seen, D, T = cert
    assert ok and count == len(seen)
    assert len(p) == 12 and len(T) == len(D) == len(edges) == 2
    assert (0, 0, 0, 0) in seen
    contexts = [
        [[] for _ in T[0]],
        [[] for _ in T[1]],
    ]
    for q, b, l, r in sorted(seen):
        assert p[2*q + b] != "---"
        contexts[0][l].append((q, b, r))
        contexts[1][r].append((q, b, l))

    colors = [_colors([tuple(x) for x in side]) for side in contexts]
    for _ in range(max(map(len, T)) + 1):
        refined = []
        for side in (0, 1):
            labels = []
            for i, label in enumerate(colors[side]):
                labels.append((
                    label,
                    *(
                        colors[side][D[side][(i, b)]]
                        if (i, b) in D[side] else -1
                        for b in (0, 1)
                    ),
                ))
            refined.append(_colors(labels))
        if refined == colors:
            break
        colors = refined
    else:
        raise AssertionError("context partition did not stabilize")

    sizes = [max(side) + 1 for side in colors]
    quotient_T = [[""] * sizes[d] for d in (0, 1)]
    representative = [[False] * sizes[d] for d in (0, 1)]
    quotient_D = [{}, {}]
    quotient_edges = [defaultdict(set), defaultdict(set)]

    for d in (0, 1):
        for i, word in enumerate(T[d]):
            cls = colors[d][i]
            if not representative[d][cls]:
                quotient_T[d][cls] = word
                representative[d][cls] = True
            for bit in (0, 1):
                if (i, bit) not in D[d]:
                    continue
                target = colors[d][D[d][(i, bit)]]
                key = (cls, bit)
                assert key not in quotient_D[d] or quotient_D[d][key] == target, (
                    "push congruence violation", d, key,
                )
                quotient_D[d][key] = target
            for bit, pre in edges[d].get(i, ()):
                quotient_edges[d][cls].add((bit, colors[d][pre]))

    quotient_seen = {
        (q, b, colors[0][l], colors[1][r])
        for q, b, l, r in seen
    }
    assert (0, 0, colors[0][0], colors[1][0]) in quotient_seen

    # Every incoming edge must name the recorded push target.  This is an
    # independent local consistency check, not a trusted quotient theorem.
    for d in (0, 1):
        assert (0, colors[d][0]) in quotient_edges[d][colors[d][0]]
        for target, inverse in quotient_edges[d].items():
            for bit, pre in inverse:
                assert quotient_D[d].get((pre, bit)) == target or (
                    target == colors[d][0] and bit == 0 and pre == colors[d][0]
                    and (0, 0) in edges[d].get(0, ())
                ), ("edge/push mismatch", d, target, bit, pre)

    # Recheck *all* transitions of the quotient relation, including cross
    # products of inverse-pop edges introduced by merged stack states.
    for q, b, l, r in quotient_seen:
        mv = p[2*q + b]
        assert mv != "---"
        write = int(mv[0])
        leftward = mv[1] == "L"
        d = int(leftward)
        pushed_from = r if leftward else l
        popped_from = l if leftward else r
        assert (pushed_from, write) in quotient_D[d]
        pushed = quotient_D[d][(pushed_from, write)]
        ns = ord(mv[2]) - 65
        for read, pre in quotient_edges[1-d][popped_from]:
            nxt = (
                (ns, read, pre, pushed) if leftward
                else (ns, read, pushed, pre)
            )
            assert nxt in quotient_seen, ("quotient not closed", (q,b,l,r), nxt)

    return (
        True,
        len(quotient_seen),
        quotient_edges,
        quotient_seen,
        quotient_D,
        quotient_T,
    )
