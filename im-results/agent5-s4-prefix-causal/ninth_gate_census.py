"""Exact finite nine-digit S4 prefix-gate census.

The deterministic nine-digit projection `pp` is the original source-aligned
projection from ninth_digit_candidate.py. This program does not simulate a
hypothetical infinite suffix. Its output is a finite, reproducible arithmetic
census for the source-certified projected 81920-return cycle.

Mathematical interpretation: for a successful genuine S4 trajectory, each
G(c, prefix ++ suffix) can halt only if W(prefix)+c is divisible by 512,
because W(prefix ++ suffix)=W(prefix)+512*W(suffix) and all such numbers
exceed 512. See S4Octet.G_none_iff_power and S4PrefixCausal.prun_prefix.
"""

from collections import Counter

from ninth_digit_candidate import gp, pp

CYCLE_NINE = (
    283, 906, 982, 3490, 3734, 5935, 13580, 109210, 171050
)
OFFSETS = (509, 290, 219)
PERIOD = 81920
MODULUS = 1 << len(CYCLE_NINE)


def weight(digits: tuple[int, ...]) -> int:
    return sum((digit + 1) << i for i, digit in enumerate(digits))


def census() -> tuple[list[tuple[int, int]], Counter[tuple[bool, bool, bool]]]:
    prefix = CYCLE_NINE
    mask_counts: Counter[tuple[bool, bool, bool]] = Counter()
    candidate_phases: list[tuple[int, int]] = []

    for phase in range(PERIOD):
        stage_prefixes = (
            prefix,
            gp(509, prefix),
            gp(290, gp(509, prefix)),
        )
        assert all(len(stage) == len(CYCLE_NINE) for stage in stage_prefixes)
        stage_inputs = tuple(weight(p) + c for p, c in zip(stage_prefixes, OFFSETS))
        assert min(stage_inputs) > MODULUS
        mask = tuple(n % MODULUS == 0 for n in stage_inputs)
        mask_counts[mask] += 1
        if any(mask):
            candidate_phases.append((phase, next(i for i, bad in enumerate(mask) if bad)))
        prefix = pp(prefix)

    assert prefix == CYCLE_NINE
    assert len(candidate_phases) == 703
    assert mask_counts == Counter({
        (False, False, False): 81217,
        (True, False, False): 118,
        (False, True, False): 196,
        (False, False, True): 389,
    })
    return candidate_phases, mask_counts


def main() -> None:
    phases, masks = census()
    print("Original S4 root-synchronized prefix: return 5457 + n")
    print("Period:", PERIOD, "prefix digits:", len(CYCLE_NINE))
    print("Unrestricted-suffix safe phases:", masks[(False, False, False)])
    print("Potential binary-power stopping phases:", len(phases))
    print("By source stage G(509), G(290), G(219):", 118, 196, 389)
    print("Earliest candidate phase:", phases[0])
    print("Last candidate phase:", phases[-1])
    print("Distinct-stage disjointness: verified")


if __name__ == "__main__":
    main()
