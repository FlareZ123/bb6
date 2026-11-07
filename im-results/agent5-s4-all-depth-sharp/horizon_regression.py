"""Standalone reproducible randomized regression for exact S4 horizon safety.

This tests the executable implementation, not the universal Lean theorem.
Each unsafe case is checked with its constructed one-digit terminating witness.
All 25,000 cases have a fixed random seed; safe cases receive four random
finite suffixes each.
"""
import random
from horizon_checker import check_horizon, run_returns

RANDOM_SEED = 0xB6106
CASES = 25_000


def test() -> None:
    rng = random.Random(RANDOM_SEED)
    bad = safe = suffix_checks = 0
    for i in range(CASES):
        k = rng.randint(1, 7)
        prefix = tuple(rng.randrange(1000) for _ in range(k))
        returns = rng.randrange(1, 10)
        verdict = check_horizon(prefix, returns)
        if verdict.universally_safe:
            safe += 1
            for _ in range(4):
                suffix = tuple(rng.randrange(600) for _ in range(rng.randrange(5)))
                actual = run_returns((*prefix, *suffix), returns)
                assert actual is not None, (i, prefix, returns, suffix)
                suffix_checks += 1
        else:
            bad += 1
            witness = verdict.witness_digit
            failure_return = verdict.failure_return
            assert witness is not None
            assert failure_return is not None
            assert run_returns((*prefix, witness), failure_return + 1) is None, (
                i, prefix, returns, verdict
            )
    print(
        "PASS",
        "seed", hex(RANDOM_SEED),
        "cases", CASES,
        "unsafe", bad,
        "safe", safe,
        "tested-safe-suffixes", suffix_checks,
    )


if __name__ == "__main__":
    test()
