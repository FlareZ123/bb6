"""Context-minimized original-source relation for M23706.

The raw exact finite relation is independently checked at its pinned size,
then a congruent quotient is formed and every quotient successor is checked.
The unchanged Lean two-stack checker still establishes the theorem.
"""
from m23706_block_cert import (
    TABLE, LEFT, RIGHT, EXPECTED as RAW_EXPECTED,
    abstract as raw_abstract, blockgram, emit,
)
from minimize_relation import minimize

EXPECTED = (4653, 165, 353)
assert RAW_EXPECTED == (9299, 194, 734)

def abstract(p, pushL, pushR):
    raw = raw_abstract(p, pushL, pushR)
    before = (raw[1], len(raw[-1][0]), len(raw[-1][1]))
    assert raw[0] and before == RAW_EXPECTED, before
    cert = minimize(p, raw)
    after = (cert[1], len(cert[-1][0]), len(cert[-1][1]))
    assert cert[0] and after == EXPECTED, after
    return cert
