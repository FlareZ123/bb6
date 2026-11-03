"""Conditional L checkpoints closed under two E-exception returns where possible.

Each underlying one-step and two-step rule comes from existing D0 original-source
universal macro endpoint identities, but the combined rooted chain is unproved.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
import hashlib

from check_root_L_escape import L, next_source_macro


@dataclass(frozen=True)
class Outside:
    k: int
    q: int
    a: int
    witness_suffix: str = "(01)^2 0 1^(2q-3) 0 1^6"


def second_of_exception(c: L) -> L | Outside:
    assert c.a % 3 == 1 and c.q >= 1 and c.b == 1
    k = (c.a - 4) // 3
    t, r = divmod(k, 3)
    q = c.q
    if q == 1:
        if r == 0:
            return L(64 * t + 27)
        if r == 1:
            return L(64 * t + 37, 3, 0)
        return L(64 * t + 49, 6, 0)
    if r == 0:
        return L(64 * t + 17 + 2 * q, 1, 5)
    if r == 1:
        if q == 2:
            return L(64 * t + 33, 4, 5)
        return Outside(k, q, 64 * t + 33)
    u, s = divmod(2 * q, 3)
    if s == 0:
        return L(64 * t + 65 + 8 * u)
    if s == 1:
        return L(64 * t + 77 + 8 * u)
    return L(64 * t + 59 + 8 * u, 3, 2)


def fingerprint(n: int) -> str:
    return hashlib.sha256(n.to_bytes((n.bit_length() + 7) // 8, 'little')).hexdigest()


def trace(seed: int, max_sections: int = 120000) -> dict:
    state = L(seed)
    index = 0
    exceptions = []
    labels = Counter()
    while index < max_sections:
        nxt, label = next_source_macro(state)
        labels[label] += 1
        if nxt is None:
            after = second_of_exception(state)
            if isinstance(after, Outside):
                return {'seed': seed, 'sections': index, 'exception_count': len(exceptions) + 1,
                        'halted_at_outside': True, 'k_mod3': after.k % 3, 'q': after.q,
                        'input_a_bits': state.a.bit_length(),
                        'input_a_sha256_le': fingerprint(state.a),
                        'output_a_bits': after.a.bit_length(),
                        'output_a_sha256_le': fingerprint(after.a),
                        'previous_exceptions': exceptions[-12:], 'labels': dict(labels)}
            exceptions.append({'index': index, 'r': (state.a - 4) // 3 % 3, 'q': state.q,
                               'a_bits': state.a.bit_length(),
                               'output_a_bits': after.a.bit_length()})
            state = after
            index += 2
        else:
            state = nxt
            index += 1
    return {'seed': seed, 'sections': index, 'exception_count': len(exceptions),
            'halted_at_outside': False, 'state_a_bits': state.a.bit_length(),
            'state_a_sha256_le': fingerprint(state.a),
            'previous_exceptions': exceptions[-12:], 'labels': dict(labels)}


def main() -> None:
    from check_all_E_second import second_prediction
    from check_root_L_escape import parse_bits
    for k in range(12):
        for q in range(1, 13):
            c = L(3 * k + 4, q, 1)
            derived = second_of_exception(c)
            _, out = second_prediction(k, q)
            actual = parse_bits(out[:])
            if isinstance(derived, Outside):
                assert actual is None, (k, q, derived, actual)
            else:
                assert derived == actual, (k, q, derived, actual)
    print('PASS 144/144 arithmetic second-stage state classifications')
    for seed in (5, 9, 15, 39):
        print(trace(seed))


if __name__ == '__main__':
    main()
