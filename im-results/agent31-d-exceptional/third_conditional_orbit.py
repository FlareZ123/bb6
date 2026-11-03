"""Three-return completion for the k=3t+1, q>=3 E exceptional family.

Source-derived endpoint families; no asserted global blank-root induction.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass

from check_second_escape import pairs, one, physical_return
from check_root_L_escape import L, next_source_macro, parse_bits
from extended_conditional_orbit import Outside, second_of_exception, fingerprint
from check_all_E_second import second_prediction


@dataclass(frozen=True)
class NewPacket:
    tag: str
    unary: int
    q: int
    suffix: str


def third_outcome(out: Outside) -> L | NewPacket:
    k, q = out.k, out.q
    assert k % 3 == 1 and q >= 3
    t = (k - 1) // 3
    u, s = divmod(t, 3)
    if s == 0:
        K = 64 * u + 10
        a, r = divmod(q, 3)
        if r == 0:
            return L(8 * K + 13 + 16 * a)
        if r == 1:
            return L(8 * K + 7 + 16 * a, 3, 2)
        return L(8 * K + 33 + 16 * a)
    if s == 1:
        K = 64 * u + 31
        return NewPacket('Etriple2', 8 * K + 9, q, '(01)^4 0 1^(2q-6) 0 1^6')
    K = 64 * u + 53
    return NewPacket('B', 8 * K + 10, q, '0 1 0 1^(2q-3) 0 1^6')


def test_short() -> None:
    count = 0
    for t in range(10):
        for q in range(3, 13):
            out = Outside(3 * t + 1, q, 64 * t + 33)
            _, second = second_prediction(3 * t + 1, q)
            _, third = physical_return(second, max_steps=1000000)
            predicted = third_outcome(out)
            if isinstance(predicted, L):
                assert parse_bits(third.copy()) == predicted, (t, q, predicted)
            else:
                suffix = (pairs(4) + [0] + one(2 * q - 6) + [0] + one(6)
                          if predicted.tag == 'Etriple2'
                          else [0, 1, 0] + one(2 * q - 3) + [0] + one(6))
                assert third == one(predicted.unary) + suffix, (t, q, predicted)
            count += 1
    print('PASS', count, 'exact third physical F0 sections (t=0..9,q=3..12)')


def trace(seed: int, max_sections: int = 180000) -> dict:
    c = L(seed)
    index = 0
    exceptions = []
    while index < max_sections:
        nxt, _ = next_source_macro(c)
        if nxt is not None:
            c = nxt
            index += 1
            continue
        second = second_of_exception(c)
        if isinstance(second, Outside):
            third = third_outcome(second)
            if isinstance(third, NewPacket):
                return {'seed': seed, 'failed_section': index,
                        'failed_k_mod9': second.k % 9, 'q': second.q,
                        'first_nonL_at': index + 1,
                        'after_three': third.tag,
                        'input_a_bit_length': c.a.bit_length(),
                        'input_a_mod81': c.a % 81,
                        'input_a_sha256_le': fingerprint(c.a),
                        'preceding_exceptions': exceptions[-12:]}
            exceptions.append({'section': index, 'k_mod9': second.k % 9,
                               'q': second.q, 'type': 'three-return',
                               'a_bits': c.a.bit_length()})
            c = third
            index += 3
            continue
        exceptions.append({'section': index, 'k_mod9': (c.a - 4) // 3 % 9,
                           'q': c.q, 'type': 'two-return',
                           'a_bits': c.a.bit_length()})
        c = second
        index += 2
    return {'seed': seed, 'limit': max_sections,
            'exception_count': len(exceptions)}


def main() -> None:
    test_short()
    for seed in (5, 9, 15, 39):
        print(trace(seed))


if __name__ == '__main__':
    main()
