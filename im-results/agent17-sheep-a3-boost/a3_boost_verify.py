"""Exact certificate for a=3 Sheep first-even parents at j=2*3**k.

Pure Python 3, exact modular arithmetic and literal section transitions.
"""
from hashlib import sha256


def modular_q(j: int, h: int, prime: int = 17) -> int:
    m = prime * 3**h
    r = (pow(2, j, m) - 1) % m
    assert r % 3**h == 0
    return r // 3**h


def expected_h(k: int) -> set[int]:
    residue = 10 if k % 2 == 0 else 14
    return {h for h in range(1, k + 2) if h % 16 == residue}


def source_check(k: int, h: int) -> bytes:
    j = 2 * 3**k
    power = 1 << j
    divisor = 3**h
    q, remainder = divmod(power - 1, divisor)
    assert remainder == 0 and q >= 7 and q % 2 == 1
    numerator = (1 << (h + 1)) * q - 3
    u, r = divmod(numerator, 17)
    assert r == 0 and u >= 5 and u % 2 == 1
    x = 8 * u
    f = x + 3 + (u - 1)//2
    t = f - 1
    v2 = (t & -t).bit_length() - 1
    assert v2 == h
    e = 1 + 3**h * (t >> h)
    assert e == power
    return sha256(x.to_bytes((x.bit_length()+7)//8, 'big')).digest()


def run() -> None:
    c = sha256()
    source_count = 0
    modular_count = 0
    first = {}
    for k in range(1, 129):
        j = 2 * 3**k
        actual = set()
        for h in range(1, k + 2):
            q17 = modular_q(j, h)
            if ((pow(2, h + 1, 17) * q17) - 3) % 17 == 0:
                actual.add(h)
            modular_count += 1
        predicted = expected_h(k)
        assert actual == predicted, (k, sorted(actual), sorted(predicted))
        if k <= 13:
            for h in sorted(actual):
                c.update(source_check(k, h))
                source_count += 1
        if k in {10, 13, 24, 50, 100, 128}:
            first[k] = (len(predicted), sorted(predicted))
    print('PASS: all k=1..128: complete a=3 mod-17 h classification')
    print(f'PASS: {modular_count} modular hidden-block tests; {source_count} full exact F/E parent checks')
    print('Sample (k: (a3 parent count, h list)):', first)
    print('Source checksum SHA256:', c.hexdigest())


if __name__ == '__main__':
    run()
