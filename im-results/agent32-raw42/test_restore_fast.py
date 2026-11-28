#!/usr/bin/env python3
"""Round-trip the actual generated Run modules from an assembly artifact."""
from pathlib import Path
import sys
from restore_fast import restore_fast
from minimize_bidfa import parse, minimize
from convert_bidfa import convert

count = 0
for root in map(Path, sys.argv[1:]):
    for p in sorted(root.glob('*Run*.lean')):
        source = p.read_text()
        if 'def cert : FastCert :=' not in source:
            continue
        a = parse(restore_fast(source))
        b = parse(restore_fast(convert(restore_fast(source))))
        assert a[1:3] == b[1:3]
        assert all(set(x) == set(y) for x, y in zip(a[3:], b[3:])), p
        reduced, before, after = minimize(source)
        assert all(x >= y for x, y in zip(before, after)), p
        assert 'def cert : FastCert :=' in convert(reduced)
        count += 1
        print(p.name, before, '->', after)
assert count > 0, 'no FastCert fixture exercised'
print('exact actual FastCert round-trips:', count)
