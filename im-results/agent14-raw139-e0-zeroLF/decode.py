"""Decode compact reproducible discovery records; all witnesses remain untrusted."""
import base64, hashlib, struct, zlib
from pathlib import Path

def decode(path):
    raw = zlib.decompress(base64.b64decode(Path(path).read_bytes()))
    assert hashlib.sha256(raw).hexdigest() == '6a8e0dc217b60d744754451eeaa17929556baf1c17a9201e82f1c682b420a861'
    assert raw[:4] == b'ZLF1'
    pos = 4
    def take(fmt):
        nonlocal pos
        v = struct.unpack_from('<'+fmt, raw, pos)
        pos += struct.calcsize('<'+fmt)
        return v
    n, = take('B')
    params = [take('6B') for _ in range(n)]
    tags = take('12646B')
    base = {}
    for i, tag in enumerate(tags):
        if tag < n:
            base[i] = ('block', params[tag])
        elif tag == 253:
            base[i] = ('open',)
        elif tag in (254, 255):
            base[i] = ('late' if tag == 254 else 'split', *take('HB'))
        else:
            raise ValueError((i, tag))
    n_ext, = take('H')
    ext = {}
    for _ in range(n_ext):
        i, tag = take('HB')
        if tag == 0:
            ext[i] = ('cycle', *take('HHBh'))
        elif tag == 1:
            ext[i] = ('hole', *take('HB'))
        elif tag == 2:
            r, d = take('BB')
            ext[i] = ('far', r, take(f'{2*d}B'))
        elif tag == 3:
            ext[i] = ('open',)
        else:
            raise ValueError((i, tag))
    n_hard, = take('H')
    hard = {}
    for _ in range(n_hard):
        i, tag = take('HB')
        hard[i] = ('open',) if tag == 255 else ('block', params[tag])
    assert pos == len(raw)
    assert n_ext == 393 and n_hard == 156
    return base, ext, hard
