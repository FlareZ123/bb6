"""Independent exact two-stack simulation; low bit is nearest the head."""
def replay(table, limit):
    q = h = left = right = symbol = 0
    for n in range(limit + 1):
        code = table[2*q+symbol]
        if code == 24:
            return n, 2*q+symbol, h, left, right
        w = (code >> 1) & 1
        if code & 1:
            left, symbol, right = 2*left+w, right&1, right>>1
            h += 1
        else:
            right, symbol, left = 2*right+w, left&1, left>>1
            h -= 1
        q = code >> 2
    raise ValueError("query not reached")
if __name__ == "__main__":
    r = replay([7,17,11,23,14,1,3,16,12,11,24,3], 14876964)
    assert r[:3] == (14876964,10,52), r
    print(r[:3], hex(r[3]), hex(r[4]))
