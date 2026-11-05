"""Reproduce four-sector vs three-sector filter comparison on Machine C gates.

Independent literal translation of original Agent46 secNext/bounce.
This is finite experimental evidence, subordinate to the source-certified Lean
universal inverse/filter theorems. Never interpret a rejected synthetic gate as
a machine-wide nonhalting proof.
"""


def bounce(k, c):
    while True:
        if c < 4:
            return None
        if k % 2 == 1:
            if c <= 2*k+6:
                return 2*k+6-c, c
            k, c = 2*k+3, c-(2*k+3)
        else:
            if c == 4:
                return 2*k+2, 3
            if c == 5:
                return None
            if c <= 2*k+8:
                return 2*k+8-c, c-1
            k, c = 2*k+4, c-(2*k+5)


def section(a, k):
    if a == 0:
        if k == 0: return None
        if k == 1: return 0, 4
        return bounce(1, 2*k+1)
    if a == 1:
        if k == 0: return 5, 1
        if k == 1: return 2, 3
        if k == 2: return 2, 5
        if k == 3: return 0, 7
        return bounce(4, 2*k-3)
    if k == 0: return a-2, 2
    if 2*k <= a: return a-2*k, 2*k+2
    return bounce(a-1, 2*k-a+3)


def normalize(x, y, four=False):
    path = [(x, y)]
    while True:
        total = x+y
        if x%2 == 1 and y%2 == 1 and y >= 5 and total >= 24 and total%4 == 0 and total%16 != 0:
            nx, ny = (total-4)//2, (x+3*y-10)//4
        elif x%2 == 0 and y%2 == 1 and y >= 5 and total >= 23 and (total+1)%16 == 8:
            nx, ny = (total-5)//2, (x+3*y-9)//4
        elif y >= 4 and y%2 == 0 and (total%4 == 1 or (four and total%4 == 2)):
            nx, ny = total-2, (y-2)//2
        else:
            return (x, y), path
        assert nx+2*ny < x+2*y
        assert section(nx, ny) == (x, y), (x,y,nx,ny)
        x, y = nx, ny
        path.append((x, y))


def forbidden(x, y):
    return y >= 5 and y%2 == 1 and (x+y)%4 in (1,2)


def main():
    extra_first = []
    for m in range(1, 200):
        y = (1 << (2*m+3))-3*m-4
        old, _ = normalize(1,y)
        new, _ = normalize(1,y,True)
        if forbidden(*new) and not forbidden(*old):
            extra_first.append(m)
    extra_high = []
    for m in range(32):
        for j in range(512):
            y = (1 << (2*m+2))*(j+3)-j-3*m-5
            x = 2*j+3
            old, _ = normalize(x,y)
            new, _ = normalize(x,y,True)
            if forbidden(*new) and not forbidden(*old):
                extra_high.append((j,m))
    assert len(extra_first) == 0, extra_first
    assert len(extra_high) == 203, len(extra_high)
    assert (6,0) in extra_high
    print("first-family additional exclusions: 0 of 199 parameters")
    print("second-family additional exclusions: 203 of 16,384 parameter pairs")
    print("each forced reverse edge was checked by an independent literal interpreter")
    print("sample new second-family pairs:",extra_high[:15])


if __name__ == "__main__":
    main()
