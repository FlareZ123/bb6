from collections import Counter

def walk(root, maxband):
    j = 0
    p = 5
    x = 5 if root == 1 else root
    q = 2*(x-(p-j-3))+j+6
    crossings = Counter()
    exceptional = []
    negative = []
    while j <= maxband:
        n = 0
        w = 4*p-2*q-3
        while 3*q <= 2*p+j+2:
            q *= 3
            n += 1
        if q == 2*p+j:
            return ("halt", j, root, crossings, exceptional, negative)
        if q == 2*p+j+2:
            jj, qq, kind = j+1, 3*j+15, "special"
        elif 3*q <= 6*p+j:
            jj, qq, kind = j+1, 3*q-2*p+3, "one"
        else:
            jj, qq, kind = j+2, 3*q-6*p+6, "skip"
        if w < 0 or 4*p-2*q-3 < 0:
            negative.append(j)
        crossings[(kind,n)] += 1
        if kind != "one":
            exceptional.append((j,kind,n))
        p <<= jj-j
        j,q = jj,qq
    return ("not halted", j, root, crossings, exceptional, negative)

if __name__ == "__main__":
    import sys
    maxband = int(sys.argv[1]) if len(sys.argv)>1 else 100000
    for root in (1,2,3):
        print(walk(root,maxband),flush=True)
