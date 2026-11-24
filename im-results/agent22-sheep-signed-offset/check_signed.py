"""Exact signed-offset classification for Sheep's generic affine families."""

def offset_step(d, B):
    assert d > 0 and d % 2 == 1 and B != 0
    b = (abs(B) & -abs(B)).bit_length() - 1
    v = B >> b
    return B + d*b + (v-d)//2, b


def barrier(d):
    k = 1
    while (1 << k) < 4*d*k:
        k += 1
    return (1 << (2*k)) + 1


def offset_orbit(d, B):
    """Return (status, list of (offset,valuation)) at zero, escape or repeat.

    An escape proves no later zero, but is not a proof of Sheep nonhalting.
    """
    assert d > 0 and d % 2 == 1
    N = barrier(d)
    trace = []
    seen = set()
    while True:
        if not B:
            return 'zero', trace
        if B >= d or B <= -N:
            return 'escape', trace
        if B in seen:
            return 'cycle', trace
        seen.add(B)
        C, b = offset_step(d, B)
        trace.append((B, b))
        B = C


def integral_phase(C, d, B):
    """Return an exponent residue and period, or None if no integral member.

    Repeated multiplication by 2 permutes residues modulo odd d. O(d) time.
    """
    assert d > 0 and d % 2 == 1 and C > 0
    start = C % d
    x, j, first = start, 0, None
    while True:
        if (x+B) % d == 0 and first is None:
            first = j
        x = (2*x) % d
        j += 1
        if x == start:
            return None if first is None else (first, j)


def classify(C, d, B):
    """Classify all sufficiently large integral family members in fixed time.

    Returns (label, time, exponent shift, threshold). For terminal labels,
    all integral exponents j>=threshold hit a power at exactly time;
    shift gives the target exponent j+shift. For 'pure', time is the first
    pure fixed-cofactor state, not a terminal hit. For escape/cycle, no
    uniformly bounded terminal hit occurs along unbounded exponents.
    """
    phase = integral_phase(C, d, B)
    if phase is None:
        return 'empty', None, None, None
    status, trace = offset_orbit(d, B)
    if status != 'zero':
        return status, None, None, None
    c = 0
    jmin = 0
    for offset, b in trace:
        v = offset >> b
        # Ensure b < A and C*2^(A-b)+v >= 5*d, A=j-c.
        m = max(1, (max(1, 5*d-v)-1).bit_length())
        jmin = max(jmin, c+b+m)
        C *= (1 << (b+1)) + 1
        c += b+1
    assert C % d == 0
    Q = C//d
    a = (Q & -Q).bit_length()-1
    jmin = max(jmin, c)
    return ('terminal' if Q >> a == 1 else 'pure', len(trace), a-c, jmin)


def bounded_terminal(C, d, B):
    """Direct O(log d)-step decision of eventual bounded-time power hits.

    Returns (time, exponent shift, threshold) for all sufficiently large
    integral members, or None when no uniformly bounded halt occurs.
    This is not a decision for a particular finite exponent.
    """
    if integral_phase(C, d, B) is None:
        return None
    c = tau = jmin = 0
    while True:
        a = (C & -C).bit_length()-1
        odd = C >> a
        if B == 0:
            return (tau, a-c, max(jmin, c)) if odd == d else None
        if odd >= d or d % odd:
            return None
        Bnew, b = offset_step(d, B)
        v = B >> b
        m = max(1, (max(1, 5*d-v)-1).bit_length())
        jmin = max(jmin, c+b+m)
        C *= (1 << (b+1)) + 1
        c += b+1
        tau += 1
        B = Bnew


def physical(x):
    assert x > 0
    a = (x & -x).bit_length()-1
    u = x >> a
    if u == 1:
        return None
    return x+a+(3 if u == 3 else (u-1)//2)


def check():
    # Exact finite regression tests of lifts and terminal predictions.
    count = 0
    for d in range(1, 42, 2):
        N = barrier(d)
        for b in range(N.bit_length()+3):
            # First two odd multiples of 2^b at or beyond the barrier.
            u = ((N + (1 << b)-1) >> b) | 1
            for v in (u, u+2):
                assert offset_step(d, -(v << b))[0] <= -N
        for C in range(1, 13):
            for B in range(-24, 25):
                phase = integral_phase(C, d, B)
                if phase is None:
                    continue
                status, tau, shift, threshold = classify(C,d,B)
                assert bounded_terminal(C,d,B) == ((tau,shift,threshold) if status == 'terminal' else None)
                if status not in ('terminal','pure'):
                    continue
                j0,p = phase
                j = j0 + p*max(0,(max(100,threshold)-j0+p-1)//p)
                x = (C*(1 << j)+B)//d
                for _ in range(tau):
                    x = physical(x)
                    assert x is not None
                if status == 'terminal':
                    assert x == (1 << (j+shift)) and physical(x) is None
                else:
                    assert physical(x) is not None
                count += 1
    print('validated zero-family predictions:', count)
    for C,d,B in [(4,5,-2),(2,3,1),(28,5,-2),(1,1,-1),(1,1,1),(1,3,1),(1,9,-2)]:
        print((C,d,B),classify(C,d,B),offset_orbit(d,B))


if __name__ == '__main__':
    check()
