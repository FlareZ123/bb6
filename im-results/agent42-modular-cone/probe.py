from functools import lru_cache

def canon(b, x, y):
    p = 1 << b
    return x % p, y % p

def bad(x, y):
    return y % 2 == 1 and (x + y) % 4 in (1, 2)

@lru_cache(maxsize=1_000_000)
def check(fuel, bits, x, y):
    """Mirror ModularCone.check(fuel,bits,residue bits).

    Each inverse edge consumes one unit of recursion fuel. A direct edge
    consumes one modulus bit; a high edge consumes n+2 modulus bits.
    """
    x, y = canon(bits, x, y)
    if fuel == 0:
        return bits >= 2 and bad(x, y)
    if bits < 2:
        return False
    if bad(x, y):
        return True

    s = x + y
    odd = s % 2
    q = s + odd
    if q == 0:
        return False
    v = (q & -q).bit_length() - 1
    if v + 1 > bits:
        return False

    if y % 2 == 0:
        child_bits = max(0, bits - 1)
        child = canon(child_bits, s - 2, (y - 2) // 2)
        if not check(fuel - 1, child_bits, *child):
            return False

    for n in range((x + 1 + odd) % 2, v - 1, 2):
        d = 1 << (n + 1)
        a = q // d - 2 - odd
        numerator = x + 2 * y - a - 7 - 3 * n
        if d * (a + 2 + odd) != q or numerator % 2:
            return False
        k = numerator // 2
        if 2 * k + a + 7 + 3 * n != x + 2 * y:
            return False
        child_bits = max(0, bits - n - 2)
        child = canon(child_bits, a, k)
        if not check(fuel - 1, child_bits, *child):
            return False
    return True

def excluded(bits, x, y):
    return check(bits, bits, *canon(bits, x, y))

def stop(j, m, bits):
    return excluded(bits, 2*j+1, -j-3*m-4)

def stop_bits(j, m, cap=32):
    # One extra bit is available for the unified high family j>=2.
    return min(cap, 2*m+(2 if j>=2 else 1))

def stop_auto(j, m, cap=32):
    return stop(j, m, stop_bits(j, m, cap))

def stop8(j, m):
    return stop(j, m, 8)

def depth_check(fuel, bits, x, y, memo):
    """Return (accepted, maximum recursive parent depth)."""
    x, y = canon(bits, x, y)
    key = (fuel, bits, x, y)
    if key in memo:
        return memo[key]
    if fuel == 0:
        out = (bits >= 2 and bad(x, y), 0)
        memo[key] = out
        return out
    if bits < 2:
        out = (False, 0)
        memo[key] = out
        return out
    if bad(x, y):
        out = (True, 0)
        memo[key] = out
        return out

    s = x + y
    odd = s % 2
    q = s + odd
    if q == 0:
        out = (False, 0)
        memo[key] = out
        return out
    v = (q & -q).bit_length() - 1
    if v + 1 > bits:
        out = (False, 0)
        memo[key] = out
        return out

    depth = 0
    if y % 2 == 0:
        child_bits = max(0, bits - 1)
        child = canon(child_bits, s - 2, (y - 2) // 2)
        ok, child_depth = depth_check(fuel - 1, child_bits, *child, memo)
        if not ok:
            out = (False, 0)
            memo[key] = out
            return out
        depth = max(depth, child_depth + 1)

    for n in range((x + 1 + odd) % 2, v - 1, 2):
        d = 1 << (n + 1)
        a = q // d - 2 - odd
        numerator = x + 2 * y - a - 7 - 3 * n
        if d * (a + 2 + odd) != q or numerator % 2:
            out = (False, 0)
            memo[key] = out
            return out
        k = numerator // 2
        if 2 * k + a + 7 + 3 * n != x + 2 * y:
            out = (False, 0)
            memo[key] = out
            return out
        child_bits = max(0, bits - n - 2)
        child = canon(child_bits, a, k)
        ok, child_depth = depth_check(fuel - 1, child_bits, *child, memo)
        if not ok:
            out = (False, 0)
            memo[key] = out
            return out
        depth = max(depth, child_depth + 1)

    out = (True, depth)
    memo[key] = out
    return out

if __name__ == "__main__":
    print("cap | low m=0..1023 | old high | adaptive high | adaptive outside unified j>3m+1")
    hi = [(j, m) for j in range(1, 128) for m in range(1, 128)]
    out = [(j, m) for j, m in hi if j > 3*m+1]
    for cap in [4, 8, 12, 16, 24, 32]:
        low = sum(stop(0, m, min(2*m+1, cap)) for m in range(1024))
        old_high = sum(stop(j, m, min(2*m+1, cap)) for j, m in hi)
        high = sum(stop_auto(j, m, cap) for j, m in hi)
        outside = sum(stop_auto(j, m, cap) for j, m in out)
        print(cap, low, 1024, old_high, len(hi), high, len(hi), outside, len(out))

    unresolved = [m for m in range(100) if not stop_auto(0, m, 32)]
    print("adaptive low unresolved m<100:", unresolved)

    high8 = sum(stop8(j, m) for j in range(256) for m in range(256))
    high8_immediate = sum(
        bad(*canon(8, 2*j+1, -j-3*m-4))
        for j in range(256) for m in range(256)
    )
    low8 = sum(stop8(0, m) for m in range(256))
    low8_immediate = sum(
        bad(*canon(8, 1, -3*m-4))
        for m in range(256)
    )
    print("fixed b=8 high accepted/immediate/deeper:", high8, high8_immediate, high8-high8_immediate, "/", 256*256)
    print("fixed b=8 low accepted/immediate/deeper:", low8, low8_immediate, low8-low8_immediate, "/", 256)

    high_hist, low_hist = {}, {}
    memo = {}
    for j in range(256):
        for m in range(256):
            ok, depth = depth_check(8, 8, 2*j+1, -j-3*m-4, memo)
            if ok:
                high_hist[depth] = high_hist.get(depth, 0) + 1
    for m in range(256):
        ok, depth = depth_check(8, 8, 1, -3*m-4, memo)
        if ok:
            low_hist[depth] = low_hist.get(depth, 0) + 1
    print("fixed b=8 high max-depth histogram:", dict(sorted(high_hist.items())))
    print("fixed b=8 low max-depth histogram:", dict(sorted(low_hist.items())))

    original_hi = [(j, m) for j in range(1, 128) for m in range(1, 128)]
    original_out = [(j, m) for j, m in original_hi if j >= 3*m+1]
    original_total = sum(stop_auto(j+1, m, 32) for j, m in original_hi)
    original_outside = sum(stop_auto(j+1, m, 32) for j, m in original_out)
    print("original high index j=1..127 (unified J=j+1):",
          original_total, len(original_hi), "outside old j<=3m gate:",
          original_outside, len(original_out))
    print("cache:", check.cache_info())
