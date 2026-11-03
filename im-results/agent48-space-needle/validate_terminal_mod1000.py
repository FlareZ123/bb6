"""Independent exact-integer check of certified Space Needle terminal residues."""
import hashlib


def successor(d: int) -> int | None:
    """Return a single authentic high-level counter successor."""
    x = d + 2
    v = (x & -x).bit_length() - 1
    u = x >> v
    if u == 1:
        return None
    return d + v + 3 * ((u - 1) // 2)


def witness(r: int, bound: int) -> tuple[int, int, int, int]:
    """Build the explicit proof-carrying source for exponent r mod 1000."""
    if r % 2 == 0:
        n = (389 * (r // 2 + 494)) % 500
        k = 12 + 18 * (n + 500 * bound)
        v = 3
        u = ((1 << (k + 1)) - 3) // 19
    else:
        n = (449 * ((r + 331) // 2)) % 500
        k = 3669 + 4098 * (n + 500 * bound)
        v = 11
        u = ((1 << (k + 1)) - 19) // 4099
    assert u >= 3 and u % 2 == 1
    q = (u - 3) // 2
    d = (u << v) - 2
    return k, q, v, d


def main() -> None:
    """Check all residue witnesses for two independently chosen thresholds."""
    lines = []
    for bound in (0, 1):
        for r in range(1000):
            k, q, v, d = witness(r, bound)
            assert k >= bound and k % 1000 == r
            assert (d + 2) & ((1 << v) - 1) == 0
            assert successor(d) == (1 << k) - 2
            assert d < (1 << k) - 2
            lines.append(f"{bound},{r},{k},{v},{q.bit_length()}")
    digest = hashlib.sha256(("\n".join(lines) + "\n").encode()).hexdigest()
    assert digest == "ed010bb6eb25c53394b1d2e500e190336c7e1490fea82ed8c535c88639a1f36a"
    print("Independent exact-bigint verification: 2000 witnessed successors")
    print("Every residue mod 1000, with bounds 0 and 1")
    print("Maximum terminal exponent:", max(int(x.split(",")[2]) for x in lines))
    print("SHA-256 parameter digest:", digest)


if __name__ == "__main__":
    main()
