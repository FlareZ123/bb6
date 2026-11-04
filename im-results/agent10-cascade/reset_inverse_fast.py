"""Fast exact reset-to-reset inverse for #746's source-indexed C episode map.

The reset map R(h) is the first subsequent (u,0) reached after (h,0), or
None if the run instead halts. `predecessor_heights(u)` enumerates exactly
all h with R(h)=u, without intermediate sweep states.

This is a mathematical/source-copy model. The upstream Cryptids source
bridge and formal correctness of this Python inverse require separate audit.
"""


def reset_return(h: int) -> int | None:
    p, k = 1, 0
    while h + k + 5 >= 8 * p:
        p, k = 2 * p, k + 1
    if h + k + 4 == 4 * p:
        return None
    a = 4 * p + (h + k) // 2
    if (h + k) % 2 == 0:
        return a
    q = a + 3
    while q % 2 == 0:
        q = 3 * q // 2
    return (3 * q - 5) // 2


def predecessor_heights(u: int) -> list[int]:
    """All h>=0 whose first subsequent reset has height u, exactly."""
    out: list[int] = []
    if u >= 5:
        k = ((u + 1) // 6).bit_length() - 1
        p = 1 << k
        if u <= 8 * p - 3:
            out.append(2 * u - 8 * p - k)
    z = 2 * u + 5
    t = 0
    while z % 3 == 0:
        z //= 3
        q = z << t
        if q == 7:
            out.append(1)
        if q >= 13:
            k = ((q - 1) // 6).bit_length() - 1
            p = 1 << k
            if k >= 1 and q <= 8 * p - 1:
                out.append(2 * q - 8 * p - k - 5)
        t += 1
    return sorted(set(out))


def compute_reverse(target: int, max_nodes: int | None = None) -> tuple[int, int, bool, bool]:
    seen = {target}
    todo = [target]
    edges = 0
    while todo:
        x = todo.pop()
        for h in predecessor_heights(x):
            assert h < x
            edges += 1
            if h not in seen:
                seen.add(h)
                todo.append(h)
        if max_nodes is not None and len(seen) > max_nodes:
            return len(seen), edges, False, 2 in seen
    return len(seen), edges, True, 2 in seen


def self_test() -> None:
    from random import Random
    for h in range(100000):
        u = reset_return(h)
        if u is not None:
            assert h in predecessor_heights(u), (h, u)
    forward = {h: reset_return(h) for h in range(500)}
    for u in range(10000):
        expected = {h for h, v in forward.items() if v == u}
        actual = {h for h in predecessor_heights(u) if h < 500}
        assert expected == actual, (u, expected, actual)
    rng = Random(74620261104)
    for bits in (32, 64, 256, 1024, 8192):
        for _ in range(500):
            h = rng.getrandbits(bits)
            u = reset_return(h)
            if u is not None:
                assert h in predecessor_heights(u)
                assert all(reset_return(p) == u for p in predecessor_heights(u))
    print('PASS: forward h<100000; inverse u<10000, h<500; 2500 randomized round trips')


def audit(start: int = 257, end: int = 2048) -> None:
    import hashlib
    digest = hashlib.sha256()
    count = 0
    total = 0
    largest = (0, 0)
    for n in range(start, end + 1):
        if n % 6 not in (4, 5):
            continue
        u = 4 * (1 << n) - n - 4
        nodes, edges, complete, root_seen = compute_reverse(u)
        assert complete and not root_seen, (n, nodes, edges)
        digest.update(f'{n}:{nodes}:{edges}:0\n'.encode())
        count += 1
        total += nodes
        if nodes > largest[1]:
            largest = (n, nodes)
    print(f'PASS: {count} candidate indices n={start}..{end}, no root; '
          f'total_nodes={total}, largest={largest}, SHA256={digest.hexdigest()}')


if __name__ == '__main__':
    self_test()
    audit()
