"""Finite raw-machine checks of new *conjectural* Cryptid macro identities.

These tests provide empirical falsification checks; they are not proof for all
k,q,r,suffixes and cannot certify any blank-orbit infinite property.
"""
M = {
    "A": ((1, 1, "B"), (0, 1, "E")),
    "B": ((1, -1, "C"), (0, 1, "A")),
    "C": ((1, -1, "A"), (1, -1, "D")),
    "D": ((1, -1, "C"), (1, -1, "F")),
    "E": ((0, -1, "C"), (0, -1, "B")),
    "F": ((1, -1, "E"), None),
}

def raw_run(n: int, suffix: str, steps: int) -> str:
    """Run the exact original 12-instruction Turing machine from I_n(suffix)."""
    tape = {i+1: 1 for i in range(n)}
    for i, b in enumerate(suffix, n+1):
        if b == "1":
            tape[i] = 1
    pos, state = 0, "F"
    for _ in range(steps):
        action = M[state][tape.get(pos, 0)]
        assert action is not None, "HALT before expected F-section return"
        write, direction, state = action
        if write:
            tape[pos] = 1
        else:
            tape.pop(pos, None)
        pos += direction
    assert state == "F" and tape.get(pos, 0) == 0
    assert not any(i <= pos for i in tape)
    return "".join(
        str(tape.get(pos+j, 0))
        for j in range(1, max(tape.keys(), default=pos)-pos+1)
    ).rstrip("0")

def check() -> None:
    tails = ("", "0", "1010", "111011")
    count = 0
    for kind in (1, 2):
        for k in range(6):
            for q in range(6):
                for r in range(6):
                    for ys in tails:
                        suffix = "0" + "10"*q + "1"*(3*r+kind) + "00" + ys
                        base = (12*k*k + 49*k + 4*q + 12*r*r
                                + (24*k+55+6*q)*r)
                        if kind == 1:
                            steps = base+48
                            n_out = 8*k+13+2*q+8*r
                            out = ys
                        else:
                            steps = base+54
                            n_out = 8*k+7+2*q+8*r
                            out = "0" + "1"*6 + ys
                        actual = raw_run(3*k+3, suffix, steps)
                        assert actual == ("1"*n_out+out).rstrip("0"), (kind,k,q,r,ys)
                        count += 1
    assert count == 1728
    print("A 3r+1 / 3r+2: 1,728 finite raw tests PASS")
    count = 0
    for k in range(6):
        for q in range(1, 7):
            for ys in ("", "0", "1", "1010", "0111", "1110101"):
                suffix = "0" + "10"*q + "1100" + ys
                steps = 12*k*k + 49*k + 60 + 4*q
                n_out = 8*k+5
                out = "0" + "1"*(2*q+2) + "0" + "1"*6 + ys
                actual = raw_run(3*k+4, suffix, steps)
                assert actual == ("1"*n_out+out).rstrip("0"), (k,q,ys)
                count += 1
    assert count == 216
    print("E 1100 after q>=1: 216 finite raw tests PASS")

if __name__ == "__main__":
    check()
