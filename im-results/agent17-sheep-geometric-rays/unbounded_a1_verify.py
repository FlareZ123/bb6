"""Audit an infinite explicit source family for Sheep halting-power gates."""
from power_inverse_general import h_max, parent_signatures


def check() -> None:
    for j in range(6, 20001, 2):
        got = [h for h, a in parent_signatures(j) if a == 1]
        expected = ([h for h in range(1, h_max(j)+1, 2)]
                    if j % 4 == 2 else [])
        assert got == expected, (j, got, expected)
    print("a=1 branch iff condition PASS on 9998 even exponents 6..20000")

    for k in range(1, 41):
        j = 2 * 3**k
        h_values = [h for h,a in parent_signatures(j) if a == 1]
        expected = list(range(1, k+2, 2))
        assert h_values == expected, (k,h_values,expected)
        if k in (1,2,3,5,10,20,30,40):
            print(f"k={k}, j=2*3^{k}, distinct a1 parents={len(h_values)}")
    print("Unbounded-family signature identities PASS for k=1..40")

if __name__ == "__main__":
    check()
