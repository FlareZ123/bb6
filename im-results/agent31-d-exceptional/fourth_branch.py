"""Two all-v source-derived fourth-return B-obstruction branches of D0.

Finite original-table raw regression for both all-parameter symbolic formulas.
"""
from __future__ import annotations

from check_all_E_second import second_prediction
from check_second_escape import one, pairs, physical_return


def predict(v: int, branch: int, q: int) -> tuple[int, list[int], int, list[int]]:
    assert v >= 0 and branch in (1, 2) and q >= 3
    if branch == 1:
        K3 = 192 * v + 31
        third_n = 1536 * v + 257
        third_s = pairs(4) + [0] + one(2 * q - 6) + [0] + one(6)
        t3 = 12 * K3 * K3 + 49 * K3 + 70
        K4 = 512 * v + 85
        assert third_n == 3 * K4 + 2
        t4 = 12 * K4 * K4 + 49 * K4 + 40
        fourth_n = 4096 * v + 690
        fourth_s = pairs(3) + [0] + one(2 * q - 6) + [0] + one(6)
    else:
        K3 = 192 * v + 53
        third_n = 1536 * v + 434
        third_s = [0, 1, 0] + one(2 * q - 3) + [0] + one(6)
        t3 = 12 * K3 * K3 + 49 * K3 + 40
        K4 = 512 * v + 144
        assert third_n == 3 * K4 + 2
        t4 = 12 * K4 * K4 + 49 * K4 + 40
        fourth_n = 4096 * v + 1162
        fourth_s = [0] + one(2 * q - 3) + [0] + one(6)
    return t3, one(third_n) + third_s, t4, one(fourth_n) + fourth_s


def main() -> None:
    count = 0
    for v in range(2):
        for branch in (1, 2):
            t = 9 * v + branch
            for q in range(3, 6):
                _, second = second_prediction(3 * t + 1, q)
                t3, third = physical_return(second, max_steps=8000000)
                t4, fourth = physical_return(third, max_steps=18000000)
                p3, w3, p4, w4 = predict(v, branch, q)
                assert (t3, third) == (p3, w3), (v, branch, q, 'third')
                assert (t4, fourth) == (p4, w4), (v, branch, q, 'fourth')
                count += 1
    print(f'PASS {count} original literal-TM exact fourth return checks; '
          'v=0..1, branch=1,2, q=3..5')


if __name__ == '__main__':
    main()
