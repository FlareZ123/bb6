"""Independent literal D-start Turing-machine regression for the E->E branch.

Checks both consecutive first *physical* F/0 returns and complete right tapes,
including arbitrary suffix bits. The Lean theorem is all-parameter; this script
is supplementary finite verification.
"""
import random
from check_new_returns import Source, first_return


def main():
    random.seed(20261106)
    count = 0
    for t in range(13):
        for q in range(11):
            for width in range(5):
                y = "".join(random.choices("01", k=width))
                k = 3*t+1
                initial = "1"*(3*k+4) + "0" + "10"*q + "1101010111" + y
                first_time = 12*k*k+49*k+80+4*q
                first_right = (
                    "1"*(8*k+5) + "0" + "1"*(2*q+6) +
                    "010101010" + y
                ).rstrip("0")
                first = first_return(Source(5, "", initial), first_time+1)
                assert first == ("F0", first_time, first_right), (t,q,y,first)

                k2 = 8*t+3
                second_time = 12*k2*k2+49*k2+58
                final = (
                    "1"*(64*t+33) + "01010" + "1"*(2*q+3) +
                    "010101010" + y
                ).rstrip("0")
                second = first_return(Source(5, "", first[2]), second_time+1)
                assert second == ("F0", second_time, final), (t,q,y,second)
                assert first_time+second_time == (
                    876*t*t+1187*t+454+4*q
                )
                count += 1
    print(f"PASS {count} exact two-first-physical-return literal-table E->E regressions")


if __name__ == "__main__":
    main()
