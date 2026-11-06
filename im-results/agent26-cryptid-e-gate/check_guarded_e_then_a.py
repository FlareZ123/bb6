"""Independent primitive machine checks of two guarded E-to-A first-return sectors."""
import random
from check_new_returns import Source, first_return


def main():
    random.seed(20261106)
    count = 0
    for t in range(8):
        for u in range(8):
            for width in range(5):
                y = "".join(random.choices("01", k=width))
                ke = 3*t+2
                for mod in (1, 2):
                    q = 3*u+mod
                    initial = "1"*(3*ke+4)+"0"+"10"*q+"1101010111"+"0"+y
                    e_time = 12*ke*ke+49*ke+80+4*q
                    middle = ("1"*(8*ke+5)+"0"+"1"*(2*q+6)+"010101010"+"0"+y).rstrip("0")
                    actual_e = first_return(Source(5, "", initial), e_time+2)
                    assert actual_e == ("F0", e_time, middle), (t,u,mod,y,actual_e)
                    if mod == 1:
                        total = 876*t*t+384*t*u+2219*t+48*u*u+506*u+1472
                        output = "1"*(64*t+16*u+71)+"0"+"1"*14+y
                    else:
                        total = 876*t*t+384*t*u+2411*t+48*u*u+554*u+1729
                        output = "1"*(64*t+16*u+93)+y
                    actual_a = first_return(Source(5, "", actual_e[2]), total-e_time+2)
                    assert actual_a == ("F0", total-e_time, output.rstrip("0")), (t,u,mod,y,actual_a)
                    count += 1
    print(f"PASS: {count} exact guarded E-to-A two first-physical-return original-table regressions")


if __name__ == "__main__":
    main()
