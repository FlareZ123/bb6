"""Independent original literal-machine first-return check for E then coded A."""
import random
from check_new_returns import Source, first_return

def main():
    random.seed(202611043)
    count=0
    for t in range(8):
        for u in range(9):
            for width in range(6):
                z="".join(random.choices("01",k=width))
                ke=3*t+2
                qe=3*u
                ka=8*t+6
                r=2*u+2
                m=4*ka+3
                e_duration=12*ke*ke+49*ke+80+4*qe
                a_duration=(12*ka*ka+41*ka+32+
                    r*(6*m+41)+12*r*(r-1)+2*(m+4*r)+6)
                initial=Source(5,"","1"*(9*t+10)+"0"+"10"*qe+"1101010111"+z)
                e=first_return(initial,e_duration+2)
                first_right=("1"*(24*t+21)+"0"+"1"*(6*u+6)+"010101010"+z).rstrip("0")
                assert e==("F0",e_duration,first_right),(t,u,z,"E",e,first_right)
                a=first_return(Source(5,"",e[2]),a_duration+2)
                second_right=("1"*(64*t+16*u+75)+"10101010"+z).rstrip("0")
                assert a==("F0",a_duration,second_right),(t,u,z,"A",a,second_right)
                assert e_duration+a_duration==(
                    876*t*t+384*t*u+2219*t+48*u*u+506*u+1442)
                count+=1
    print(f"PASS: {count:,} exact consecutive E->A first physical return pairs, including complete physical tape")
if __name__=="__main__":
    main()
