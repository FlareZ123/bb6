"""Independent original-transition regression for two consecutive E->B F/0 returns."""
import random
from check_new_returns import Source, first_return

def main():
    random.seed(26110442)
    count=0
    for t in range(16):
        k=3*t
        r=8*t+1
        for q in range(11):
            for width in range(6):
                z="".join(random.choices("01",k=width))
                start=Source(5,"","1"*(9*t+4)+"0"+"10"*q+"1101010111"+z)
                e_duration=12*k*k+49*k+80+4*q
                expected_first_right=("1"*(24*t+5)+"0"+"1"*(2*q+6)+"010101010"+z).rstrip("0")
                first=first_return(start,e_duration+2)
                expected_first=("F0",e_duration,expected_first_right)
                assert first==expected_first,(t,q,z,"E",first,expected_first)
                b_duration=12*r*r+49*r+40
                second=first_return(Source(5,"",first[2]),b_duration+2)
                expected_second_right=("1"*(64*t+17+2*q+6)+"010101010"+z).rstrip("0")
                expected_second=("F0",b_duration,expected_second_right)
                assert second==expected_second,(t,q,z,"B",second,expected_second)
                assert e_duration+b_duration==876*t*t+731*t+181+4*q
                count+=1
    print(f"PASS: {count:,} exact two-return E->B section pairs, both strict physical times and tapes")

if __name__=="__main__":
    main()
