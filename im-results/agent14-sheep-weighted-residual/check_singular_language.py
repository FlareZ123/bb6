"""Check the finite periods of the exact prepared-state terminal language."""
from math import lcm

ALLOWED = (5,17,24,37,40,65)
TABLE = (
    (71,11,131), (17,137,77), (22,82,142),
    (47,167,107), (34,94,154), (161,101,41),
)

def type1(h):
    if h == 1:
        return 16
    if h == 2:
        return 50
    return next(q for q in range(2,55,2) if (16*pow(2,h,27)*q-5)%27==0)

def type2(h):
    d = 2*3**(h-1)
    a = (1+19*pow(7,h,11))%11
    b = (1+19*pow(10,h,17))%17
    return [q for q in range(1,181)
            if (7*pow(2,h,9)*q-19)%9==0
            and pow(2,d*q,11)==a and pow(2,d*q,17)==b]

def check_congruence(h,q,d,c):
    b = 2*3**(h-1)*q
    m = c*3**h
    assert (pow(2,h,m)*(pow(2,b,m)-1)-d*3**h)%m == 0

def main():
    assert lcm(6,4,2,10,16)==240
    for h in range(1,21):
        q=type1(h)
        check_congruence(h,q,5,135)
        check_congruence(h,q+54,5,135)
        if h>=3:
            assert q==type1(h+18)
    for h in range(5,245):
        qs=type2(h)
        assert len(qs)==int(h%80 in ALLOWED)
        assert qs==type2(h+240)
        if qs:
            q=qs[0]
            assert q==TABLE[ALLOWED.index(h%80)][(h%240)//80]
            check_congruence(h,q,19,1683)
            check_congruence(h,q+180,19,1683)
    for h in range(1,5):
        assert not type2(h)
    print("Finite period and congruence checks passed.")

if __name__=="__main__":
    main()
