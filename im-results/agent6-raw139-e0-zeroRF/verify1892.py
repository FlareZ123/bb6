"""Exact finite witness for the arbitrary-left-tail pump. No external dependencies.
Bits in each stack are nearest-first; left includes the scanned cell.
Code 24 is undefined; no default transition is permitted.
"""
from collections import deque

TABLE = [7,24,11,17,14,8,3,16,21,11,12,13]
P = "010110011110011110111101111111101111110011110111101111011110111100"
B = "111111001111111101111111101111011110111111111100111100111101111111111111111111100111111111111111111001111000111111111111"
T = "111111001111111101111111101111011110111111111100111100111101111111101111111111111111011111111000111111111111011111111111111111111111111110111111110111111110111111110111111111111111100111101111111111111100111111110111101111001111011110111111111111111100111111001111"

def run(q, l, r, n, guard=False):
    l, r = deque(map(int,l)), deque(map(int,r))
    for t in range(n):
        if guard and not l:
            raise ValueError(("unknown left tail read", t))
        a = l.popleft() if l else 0
        code = TABLE[2*q+a]
        if code == 24:
            raise ValueError(("undefined transition", t, q, a))
        w = (code >> 1) & 1
        if code & 1:
            l.appendleft(w)
            l.appendleft(r.popleft() if r else 0)
        else:
            r.appendleft(w)
        q = code >> 2
    return q, ''.join(map(str,l)), ''.join(map(str,r))

def main():
    assert len(P) == 66 and len(B) == 120
    assert run(0,"","",39854) == (0,P+T,"")
    assert run(0,P,"",16148,True) == (0,P+B,"")
    print("Verified seed and guarded arbitrary-tail pump.")
    print("For all k >= 0, step 39854 + 16148*k reaches (A,P+B^k+T,blank).")

if __name__ == "__main__":
    main()
