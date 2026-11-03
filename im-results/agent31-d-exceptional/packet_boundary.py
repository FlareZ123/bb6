"""Exact physical F0 returns at low-p E boundary of D packet grammar.

p=2 prediction uses locally Lean-verified all-q E110111Pairs and is awaiting
original-source import; a finite original-machine regression is provided here.
"""
from __future__ import annotations
from check_second_escape import one, pairs, physical_return
from check_root_L_escape import parse_bits


def E_predict(k: int,q: int,p: int) -> tuple[int,list[int],str]:
    if p == 0:
        return 12*k*k+49*k+50+4*q,one(8*k+5)+[0]+one(2*q+12),'E0_L'
    if p == 1:
        return 12*k*k+49*k+64+6*q,one(8*k+9)+pairs(q+4)+one(2),'E1_L'
    if p == 2:
        return 12*k*k+49*k+68+4*q,one(8*k+5)+[0]+one(2*q+6)+[0,1,0,1,0]+one(3),'E2_N'
    raise ValueError(p)


def main() -> None:
    successes = 0
    for k in range(12):
        for q in range(11):
            for p in range(3):
                T,out = physical_return(one(3*k+4)+pairs(q)+[0]+one(p)+[0]+one(6),max_steps=200000)
                pred,word,label = E_predict(k,q,p)
                assert (T,out) == (pred,word), (k,q,p,label,T,pred)
                assert (parse_bits(out[:]) is not None) == (p<2), (k,q,p,label)
                successes += 1
    print(f'PASS {successes} exact original-table E low-p F0 returns (k=0..11,q=0..10,p=0..2)')


if __name__ == '__main__':
    main()
