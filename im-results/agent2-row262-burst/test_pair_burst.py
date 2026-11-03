"""SFT: source RLE raw-step verification of Row262's universal 9q burst theorem.

Checks every original primitive transition, head position, physical tape, and
intermediate A checkpoint. This is finite regression, not a global orbit decision.
"""
from random import Random

RLE = "1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---"
TABLE = {}
for state, block in zip("ABCDEF", RLE.split("_"), strict=True):
    for bit in (0, 1):
        code = block[3*bit:3*bit+3]
        if code != "---":
            TABLE[state, bit] = (int(code[0]), 1 if code[1] == "R" else -1, code[2])
assert len(TABLE) == 11


def physical(left, head, right, position=0):
    occupied = {position-(j+1) for j,b in enumerate(left) if b}
    if head: occupied.add(position)
    occupied.update(position+(j+1) for j,b in enumerate(right) if b)
    return occupied


def step(state, position, occupied):
    write, shift, nxt = TABLE[state, int(position in occupied)]
    if write: occupied.add(position)
    else: occupied.discard(position)
    return nxt, position+shift


def test():
    rng=Random(0x62622026)
    tests=0
    transitions=0
    maxq=27
    for q in range(maxq+1):
        for attempt in range(96):
            left=[rng.randrange(2) for _ in range(rng.randrange(20))]
            suffix=[rng.randrange(2) for _ in range(rng.randrange(25))]
            right=[1,0]+[z for _ in range(q) for z in (0,0,1)]+suffix
            tape=physical(left, 0, right)
            state, pos='A',0
            for t in range(1,9*q+1):
                state,pos=step(state,pos,tape)
                assert (state,int(pos in tape)) in TABLE, ('unexpected halt',q,t)
                if t%9==5:
                    assert state=='A' and pos==3*(t//9)+5 and pos in tape
                if t%9==0:
                    assert state=='A' and pos==3*(t//9) and pos not in tape
            expected=physical(([0,1,1]*q)+left, 0, [1,0]+suffix, 3*q)
            assert (state,pos,tape)==('A',3*q,expected), (q,attempt)
            tests+=1
            transitions+=9*q
    print(f'PASS {tests} arbitrarily sided finite tapes, {transitions} source-rle primitive transitions; q=0..{maxq}; each pair has A checkpoints at 5,9 steps')


if __name__=='__main__':
    test()
