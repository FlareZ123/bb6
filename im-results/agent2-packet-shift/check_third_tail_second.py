"""Independent original D TM first two physical section checks.

Physical left blank: every nonzero cell is at or right of head.
Counts are defined primitive steps, with F/1 frozen halt separate.
"""
# Twelve original D-start instructions: write, displacement, next state.
TABLE = (
    ((1, 1, 1), (0, 1, 4)), ((1, -1, 2), (0, 1, 0)),
    ((1, -1, 0), (1, -1, 3)), ((1, -1, 2), (1, -1, 5)),
    ((0, -1, 2), (0, -1, 1)), ((1, -1, 4), None),
)


def first(right, maxsteps=500000):
    tape = {i+1: 1 for i, c in enumerate(right) if c == "1"}
    state, head = 5, 0
    for t in range(1, maxsteps+1):
        action = TABLE[state][int(head in tape)]
        if action is None:
            return ("halt", t-1, "")
        write, delta, state = action
        if write:
            tape[head] = 1
        else:
            tape.pop(head, None)
        head += delta
        if state == 5 and head not in tape and all(p >= head for p in tape):
            last = max(tape, default=head)
            word = "".join("1" if i in tape else "0" for i in range(head+1, last+1))
            return ("return", t, word.rstrip("0"))
    return ("timeout", maxsteps, "")


def expect(k, q):
    assert k >= 0 and q >= 1
    initial = '1' * (3*k+4) + '0' + '10'*q + '11010101010'
    first_time = 12*k*k + 49*k + 76 + 4*q
    first_word = '1'*(8*k+5)+'0'+'1'*(2*q+2)+'0'+'1'*14
    t, k_mod = divmod(k, 3)
    if k_mod == 0:
        second_time = 768*t*t + 584*t + 101
        second_word = '1'*(64*t+19+2*q)+'0'+'1'*14
    elif k_mod == 1:
        second_time = 768*t*t + 968*t + 313
        second_word = '1'*(64*t+33)+'01'*2+'0'+'1'*(2*q-1)+'0'+'1'*14
    else:
        r, q_mod = divmod(q-1, 3)
        if q_mod == 0:
            second_time = 48*r*r + 384*r*t + 638*r + 768*t*t + 2504*t + 2103
            second_word = '1'*(64*t+97+16*r)+'0'+'1'*6
        elif q_mod == 1:
            second_time = 48*r*r + 384*r*t + 494*r + 768*t*t + 1928*t + 1216
            second_word = '1'*(64*t+89+16*r)
        else:
            second_time = 48*r*r + 384*r*t + 494*r + 768*t*t + 1928*t + 1234
            second_word = '1'*(64*t+75+16*r)+'01'*2+'0'+'1'*11
    return (initial, ("return", first_time, first_word), ("return", second_time, second_word))


def main():
    cases=0
    for k in range(15):
        for q in range(1,26):
            word, pred1, pred2 = expect(k,q)
            out1=first(word,maxsteps=pred1[1]+1)
            assert out1==pred1,(k,q, "first",out1,pred1)
            out2=first(out1[2],maxsteps=pred2[1]+1)
            assert out2==pred2,(k,q, "second",out2,pred2)
            cases+=1
    print(f"PASS: {cases} two-first-physical-return samples from independent original raw TM; k 0..14, q 1..25")


if __name__=='__main__': main()
