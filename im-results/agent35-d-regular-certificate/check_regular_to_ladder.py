"""Literal original six-state F/0 test of the first regular-to-ladder case."""
from primitive import run_word

k, q = 40, 6
t = (k - 1) // 3
u = (t - 1) // 3
cost1 = 12*k*k + 49*k + 56 + 4*q
K1 = 8*t + 3
cost2 = 12*K1*K1 + 49*K1 + 58
K2 = 64*u + 31
cost3 = 12*K2*K2 + 49*K2 + 58 + 12
K3 = 767
cost4 = 12*K3*K3 + 49*K3 + 58 + 24
start_a = 3*k + 4
start_word = [0, 1]*q + [1]

for j, elapsed, expected in [
    (1, cost1, [1]*(8*k+5)+[0]+[1]*(2*q)+[0]+[1]*6),
    (2, cost1+cost2, [1]*(64*t+33)+[0, 1]*2+[0]+[1]*(2*q-3)+[0]+[1]*6),
    (3, cost1+cost2+cost3, [1]*(512*u+257)+[0, 1]*4+[0]+[1]*(2*q-6)+[0]+[1]*6),
    (4, cost1+cost2+cost3+cost4, [1]*6145+[0, 1]*6+[0]+[1]*3+[0]+[1]*6),
]:
    actual = run_word(start_a, start_word, elapsed)
    assert actual == expected, (j, len(actual), len(expected))
    print("PASS original regular E-origin macro", j, "elapsed", elapsed, flush=True)

print("ALL PASS")
