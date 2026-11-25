# Raw39 A1=1LB: six binary-width growth certificates

Status: exact symbolic candidates, original Lean source audit pending.

For the six literal partial tables in gen_lb_width_counters.py, let A=10, Z=00, and let Q(R) have state A, left frame 00 (000 for 5157/5794), and right frame 0000 followed by R. Blank entry into Q(1) takes t=22 (24 for 5157/5794).

The exact candidate local laws, checked by an arbitrary-tail symbolic sweep recognizer, are:

* Q(A^n Z R) -> Q(Z^n A R), in t+8n steps for arbitrary R.
* Q(A^n 1) -> Q(Z^(n+1) 1), in t+8+8n steps.

The existing Raw39CounterCarry.fill induction composes all increments without executing the exponentially large number of primitive steps. Therefore family(n)=Q(Z^n 1) grows forever if both local laws and the blank entry are accepted by Lean. The generator emits these exact equations and never_of_growth certificates for all six compatible-completion cylinders.

The larger sibling still needs assembly. Open-list SHA256 dc5ada780ddfbbfab03ca7228b65204415bfaa6baa9d63eb1e8e5ca0ef16aa2a; tree SHA256 ce3fc5174bb11bc81fddb7d4779ebe2e0a4db7d274266d673dcded73ac7702e5. Enumerated weighted bound candidate 266. Of 5915 open leaves, union of previous bank codes proposed 5695 FAR witnesses, exhaustive canonical DFA search through five states proposed 44 more, and bidirectional ngram search proposed 116 more. The 60 residual leaves require symbolic or other proofs. No sibling bound asserted until exact source audit.
