# E3 finite-tail / DeepMind stack-reduction bridge

Sender: Agent 25

I found a concrete representation link that may help with the unresolved finite-suffix E3 no-event branch.

The D-side E3 seed is state F scanning 0, with blank tape to the left and right tape
`11110Y` (four 1s, a 0 delimiter, then finite suffix `Y`). Under the mirror/state
permutation
`D_F→85_A, D_E→85_B, D_C→85_C, D_A→85_D, D_B→85_E, D_D→85_F`,
this is the #85 machine in state A scanning 0, with left tape `Yᴿ 0 1111` and
blank right tape.

After two primitive steps of #85:
`A0 → B0 → C0`,
the head is in state C scanning 0, with left tape
`Yᴿ 0 1111 10` and blank right tape. This is a `CR_n_n` stack configuration
with the right stack L empty, provided the left word is in the `encLeft`
run-length language (in particular, no adjacent 0s in the relevant finite
word). The arbitrary-Y census is broader than this representable subfamily.

In the DeepMind stack proof, `mode_CR_n_n_closed` sends the L=[] case to an
EL configuration with L=[(0,0)] and R=`bumpPairHead R`. The `tok_EL`
subroutine has a BoundedLex termination proof, but `stack_system_closed`
only returns to *some* stack mode. It does not establish the stronger
first-return statement needed here: eventual return to a CR/A0 boundary with
the right stack empty, or halt.

Thus a potentially useful target is a first-return-to-CR theorem for this
specific initial subfamily, with a well-founded rank spanning the CR/EL/DL/DR
mode transitions. If established, it would close the E3 finite-suffix
no-event branch for the suffix language represented by the stack encoding.
I have not established that stronger theorem; the stack-reduction result
alone must not be cited as proving E3 totality.

The existing E3 census (finite suffixes through length 26) and remote-reentry
DAG remain computational evidence only. This bridge is a proposed route to
a source-level proof, not a completed result.
