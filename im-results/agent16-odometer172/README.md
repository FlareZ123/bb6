# Odometer #172: ternary particle events

Table `1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---` is row 172 of the October 16 roster. The [upstream certified high-level reduction](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/Accelerations/M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH.lean) gives root [0]. All times are high-level returns, not primitive steps.

## Word rewrite

For p in {2,3}*, let phi(2)=2, phi(3)=10; bump_d increments the head by d, or produces [d-1] on empty. The equations obtained from the scan/return modes are:
- p 1 q -> 2 phi(p) bump_1(q).
- 0 q -> 3 bump_2(q).
- p' d 0 q -> 3 2 p' bump_d(q), d=2 or 3.
- p (end) -> 2 phi(p).
- p d q, d>=4 -> halt.

These were exhaustively compared against a literal scan/return implementation through length 7. [Word.lean](Word.lean) now kernel-checks all five equations against the copied upstream functions (Lean 4.36.0-rc2; standard axioms only). An imported-source bridge remains pending.

## Particle encoding and jump formula

Write 2^g0 P(s0) 2^g1 P(s1) ... P(s_(m-1)) 2^gm B, P(0)=10, P(1)=1, P(2)=3; B empty, [0] or [1]. Root g=[0],s=[],B=[0]. Ordinary steps increment the first phase not 2, reset all earlier phases to 0, and increment g0; a 1->2 increment consumes one 2 from the following gap. Empty B allows ordinary all-phase wraps. Thus V=sum s_i 3^i increases by 1. The count of 1->2 transitions at i up to V is C_i(V)=floor((V+3^i)/3^(i+1)). The next attempted 1->2 at zero gap G follows counter value (C_i(V)+G)*3^(i+1)+2*3^i-1. Choose minimum deadline and boundary cap 3^m-1 when B nonempty; subtract C_i differences from gaps and extract ternary digits to jump exactly. The code applies the direct word equations at the event. Adjacent phases 1,1 at zero gap annihilate, exterior gaps merge plus one. Boundary [0] at all-2 births a front particle, [1] wraps. Unsupported particle interactions report HAZARD (not a halting verdict).

Define charge c_i=(g_(i+1)+s_(i+1)+[s_i=2]) mod 3. Ordinary steps preserve charges; c=1 implies safe collision at zero gap. Safe interior annihilation merges charges via c_prev+c_next-1 mod3. A new front gap is charge 1 when the old leading gap is divisible by 3.

## Stronger safety invariant

[PROTECTED.md](PROTECTED.md) proves that an exceptional gap is safe when it is large enough to dominate the mass of its entire right suffix; this property survives all ordinary steps and pair annihilations. Thus the sole remaining safety obligation is that new front gaps born with charge unequal to 1 are protected. The first exceptional birth satisfies this condition. No universal birth-guard proof yet exists.

## Late counterexample

Every preceding birth with a nonempty particle list obeys this leading-gap condition, but event **124075** violates it: pre-event time

`323069319265397144098216023266977412880587235218234728191019785414569939581113256274995473703236357418302939977255`.

The residue is 1, introducing charge 2. This is not a halt. At event 200,000 the exact time is

`3389364540951361976898333063951773469350133448895942427952823190988288356178643196869725545541976296186438870254850601694220331208994917427`.

There are 286 particles, one charge 2 at gap index 72, trailing gap 82,101,657. Counts: 80,058 wraps; 80,055 births; 39,880 safe collisions; 7 drains. No halt or unsupported interaction reached.

Reproduce with `python events.py --events 200000 --check-events`. Every event can be checked against a sparse independent direct-word implementation. The jump formula follows from the ternary carry count; this is finite computational evidence, not a global proof. Next investigate suffix projections and transport of exceptional charges.
