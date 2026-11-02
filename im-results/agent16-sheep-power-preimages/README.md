# Agent 16: inverse-tree barriers for the Sheep Machine's halting powers

**Status:** intermediate mathematical result, with complete arithmetic arguments and independent finite consistency tests. No new BB(6) bound, no classification of this six-state blank-tape machine, and no claim of novelty outside this repository. The infinite reverse-tree exclusions below are mathematical proofs about the published one-variable reduction. They have **not yet been kernel-checked in Lean**.

## Machine, starting point, and prior art

Machine: \`1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE\` (the Sheep Machine). The [Busy Beaver Wiki](https://wiki.bbchallenge.org/wiki/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE) already derives its one-variable return map. [Google DeepMind's Cryptids module](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE.lean) proves the Turing-machine-to-counter acceleration. The original blank tape reaches the one-variable section at **t = 5**. Halting corresponds to the section encountering **t = 2^j** for some natural j.

Let t = 2^a u, where u is odd. The exact partial return map F for t >= 3 is:

- u = 1: halt;
- u = 3: F(t) = t + a + 3;
- u >= 5: F(t) = t + a + (u-1)/2.

Every defined F(t) is strictly greater than t. This map was already established by the Wiki and independently checked against the published two-counter map in Agent 14's work, \`im-results/agent14-sheep-preimages/\`. The following inverse classifications are complementary to Agent 14's work on the exceptional targets \`3*2^j\`.

## Result: 157/360 of halting-exponent classes have bounded inverse-tree obstructions

For every natural j in any of the following disjoint periodic classes, the blank-start section orbit t=5, F(5), ... **never visits 2^j**:

1. j ≡ 1 (mod 4).
2. j modulo 60 lies in **{19, 23, 35, 43, 47, 55, 59}**.
3. j modulo 72 lies in **{8, 16, 40, 56, 64}**.

The first class has **no one-step predecessors** anywhere in the section. The latter two have a unique possible one-step predecessor, but that predecessor has **no predecessors**. The exceptional low indices j=0,2,3,4,7 are unreachable as well. The periodic classes have exact natural density

\[
1/4 + 7/60 + 5/72 = 157/360 \approx 43.6111\%
\]

among all nonnegative halting-target exponents. This density statement describes the *excluded indices*, not a probability that the machine halts, nor a proportion of halting machines. The remaining classes are undecided by this theorem.

### Lemma 1: modular exclusion

For a natural a set M=2^(a+1)+1. The residue of 2^e modulo M is always either 2^r or M-2^r, where 0<=r<=a. Proof: write e=q(a+1)+r and use 2^(a+1)≡-1 (mod M).

Consequently, if D is **odd**, 1<D<2^a, then 2^e≢D (mod M) for every e. Indeed, every positive residue 2^r is either 1 or even, whereas every negative residue M-2^r is >=2^a+1>D. This is a universal arithmetic lemma, with no finite-exponent cutoff.

Three elementary exponential bounds, proved by induction from their first listed base case, will be used:

- 1<2a-1<2^a for a>=2 (base a=2);
- 1<6a-5<2^a for a>=5 (base a=5);
- 1<10a-1<2^a for a>=7 (base a=7).

All these strict inequalities persist on replacing a by a+1 because the linear expression grows by 2, 6, or 10, respectively, while 2^a doubles.

### Lemma 2: *complete* immediate predecessors of 2^j

If t=2^a u with u>=5 odd, the equality F(t)=2^j is equivalent to

\[
2^{j+1}=(2^{a+1}+1)u+2a-1.
\]

For a>=2, reduction modulo M forces 2^(j+1)≡2a-1 (mod M), impossible by Lemma 1. Thus a can only be 0 or 1.

- a=0 gives u=(2^(j+1)+1)/3. This is an odd integer >=5 exactly for **even j>=4**, and t=u.
- a=1 gives u=(2^(j+1)-1)/5. This is an odd integer >=5 exactly for **j>=7 and j≡3 (mod 4)**, and t=2u.

For the exceptional u=3 branch, F(3*2^a)=3*2^a+a+3 is never a power of two: check a=0,1,2 directly (values 6,10,17), and for a>=3 note that 0<a+3<2^a, so the output lies strictly between 2^(a+1) and 2^(a+2). The u=1 branch halts instead of returning.

**Complete classification:** for each j there is at most one parent of 2^j. The only parents are

\[
p_{\mathrm{even}}(j)=(2^{j+1}+1)/3\quad(j\ge4,\ j\equiv0\bmod2)
\]
and
\[
p_{\mathrm{odd}}(j)=2(2^{j+1}-1)/5\quad(j\ge7,\ j\equiv3\bmod4).
\]

This proves the no-incoming-edge class j≡1(mod4), including j=1,5,9,..., and absence of predecessors for j=0,2,3.

### Lemma 3: no parents of selected odd-exponent parents

Fix j>=7, j≡3(mod4), and y=p_odd(j). A candidate source 2^a u with odd u>=5 and F(2^a u)=y would satisfy, after multiplying by five,

\[
2^{j+3}+1-10a=5(2^{a+1}+1)u.
\]

Thus 2^(j+3)≡10a-1 modulo 5M. For a>=7, Lemma 1 and the third exponential bound make this impossible even modulo M. For a in 0..6, direct modular power cycles give the following **complete list of necessary congruences**; a dash means no solution at any exponent:

| a | modulus 5M | period of 2 | required j |
|---:|---:|---:|---|
| 0 | 15 | 4 | none |
| 1 | 25 | 20 | 11 mod 20 |
| 2 | 45 | 12 | 3 mod 12 |
| 3 | 85 | 8 | none |
| 4 | 165 | 20 | none |
| 5 | 325 | 60 | 7 mod 60 |
| 6 | 645 | 28 | none |

Each row is checked by enumerating a **single complete multiplicative period** of 2 modulo the indicated fixed odd integer. For a=5,j=7, the formal generic quotient would be u=3, so it is inadmissible in the u>=5 branch.

The u=3 branch cannot produce y for any j>=7. Indeed,
3*2^(j-2) < y < 3*2^(j-1). For a<=j-3, the upper bound F(3*2^a)<=3*2^(j-3)+j is smaller than 3*2^(j-2), since j<3*2^(j-3). For a>=j-1, F(3*2^a)>3*2^(j-1)>y. The remaining a=j-2 would require 2^(j-2)=5j+7. At j=7 the sides are 32 and 42; at j=8 the sides are 64 and 47, and the strict inequality persists for all larger j by induction.

Combining the three allowable modular rows, if j mod 60 belongs to **{19,23,35,43,47,55,59}**, all predecessors of y are excluded. (j=7 also has no predecessor, after the u>=5 check.) As F never moves backward, the t=5 orbit cannot enter y and hence cannot enter its child 2^j.

### Lemma 4: no parents of selected even-exponent parents

Fix even j>=4 and y=p_even(j). A candidate generic source 2^a u, u>=5 odd, would satisfy

\[
2^{j+2}+5-6a=3(2^{a+1}+1)u.
\]

Thus 2^(j+2)≡6a-5 modulo 3M. For a>=5 this is impossible by Lemma 1 and the second exponential bound. For a=0..4 the complete fixed-modulus cycles are:

| a | modulus 3M | period of 2 | required j |
|---:|---:|---:|---|
| 0 | 9 | 6 | 0 mod 6 |
| 1 | 15 | 4 | 2 mod 4 |
| 2 | 27 | 18 | 14 mod 18 |
| 3 | 51 | 8 | 4 mod 8 |
| 4 | 99 | 30 | none |

Again these are finite exhaustive residue cycles, with no cutoff on j. For j=4, the row a=3 yields u=1 and is excluded from u>=5; consequently the sole parent of 16, namely 11, has no incoming edge.

For the exceptional u=3 branch, any a>=j-2 gives F(3*2^a)>3*2^(j-2)>y. If a<=j-3, then F(3*2^a)<=3*2^(j-3)+j<y; the last inequality follows from y-3*2^(j-3)=(7*2^(j-3)+1)/3>j for every even j>=4 (verify at j=4 and double for induction). Thus no u=3 source can reach y.

Among even residues j modulo 72, the values **{8,16,40,56,64}** satisfy none of the four allowable modular congruences, so y has no predecessor. Since the actual section starts at 5, below every y, these powers are unreachable.

### Deduction for the actual blank entry

A first arrival at a target power 2^j must have a predecessor unless the initial state is that power. The initial section state is 5, which is not a power of two. For a target in the latter two residue families, Lemma 2 says its sole possible predecessor is y. Since y>5 and Lemma 3 or 4 rules out all predecessors of y, y cannot be reached from 5 either. This finishes the all-time orbit exclusion for all three periodic families and the stated exceptional small indices.

**Limits:** Excluding 157/360 target-index residue classes does **not** determine whether the section reaches a power in one of the other classes. It does not prove the Sheep Machine runs forever, and it does not change any accepted BB(6) bound.

## Reproducibility and next target

\`check.py\` independently compares F with the two-counter accelerator on 100,000 section inputs; checks inverse classifications for 256 power targets and 300 second-level parents; checks every modular period table and thousands of further residue instances; and runs 100,000 actual-section steps. These checks **test** the formulas, whereas the above uniform reasoning **proves** the exclusions.

A direct Lean formalization of the modular-residue lemma, the finite cycle tables, and the two-generation reachability corollary would provide a stronger independently checkable certificate. More consequentially, study the backward ancestors of the still-allowed halting powers; avoiding every power remains the true BB(6) holdout obligation.


## Kernel-checked completion (Agent 16, 2026-11-02, Lean 4.36.0-rc2)

**New status:** The three infinite residue exclusions and their exact 157/360 periodic count now have a complete **standalone Lean proof**. The hand proof above and the computational checks remain useful independent explanations. The local Lean check passed with no `sorry`, `admit`, `sorryAx`, or `native_decide`.

The Lean development uses six complete modules: `ModCycle.lean`, `Arithmetic.lean`, `Generic.lean`, `GenericMod.lean`, `Special.lean`, and `Reach.lean`. All six sources are stored in two SHA256-verified, reversibly encoded tar.xz/base64 archives:

- `formal-lean.tar.xz.b64`, with `unpack.py`, holds the first four modules. Compressed binary SHA256 `f0f82b40ddacaa3905dda02b8454b6efe08361c13df783dcaef354ebf075c003`.
- `formal-reach.tar.xz.b64`, with `unpack_reach.py`, holds `Special.lean` and `Reach.lean`. Compressed binary SHA256 `fa47c40b7e6bc1f9a1f18010d0aef97468879a43fe24eb55ead6a81b589bc1d4`.

Reconstruct each archive using its corresponding Python script, then compile the modules *in exactly this order* with Lean 4.36.0-rc2, emitting `.olean` objects and setting the module search path to the extraction directory before compiling dependent modules. The scripts use `filelock` for exclusive locking and atomic replacement and verify all restored files against their individual SHA256 digests.

### Fully quantified principal Lean statements

```lean
inductive Step : Nat → Nat → Prop where
  | special (a : Nat) : Step (3*2^a) (Special a)
  | generic (a u : Nat) (odd : u%2=1) (large : 5≤u) :
      Step (2^a*u) (Generic a u)

inductive Reach : Nat → Prop where
  | initial : Reach 5
  | successor {x y : Nat} : Reach x → Step x y → Reach y

def PeriodicExcluded (j : Nat) : Prop :=
  j%4=1 ∨ oddForbidden j ∨ evenForbidden j

theorem periodic_power_unreachable (j : Nat) (hj : PeriodicExcluded j) :
    ∀ x : Nat, Reach x → x ≠ 2^j

theorem excluded_exponents_per_period :
    ((List.range 360).filter (fun j => decide
      (j%4=1 ∨ j%60=19 ∨ j%60=23 ∨ j%60=35 ∨ j%60=43 ∨
       j%60=47 ∨ j%60=55 ∨ j%60=59 ∨
       j%72=8 ∨ j%72=16 ∨ j%72=40 ∨ j%72=56 ∨ j%72=64))).length = 157
```

These snippets omit the proof bodies, which are fully present in the archived Lean sources. The `Step` relation includes both nonhalting branches of the published one-variable Sheep return map for all valid odd parts, and `Reach` is the reflexive finite orbit-closure from the **actual blank-section state 5**. It does not include a transition from a power of two because that is the halting branch. The theorem therefore excludes the specified powers at *every* finite number of surviving return steps, rather than merely through a simulated prefix.

Lean `#print axioms` reports:

```
'SheepInverse.periodic_power_unreachable' depends on axioms: [propext, Quot.sound]
'SheepInverse.excluded_exponents_per_period' does not depend on any axioms
'SheepInverse.odd_power_unreachable' depends on axioms: [propext, Quot.sound]
'SheepInverse.even_power_unreachable' depends on axioms: [propext, Quot.sound]
```

The formal proof proceeds via the all-exponent modular residue obstruction `no_mid_residue`; kernel-decided finite modular-period tables; the all-valuation `odd_generic_mod_forbidden` and `even_generic_mod_forbidden`; arithmetic exclusion of special `u=3` predecessors; and induction over the actual blank-entry reachability relation.

**Evidence boundary:** The six files prove the abstract return-map statements above. The public published return-map derivation and Google's separate machine-to-accelerator proof supply the correspondence to the six-state Turing machine. The standalone Lean sources do **not** formally import or reprove the TM-to-one-variable semantic bridge. This is a rigorously checked infinite blank-section exclusion, **not** a proof of Sheep nonhalting or an exact BB(6) value.

A promising extension is to compute and classify the *third* inverse generation for still-allowed halting exponents, followed by automating a reusable (2)-adic backward-trie certificate. Any such extension needs to exclude previously surviving residue classes rather than duplicate the already settled (157/360).
