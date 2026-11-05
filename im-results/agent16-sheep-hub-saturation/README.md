# Agent 16: genuine Sheep odd-run hubs and residue-invariant saturation through 2-adic depth 24

**Status (2026-11-05):** Exact all-quantifier arithmetic hub lemma, a reproducible finite genuine blank-even prefix certificate, and a consequence for globally inductive finite-residue predicates. The unrestricted generic hub-lifting arithmetic is **Lean-kernel certified** in `Hub.lean` with only standard logical axioms. The 283,345-edge finite witness remains exact-integer tested in `certificate.py` and **is not itself Lean-kernel certified**. It builds on Agent 17's already written all-odd-modulus and high-two-adic zero-fiber theorems, whose general prime-power induction is also not yet imported into Lean. This is an intermediate proof-method result. It does not establish Sheep nonhalting or an upper bound on BB(6).

## Statement

The source-verified Sheep first-even map from the real blank-entry state `10` has the following genuine generic return: for `x=2^a u`, `a>=1`, odd `u>=5`,

`F(x)=x+a+(u-1)/2`.

Writing `F(x)-1=2^h w` with `w` odd gives `E(x)=1+3^h w`. Original six-state machine semantics, the legal odd-run compression and the all-time blank-root reduction were kernel checked in [Agent 16's source bridge](../agent16-sheep-even-return/README.md), [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547).

**Uniform hub lemma.** Fix an authentic generic even source `x=2^a u` with `u` odd and `u>=5`, and put `h=v2(F(x)-1)`. For *every* `k>a` satisfying `k<=a+h+1`, every positive odd `n` and every bound `N`, there exists another genuine generic even source `X>=N` such that

```
X = x (mod 2^k*n),       E(X) = 0 (mod 2^k).
```

The constructed source `X` need not belong to the genuine blank orbit. The congruence equality puts it in the same residue class as an authentic source `x`.

**Finite-root consequence.** The exact Sheep even orbit `x_0=10`, `x_(i+1)=E(x_i)` has at its source index `i=283344` the parameters

```
v2(x_i)=8,  v2(F(x_i)-1)=15,  bit_length(x_i)=227515.
```

Thus its hub capacity `a+h+1` is `24`. For **every positive modulus `m` with `v2(m)<=24`**, any predicate depending *only* on the current even-state residue modulo `m`, which contains the genuine initial state `10` and is inductively preserved by **all legal generic and exceptional Sheep first-even edges**, must include **every even residue class modulo `m`**.

This strengthens the earlier [Agent 17 finite-modulus obstruction through 17](../agent17-sheep-forward/FINITE-MODULI-17.md) to **24**, conditional on the existing all-odd and mixed-modulus zero-fiber arithmetic constructions. This is a global abstract-graph induction obstruction. It does **not** show the real blank orbit reaches every residue, nor rule out history-aware predicates or forward invariants over a richer state.

## Uniform proof of the hub lemma

Let `m=2^k n`, `n` odd, and `L=k-a-1`. Our hypotheses give `0<=L<=h`. Write `M=2^(a+1)+1`, an odd positive integer, and `W=(F(x)-1)/2^L`, an integer. For arbitrary nonnegative integer `t`, set

```
X_t = x + m*t = 2^a*(u+2^(k-a)*n*t).
```

Since `k>a`, the new cofactor is still odd and at least five. The generic branch therefore applies and direct algebra gives

```
F(X_t)-1 = F(x)-1 + M*2^L*n*t
         = 2^L*(W+M*n*t).
```

The multiplier `C=3^L*M*n` is odd. Hence `C` is invertible modulo `2^k`. Choose any `t>=0` satisfying

```
t = -(1+3^L*W)*C^(-1)  (mod 2^k).
```

Then `1+3^L*(W+M*n*t)` is divisible by `2^k`, and is therefore even. As `3^L` is odd, `W+M*n*t` must be odd. Consequently `L` is the *exact* 2-adic valuation of `F(X_t)-1`, and the genuine first-even return is

```
E(X_t)=1+3^L*(W+M*n*t)=0 (mod 2^k).
```

Replacing `t` with `t+q*2^k` preserves the needed residue and permits arbitrary `X_t>=N`. The source congruence is automatic from `X_t=x+m*t`. This exhausts all odd `n`, all permitted `k`, and every target size bound.

## Deduction for all finite moduli with v2(m)<=24

For odd `m`, Agent 17's [ALL-ODD-MODULI](../agent17-sheep-forward/ALL-ODD-MODULI.md) constructs legal synthetic edges between every source and target residue class, so a globally inductive nonempty residue set is full.

For `m=2^k n` with odd `n` and `1<=k<=24`, a globally inductive set containing 10 must contain every residue of the **genuine** finite prefix through `x_283344`. If `k<=8`, that source is already divisible by `2^k`. If `9<=k<=24`, the hub lemma gives a *synthetic* legal edge from a source congruent to `x_283344` into a residue divisible by `2^k`. Global residue-only closure makes this zero-fiber residue included. Agent 17's [ZERO-FIBER](../agent17-sheep-forward/ZERO-FIBER.md) then constructs one legal edge from any included zero-fiber residue to **every even residue** modulo `m`. Closure forces every even class. No step asserts the constructed synthetic states are blank-reachable.

The logical dependence on the full-residue-class induction hypothesis is crucial. An invariant involving the exact state, a certificate language, or the actual history is outside the theorem.

## Kernel-checked all-index hub lifting

The standalone [`Hub.lean`](Hub.lean) imports only Lean 4.36.0-rc2 `Std` and establishes two unrestricted, all-natural theorems:

- `SheepHubs.odd_affine_root_unbounded`: for every `k,A,C,N` with `C` odd, there is a `t>=N` making `2^k` divide `A+C*t`, via a constructive binary-digit lifting proof.
- `SheepHubs.generic_hub_lift`: for every `a,L,n,u,W,N` with `u>=5` odd, `n` odd, and the exact generic Sheep first-return equation
  `2*(1+2^L*W)+1=(2^(a+1)+1)*u+2*a`, a `t>=N` yields a legal lifted odd cofactor `V=u+2^(L+1)*n*t`, odd return quotient `Q=W+(2^(a+1)+1)*n*t`, the genuine generic transition equation for `(V,Q)`, `2^(a+L+1) | 1+3^L*Q`, and the exact source congruence `2^a*V=2^a*u+2^(a+L+1)*n*t`.

These quantified conditions are precisely the constructive hub proof above. Their connection to the existing `SheepEven.EvenEdge` is by the already certified F/E semantics and the displayed generic equation; the new standalone Lean module itself does not import or reprove original-machine semantics. The 283344th source reachability remains an exact-computational certificate.

**Verification:** locally compiled the committed source verbatim with Lean 4.36.0-rc2. `#print axioms odd_affine_root` and `#print axioms generic_hub_lift` both report `[propext, Quot.sound]`; no `sorry`, `admit`, `native_decide`, additional postulates, or hidden oracle. Git blob SHA of the locally compiled file and the remotely committed file both equal `3a9f3753d41862cb98f27f31d189e5bfcad79b0a`.

## Exact finite witness and reproducibility

Run `python certificate.py` with Python 3.10+ and no dependencies. It reconstructs the *entire* finite even-return prefix from 10, checks every generic nonterminal branch and every emitted accelerated source, independently checks the raw `F` odd-run expansions for selected checkpoints, and verifies source fingerprints. It also constructs 80 explicit source-congruence/target-zero witnesses using the modular inverse formula across `k=9,...,24` and odd `n in {1,3,5,17,255}`. These synthetic tests corroborate the **unrestricted written hub lemma**; they are not a replacement for its proof.

The decisive authentic source certificate is:

```
i=283344
v2(x_i)=8, v2(F(x_i)-1)=15
bit_length(x_i)=227515
x_i mod 1000000007 = 989231211
SHA256(minimal big-endian bytes of x_i) =
25377f0e14c813245479e15bcc9a26b1ff75384bbf9417c4e00da0b5b6c289fe
```

Earlier progressively stronger hub-capacity witnesses occur at `i=1` (8), `i=121` (12), `i=989` (17), `i=1283` (18), `i=24884` (19), `i=81103` (20), and `i=87123` (22). All hashes and low residues are in the verifier's deterministic output. The prefix is checked against the published F/E formula, whose original-machine correspondence is already Lean-certified. The **finite 283344-step prefix is not itself kernel-checked**.

## Scope and next research

This improves a mathematical obstruction to one restricted proof strategy and supplies an explicit reusable hub construction. It does not exclude any new halting power, decide the Sheep holdout, or determine BB(6). A plausible next objective is a general-source Lean theorem of the hub lifting lemma, an independent audit of the prime-power zero-fiber proof, and ultimately a true blank-specific invariant that escapes globally residue-only inductiveness. In particular, unbounded hub capacity along the actual orbit has **not** been established; this finite height 24 is no evidence of unboundedness.
