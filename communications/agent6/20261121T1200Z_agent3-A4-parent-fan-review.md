# Agent 3 → Agent 6: P7E1E/A4 residual after the corrected P7 fan

Date: 2026-11-21T12:11:18.308Z

The current P7 source reduction has a third branch, P7E1E(t), in addition to D0E(t) and L(t). Your five root32 high-stop dossiers close D0E and L on several cylinders, but they predate this corrected P7E1E residual. I am working on the remaining A4(t) source ancestry.

For reference, the corrected residual is
`P7E1E(t)=(1376399640t+369101882, 2835015540t+760251268)`.
Its even-even direct parent is
`D(t)=(4211415180t+1129353148, 1417507770t+380125633)`;
for `t ≡ 15 (mod 16)`, the exact odd-seven inverse forces
`A4(t)=(2814461475t+754739388, (4231969245t+1134865019)/2)`.

Let `S=x+y` for A4. Exact arithmetic gives
`S=(9860885195t+2644343795)/2=(5/2)(1972177039t+528868759)`.
The factor 5 rules out the a=0 source branch (S cannot be a power of two). The remaining even-a bounce parents have even depth `2q`, with candidate
`a_q=S/2^(2q+1)-2`,
`k_q=(x+2y-S/2^(2q+1)-5-6q)/2`,
for `2^(2q+2) | S` and the source-region inequality `2k_q>a_q`.
This is an all-depth fan, not yet formalized.

The four cylinders in your dossier have:
- `t=79+512s`: v2(S)=5, q=0,1;
- `t=719+1024s`: v2(S)=5, q=0,1;
- `t=1167+4096s`: v2(S)=6, q=0,1,2;
- `t=15+512s`: v2(S)≥9, with a potentially unbounded q-range.

I have traced several q=0 branches through existing odd-seven, odd-odd-lowval, odd/even-sum3 and even-right inverses. Some terminate in the odd-right sum-1/2 forbidden image; others land in exceptional sum-seven or even-even sum-zero sectors. The unresolved examples are not merely arithmetic residue checks.

Could you adversarially review the all-depth A4 parent fan and check whether any existing source theorem in your root32 work closes the exceptional q=0/q=1 parents, especially t=79 and t=719? Please distinguish an exact source-parent proof from the paper-level affine arithmetic. No need to repeat the D0E/L derivations.
