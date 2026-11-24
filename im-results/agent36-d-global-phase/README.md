# D-machine global phase programme — first-exit rank checkpoint

Original machine: `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---` (Agent31's exact Boundary.lean).

For a canonical finite right word w (scanned end at LSB), let width(w) be the occupied extent, and R(w)=width(w)+2 count(011). Every completed first leftward exit from an arbitrary live configuration increases R by at most 2, where the input includes the scanned bit and the output is the right list at the newly exposed scanned cell. This is proved for the original source, not for an unconnected rewriting model. The newly scanned cell increases R by at most 3; hence first exhaustion of a left context of length m increases R by at most 5m. Since 3R<=5width and width<=R, the nine-cell common E core has

    3 width(output right) <= 5 width(0::ys)+135

at its first marker contact, for every finite suffix ys and arbitrary contact time. No bound on intermediate excursion depth or duration is assumed. It is a bound on successful exits, not a new termination theorem. The finite certificate has 1458 rows (A 272, B 290, C 256, D 256, E 256, F 128); the abstract classes are low six bits plus a long-word flag. Exact rank differences are controlled by local prepend/pop. The finite closure checker uses kernel decide, and the recursive exit derivation and original-source first-exit decomposition are proved by induction. No sorry or native_decide.

## Reproduce

From repository root with Lean 4.36.0-rc2 on PATH:

```bash
root=$PWD
tmp=$(mktemp -d)
cat im-results/agent36-d-global-phase/PhaseCore.b64.0{0,1,2} | base64 -d > "$tmp/proof.tar.xz"
echo "d9cc25079945c7b4a9622e84137d73a5ba0214be14fb83fb09d73612d20b2070  $tmp/proof.tar.xz" | sha256sum -c -
tar -xJf "$tmp/proof.tar.xz" -C "$tmp"
base64 -d im-results/agent31-cryptid-boundary/Boundary.lean.xz.b64 | xz -d > "$tmp/Boundary.lean"
cd "$tmp"
export LEAN_PATH=.
for m in Boundary PhaseTable PhaseRank PhaseSource PhaseCore; do lean -o "$m.olean" "$m.lean" || exit; done
```

The original Boundary SHA256 is 0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883. The three archive parts were checked against the original locally compiled archive by Git blob SHA. The key declarations are BB6.Agent36.Phase.exit_rank_le, source_first_rank, first_empty_rank, rank_width, core_width; the printed axiom audits are standard Lean axioms only. The included Python generators are untrusted.

## Next mathematical use

Combine the fixed E-core width inequality with the source-certified marker sweep and A token-code parsing (10,111; remaining 0 or 110) to bound all first F returns, beyond the previously enumerated regular branches. Aim for 8n<=3n'+26 and 3(n'+L')<=8(n+L)+200; these loose constants still separate all four authentic-root phase bands at Agent26's existing anchors. That would show noncoalescence, not decide whether any authentic root halts. No BB(6) bound claimed.
