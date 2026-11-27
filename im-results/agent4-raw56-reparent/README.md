# Raw56 E1=1RE — original-source checked branch reduction

Parent partial table: `1RB---_1RC---_0RD---_1LD1LE_---1RE_------`.

## Current proof status (2026-11-27 05:49 UTC)

Locally checked against the original accepted dependency closure, artifact 15160313745, with Lean 4.36.0-rc2:

- E0=0LA: `BB6.Agent4Raw56.RELA.all_quotient`, weighted bound 7014. 1193 splits, 18536 translated cycles, 7336 last leaves, 1501 FAR5 leaves, 56 finite-stack certificates, 11 universal growth proofs.
- E0=0RB: `BB6.Agent4Raw56.RERB.all_quotient`, weighted bound 7014. 1181 splits, 21726 translated cycles, 4946 last leaves, 487 FAR5 leaves, 5 finite-stack certificates.
- E0=0LB and 0LC: `BB6.Agent4Raw56.RE0LB.all_quotient`, `BB6.Agent4Raw56.RE0LC.all_quotient`, weighted bound 10000.
- All four have raw compatible variants `.all`; exported axioms are propext, Classical.choice, Quot.sound only.
- `Raw56REParentCut.lean` checked: first undefined query E0 at step 10, 13 closed children, 11 residual tables. The parent cut and conditional root reduction are valid at 10000. The unconditional parent consumer is pending the remaining child checks.

The other seven children have complete *candidate* covers. Across the nine new branches, 291 holdouts after FAR5 were handled by 278 ordinary ngram/RLE, 6 transferred periodic-block/lag-XOR, 4 late first-query witnesses (1527, 1583, 4072, 7854 steps), and 3 already kernel-checked unbounded-growth proofs. The late witnesses require a parent bound greater than 7014; use 10000. The three new symbolic witnesses are RE0LF M269 (left binary counter), RE1LB M500 (right binary counter with accumulating 110 blocks), RE1RF M491 (five-phase periodic return adding four 8-cell blocks). None of this removes Raw56 from the global root roster without a complete Raw56 proof.

One large literal automaton caused a local 4 GiB memory-limit OOM during checking. A finite-stack certificate quotient by reachable-configuration profiles resolves the data-size bottleneck (9672 to 204 configurations; 7006 to 214). See follow-up compression source and reproducibility patch. No trusted checker is changed.

## Reproduce

Download artifact 15160313745 from the accepted workflow and unpack it to a directory containing manifest.json and the 747 checked modules. ZIP SHA256:
`6513147b3929ab6b707225b6592a882025e234d498ed8baca40216489b469b3d`.
Lean executable SHA256:
`db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00`.

```sh
cat source.tar.xz.b64.0[0-4] | base64 -d > source.tar.xz
sha256sum source.tar.xz
mkdir source
tar -xJf source.tar.xz -C source
cd source
python reproduce.py --base /path/to/a1-raw56-root-consumer --lean /path/to/lean
```

Archive SHA256 `bd70d009d0ca78be4eabe4efb47e4fed93a81c9dee56b999bc7ce7491d61d167`. The five parts are exact git blobs 5d02a6a4cbb8cb7ee814626a19632df8e676ab9d, 725ff7b98953718723e7f0fd222b103ae5ab82f6, 31692c09b5c3dad9c11083b6b6130f034f512e05, d86fab55ce8c620a764ad053fee128ea7953150d, 0bf71ccbe823e0a635fc9928aa69fce9e567af9a.

The bundle includes original C++ cut/FAR5 sources, generators, frozen discovery parameters, late leaves, the four growth modules, original TwoSidedAutomata checker, parent cut and parent consumer. It regenerates the certificate data instead of committing megabytes of generated Lean. The search is untrusted; all final claims depend on the original canonical checker and checked stack certificates. The accepted dependency closure is reused, not independently rebuilt. Use the compression patch before reproduction on memory-constrained runners.
