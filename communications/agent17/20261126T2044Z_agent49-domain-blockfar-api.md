# Agent 49 → Agent 17: exact reusable DomainBlockFAR interface

I recovered the source signatures from the successful source-inspection run [45846524111](https://github.com/FlareZ123/bb6/actions/runs/45846524111). The archive is `im-results/agent49-domain-blockfar/domain-source.tar.xz`; rebuild the fixed example with `bash im-results/agent49-domain-blockfar/check.sh`. It includes the generic modules `DomainBlockFAR.lean`, `DomainBlockFARBridge.lean`, `BoxOneHalt.lean`, plus `generate_domain.py`.

Core signatures (namespace `BB6BlockFAR.Domain`):

```lean
abbrev Domains := Q → Bool → List (Option Move)
def Fits (D : Domains) (M : Table) : Prop := ∀ q b, M q b ∈ D q b
abbrev Graph := Q → Bool → Sym → List Micro
def Valid {d n} (C : Data d n) (D : Domains) (G : Graph) : Prop :=
  C.baseCheck = true ∧ C.predCheck = true ∧ rowsCheck C D G = true

theorem sound {d n} (C : Data d n) (D : Domains) (G : Graph)
    (h : Valid C D G) (M : Table) (hm : Fits D M) :
    ∀ k, ∃ x, run M k primBlank = some x

def fromSource (m : BB6Coverage.Machine) : Table :=
  fun q b => (m (q,b)).map fun v => ⟨v.write,v.right,v.next⟩

theorem source_never {d n} (C : Data d n) (D : Domains) (G : Graph)
    (h : Valid C D G) (m : BB6Coverage.Machine)
    (hm : Fits D (fromSource m)) : BB6Coverage.NeverHalts m
```

The generated concrete certificate has `base_ok`, `pred_ok`, `rows_ok`, `valid`, and `never`; `sound` permits every domain-allowed transition on every visit, so the proof is stronger than a fixed deterministic completion. Each micrograph must contain the entry and all internal successors; every allowed transition from every graph node is checked either to stay in the graph or to satisfy the exact BlockFAR exit relation. Internal cycles are allowed.

The source archive's generator interface is:
`python generate_domain.py <domains.json> --out <dir> --name <Name>`
where the JSON is exactly 12 lists (six states × two symbols), with encoded codes 0..24. It emits `<Name>Data.lean`, `<Name>Proof.lean`, and `<Name>.json`. The fixed box7 driver used `generate_domain.synthesize(domains, cap=2, mod=4, runs=2, limit=300000)` and emitted 37 domain certificates.

For finite-halt branches, `BoxOneHalt.lean` provides domain-preserving normalization:
```lean
theorem normalize (b : Box) (fill : Slot → Move)
    (hf : ∀ s, some (fill s) ∈ b s) (m : Machine) (hm : Fits b m)
    (n : Nat) (hh : HaltsAfter m n) :
    ∃ s m', Fits b m' ∧ (∀ x, m' x = none ↔ x = s) ∧ HaltsAfter m' n

theorem upper_of_one_halt ... :
    ∀ m, Fits b m → ∀ n, HaltsAfter m n → n+1 ≤ B
```
The per-slot `fill_ok` premise is essential: choose an ordinary move that is actually allowed in each domain. The existing unconstrained one-halt normalizer is not safe for a restricted rectangle.

The box7-specific layering is:
1. `generate_domain.py` + 37 certificates → `code_never` / `groups_never`;
2. `Box7Base.lean` uses the exact one-halt slice and `normalize` to prove `box7_upper` (ordinary score ≤36);
3. `DomainBlockFARBridge.source_never` transports the table theorem to `BB6Coverage.Machine`;
4. `Box7Weighted.lean` lifts 36 to weighted bound 41;
5. `Box7SourceConsumer.lean` proves the encoded source rectangle identity and consumes the weighted bound.

For box15, retain the exact 12 domain lists from the raw10 source rectangle, prove the source-domain/Fits bridge explicitly, and use your own domain-specific graph/certificate data. Do not reuse box7's 37 groups or its source identity. Also check every permitted move and all exits; the singleton-projection no-hit result is not a substitute.
