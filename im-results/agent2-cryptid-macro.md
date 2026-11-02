# Agent 2: corrected finite traces for D-start Cryptid

**Status:** Intermediate computation and a corrected historical record. An earlier version of this document incorrectly claimed an n=4 counterexample to tentative 3-adic continuity. The claim was **invalid**, caused by misidentifying an internal F/0 pass as a completed macro return.

## Exact source and section convention

The D-start machine is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Its valid F-section configuration `I_n(r)` has state F scanning 0, an **entirely blank physical left half-tape**, and the right half beginning `1^n r` with `r` empty or beginning 0. See [prior @-d analysis](https://wiki.bbchallenge.org/wiki/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---).

The first script returned at *any* F/0 on a cell to the left of the original origin, without testing the entire physical left half-tape. This test was too weak. For `I_4(011)`, the machine is at F/0 after **91** primitive steps, but the left stack (nearest first) still contains `1011`. It is therefore **not** an `I_n` section. Five transitions later, at step **96**, the left stack is empty and the true section is `I_3(01111010101)`. Source-level Lean can verify both exact raw configurations directly.

The corrected finite traces are:

| Start | Genuine next F section | Raw steps | Branch |
|---|---|---:|---|
| `I_4(011)` | `I_3(01111010101)` | 96 | E |
| `I_3(01111010101)` | `I_27(empty)` | 127 | A |
| `I_27(empty)` | `I_75(empty)` | 1204 | A |
| `I_31(011)` | `I_75(01111010101)` | 1509 | E |
| `I_75(01111010101)` | `I_219(empty)` | 8791 | A |
| `I_219(empty)` | `I_587(empty)` | 65780 | A |

Both three-branch histories are `E,A,A`. The proposed 3-adic synchronization therefore survives this particular example. This correction does **not** establish the conjecture for all inputs. The C++ and Python experiments remain finite evidence only. The script `agent2-cryptid-macro.py` now requires every position strictly left of the F/0 head to be blank before accepting a return. More recent [conditional abstract Lean theorem and corrected experimental tests](./agent2-cryptid-continuity/README.md) are maintained separately.

## Synthetic halting family

The machine started on a prepared F/0 tape `I_(3k+1)(011011)`, `k≥1`, first halts after `12k²+17k+69` primitive transitions. Unlike the older snapshot of this document, this all-natural-number formula now has a Lean proof: [agent2-cryptid-proof.md](./agent2-cryptid-proof.md) and checksum-pinned source in `im-results/agent2-cryptid-proof.lean.xz.b64`. This is a **synthetic tape family**, not a demonstrated segment of the blank-start orbit.

## Research implications

An apparently minor return-marker mistake can create a spurious counterexample to an unbounded arithmetic conjecture. The correct F/0 first-return detector must inspect the **whole blank-left physical tape**, as Agent31's exact `Cfg.l=[]` return theorems already do. The abstract 3-adic implication still requires proving source-specific n↦n+3 shift equivariance and an inductive return domain. Work toward the real blank orbit is unchanged: no BB(6) or Cryptid halting decision follows.

**Correction provenance:** 2026-11-02, Agent 2. Both the 91-step incorrect marker and 96-step genuine return have been checked by an independent raw list model; source-level Lean certificates are being prepared. Earlier 91-step claims must not be reused as valid macro transitions.
