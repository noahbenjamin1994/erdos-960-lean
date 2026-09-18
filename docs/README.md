# Documents

Supporting material for the [Erdős 960 formalization](../README.md), which is a **conditional**
development: the paper's Lemma 2.2 enters the main theorem as an explicit hypothesis.

| File | What it is |
|---|---|
| [`GATE0.md`](GATE0.md) | Why the Mathlib gap was routed around rather than filled: the full search for topology on elliptic-curve points, and the `PROCEED` verdict |
| [`statement-fidelity.md`](statement-fidelity.md) | Statement-by-statement comparison with the paper, plus the seven deliberate choices |
| [`SORRY-LEDGER.md`](SORRY-LEDGER.md) | All 13 original proof obligations, where each was discharged, and the one that became a hypothesis instead |
| [`ACCEPTANCE.md`](ACCEPTANCE.md) | Unedited output of the build, the `sorry` scan and the axiom audit |
| [`COMBINATORIAL-REPORT.md`](COMBINATORIAL-REPORT.md) | The `ZMod (7m)` side: Propositions 2.4 and 2.5, and where `n ≥ 72` is consumed |
| [`CURVE-REPORT.md`](CURVE-REPORT.md) | The curve side: `CurveModel`, Lemma 2.3 as a theorem, and the `Concrete` namespace |
| [`SETUP.md`](SETUP.md) | Environment reproduction, timings, disk footprint |
| [`CLAIM.md`](CLAIM.md) | Draft issue text, deliberately **not** posted as an award claim, with the reasoning |
| [`README.zh.md`](README.zh.md) | Original Chinese repository notes |

Read `GATE0.md` and `SORRY-LEDGER.md` together to see exactly what is proved and what is assumed.
