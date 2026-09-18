# Documents

Supporting material for the [Erdős 960 formalization](../README.md).

Several of these reports were written while the paper's Lemma 2.2 was still an explicit
hypothesis of the main theorem. It is now proved, in `Erdos960/Nodal.lean`, and the top-level
theorem is `Erdos960.erdos960_unconditional`. Each affected file carries a dated note at its
head; the bodies are left as the original record.

| File | What it is |
|---|---|
| [`GATE0.md`](GATE0.md) | Why the Mathlib gap was routed around rather than filled: the full search for topology on elliptic-curve points, and the `PROCEED` verdict |
| [`statement-fidelity.md`](statement-fidelity.md) | Statement-by-statement comparison with the paper, plus the seven deliberate choices |
| [`SORRY-LEDGER.md`](SORRY-LEDGER.md) | All 13 original proof obligations, where each was discharged, and the one that became a hypothesis instead |
| [`ACCEPTANCE.md`](ACCEPTANCE.md) | Unedited output of the build, the `sorry` scan and the axiom audit |
| [`COMBINATORIAL-REPORT.md`](COMBINATORIAL-REPORT.md) | The `ZMod (7m)` side: Propositions 2.4 and 2.5, and where `n ≥ 72` is consumed |
| [`CURVE-REPORT.md`](CURVE-REPORT.md) | The curve side: `CurveModel`, Lemma 2.3 as a theorem, and the `Concrete` namespace |
| [`SETUP.md`](SETUP.md) | Environment reproduction, timings, disk footprint |
| [`CLAIM.md`](CLAIM.md) | The award claim text |
| [`README.zh.md`](README.zh.md) | Original Chinese repository notes |

Read `GATE0.md` for why the paper's own route to Lemma 2.2 is unavailable, then the
`How Lemma 2.2 is proved` section of the top-level README for the route actually taken.
