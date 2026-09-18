# Erdős 960 — a Lean 4 formalisation of Theorem 2.1

[![Lean](https://img.shields.io/badge/Lean-4.34.0-blue)](lean-toolchain)
[![Mathlib](https://img.shields.io/badge/Mathlib-5ed2965-blue)](lake-manifest.json)
[![sorry-free](https://img.shields.io/badge/sorry-0-brightgreen)](verification/scan.log)
[![axioms](https://img.shields.io/badge/axioms-standard%203%20only-brightgreen)](verification/axioms.log)
[![scope](https://img.shields.io/badge/scope-unconditional-brightgreen)](#the-main-theorem)

A machine-checked Lean 4 proof of **Theorem 2.1** of Alexeev–Putterman–Sawhney–Sellke–Valiant,
*Short proofs in combinatorics, probability and number theory II*
([arXiv:2604.06609](https://arxiv.org/abs/2604.06609), §2), which answers
[Erdős Problem 960](https://www.erdosproblems.com/960) in the **negative**.

Prize ledger entry: **JSP-000799** (`TheJustinSunPrize/awards`).

---

## Documents

| Document | What it is |
|---|---|
| [`docs/GATE0.md`](docs/GATE0.md) | The feasibility report: why the paper's own route to Lemma 2.2 is out of reach in Mathlib today. Its verdict is superseded, see the note at its head |
| [`docs/statement-fidelity.md`](docs/statement-fidelity.md) | Statement-by-statement comparison with the paper, plus the deliberate choices |
| [`docs/SORRY-LEDGER.md`](docs/SORRY-LEDGER.md) | Every original proof obligation and where it was discharged |
| [`docs/ACCEPTANCE.md`](docs/ACCEPTANCE.md) | Unedited output of the build, the `sorry` scan and the axiom audit |
| [`docs/COMBINATORIAL-REPORT.md`](docs/COMBINATORIAL-REPORT.md) | The `ZMod (7m)` side: Propositions 2.4 and 2.5, and where `n ≥ 72` is consumed |
| [`docs/CURVE-REPORT.md`](docs/CURVE-REPORT.md) | The curve side: `CurveModel`, Lemma 2.3 as a theorem, and the `Concrete` namespace |
| [`docs/SETUP.md`](docs/SETUP.md) | Environment reproduction, timings, disk footprint |
| [`docs/CLAIM.md`](docs/CLAIM.md) | The award claim text |
| [`verification/`](verification/README.md) | Raw build log, axiom audit, placeholder scan and checksums from a clean rebuild |
| [`docs/README.zh.md`](docs/README.zh.md) | Original Chinese repository notes |

## The question and the answer

For a planar point set `A`, `ord(A)` is the number of *ordinary lines*, the lines meeting `A`
in exactly two points. `F_{r,k}(n)` is the maximum of `ord(A)` over `n`-point sets in which no
line carries `k` points and no `r` points pairwise span ordinary lines. Erdős conjectured
`F_{r,k}(n) = o(n²)`.

**False.** For `r ≥ 3`, `k ≥ 4`, `n ≥ 72`: `F_{r,k}(n) ≥ n²/12 − 10n/3`.

The construction lives on a real cubic curve, where three points are collinear exactly when
they sum to the identity of the group law. Taking a cyclic subgroup of order `7m` and deleting
one residue class turns the whole geometric argument into elementary arithmetic in
`ZMod (7m)`: the ordinary-line graph becomes bipartite, hence `K_r`-free.

## The main theorem

[`Erdos960/Nodal.lean`](Erdos960/Nodal.lean) — verbatim, with no hypotheses beyond the paper's
own numeric ones:

```lean
theorem erdos960_unconditional (r k n : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) (hn : 72 ≤ n) :
    (n : ℝ) ^ 2 / 12 - 10 * (n : ℝ) / 3 ≤ (F r k n : ℝ)
```

It is assembled from `erdos960` in [`Erdos960/Main.lean`](Erdos960/Main.lean), which takes the
paper's Lemma 2.2 as a hypothesis, together with `curveModelAssumption`, which **proves** that
hypothesis. Points worth checking, with the full table in
[`docs/statement-fidelity.md`](docs/statement-fidelity.md):

- **`ord(A)` is genuine plane geometry**, not a combinatorial stand-in: `ptsOn`, `IsLine` and
  `ordinaryLine` are defined on `ℝ × ℝ` and `AffineSubspace ℝ (ℝ × ℝ)`.
- **Finiteness of `ord` is proved, not assumed.** `Set.ncard` returns `0` on infinite sets, so
  without `ordinaryLines_finite` the bound could silently be a statement about `0`.
- **The bound is stated over `ℝ`.** `n²/12` and `10n/3` are not integers in general; `ℕ`/`ℤ`
  truncation would quietly change the claim. `F` lands in `ℤ` because the paper's degenerate
  value is `−1`.
- **All three numeric hypotheses are consumed, none decorative.** `k ≥ 4` is used by
  `noKCollinear_pts`, since the construction really does contain three collinear points, so it
  is false for `k = 3`; `r ≥ 3` by `cliqueFree_of_isBipartite`; `n ≥ 72` becomes `m ≥ 12`
  through `zsmul_hgen_inj`, and weakening it to `0 < m` was measured to break two `omega` calls.
- **Anti-vacuity checks.** The bound is `192 > 0` at `n = 72`, and the degenerate `F = −1`
  branch is excluded under the theorem's own hypotheses.

## How Lemma 2.2 is proved

The paper takes its cyclic subgroups from `E(ℝ)` being connected for the smooth curve
`y² = x³ − x + 1`, hence `E(ℝ) ≅ ℝ/ℤ`. That route is closed in Mathlib today: there is no
`TopologicalSpace` instance on `WeierstrassCurve.Affine.Point` at all, no Lie theory for it,
and no uniformisation `ℂ/Λ ≅ E(ℂ)`. The search is logged in [`docs/GATE0.md`](docs/GATE0.md).

What the argument needs is weaker than what the paper invokes. `CurveModel` asks only for
*some* injection of the group into the plane whose collinear triples are exactly its zero-sum
triples, and the paper itself notes in §2.2 that any non-degenerate curve will do. A
**singular** cubic supplies one, with a group law that is pure trigonometry.

[`Erdos960/Nodal.lean`](Erdos960/Nodal.lean) works with the nodal cubic `Z(X² + Y²) = X³`,
which has an acnode at `[0 : 0 : 1]`, so its real smooth locus is a circle rather than a line
and it carries finite cyclic subgroups of every order. It is parametrised by an angle,

```lean
Pt φ = (cos (φ + π/6), sin (φ + π/6), cos (φ + π/6) ^ 3)
```

and the whole construction rests on one identity, `det3_Pt`:

```
det3 (Pt a) (Pt b) (Pt c) = sin (b - a) * sin (c - a) * sin (c - b) * sin (a + b + c)
```

So three pairwise distinct points are collinear exactly when `a + b + c ≡ 0 (mod π)`, and
`φ = k·π/N` gives `ZMod N`. Two details carry real weight:

1. **The `π/6` shift is essential.** Without it the criterion reads `≡ π/2 (mod π)`, which is
   not a group condition. The shift moves the origin of the group law to an inflection point.
2. **The chart is chosen after the subgroup.** `Pt` lands in the projective plane, and for even
   `N` one group point sits on the line at infinity of the obvious chart. The fix is to divide
   by the linear form through two reference points at angles `π/(4N)` and `2π/(4N)`; the third
   intersection of that line with the cubic is at `−3π/(4N)`, and none of `1`, `2`, `−3` is
   divisible by `4`, so no `kπ/N` ever lands on it. Collinearity is projective, so the criterion
   survives the chart (`collinear_chart_iff`).

`Erdos960.Nodal.curveModel` packages this and `Erdos960.curveModelAssumption` discharges the
hypothesis for every `7m`. Nothing in the chain uses topology, Lie groups or uniformisation.
Lemma 2.3, no four collinear points, was already a theorem rather than an assumption: it
follows from the criterion by cancellation alone.

## Verification

```bash
lake exe cache get          # ~6.7 GB of prebuilt Mathlib oleans
lake build                  # 8931 jobs
lake env lean Axioms.lean   # the audit list: 133 `#print axioms`
```

Raw output from a clean rebuild is committed under [`verification/`](verification/README.md):
[`build.log`](verification/build.log), [`axioms.log`](verification/axioms.log),
[`scan.log`](verification/scan.log) and [`CHECKSUMS.txt`](verification/CHECKSUMS.txt), so a
reviewer can diff against their own run rather than take these numbers on trust. Every audited
declaration reports only `propext`, `Classical.choice` and `Quot.sound`; several report fewer,
which is stronger.

`grep -rn sorry Erdos960/` does match twice, and both are the words `` `sorry`-free `` in
file-header prose. The mechanical criterion is Lean's own `declaration uses 'sorry'` count,
which is 0.

Environment: Lean `leanprover/lean4:v4.34.0`, Mathlib tag `v4.34.0`, commit
`5ed2965256430c3649e86755f9576b54eca72435`. **Do not move the pins**, since the proofs are
written against that Mathlib API.

## Credit

The mathematics is due to **Boris Alexeev, Mehtaab Putterman, Mehtaab Sawhney, Mark Sellke and
Gregory Valiant**, §2 of the paper. **Prover credit belongs entirely to them.** The
construction, the lemmas, the constants and the `n ≥ 72` threshold are all theirs.

What is claimed here is the independent **formalizer credit**: rebuilding that proof in Lean 4,
including supplying the curve-side input by a route Mathlib can support today.

## Layout

```
Erdos960.lean                   root module
Erdos960/
  Defs.lean               328   §2.1 — ptsOn / IsLine / ordinaryLine / ord / G_A / F
  Curve.lean              482   CurveModel, Lemma 2.3 (proved), the `Concrete` namespace
  Combinatorial.lean      873   §2.2.2–§2.3 — elementary arithmetic in ZMod (7m), Props 2.4, 2.5
  Bridge.lean             142   geometry ⇄ group theory: edgeCount = ord
  Main.lean               213   Theorem 2.1 given Lemma 2.2, plus numeric anti-vacuity instances
  Nodal.lean              445   Lemma 2.2 on a nodal cubic, and the unconditional Theorem 2.1
Axioms.lean               163   the 133-line `#print axioms` audit list
docs/                           reports, fidelity table, gate-0 report, claim text
verification/                   raw logs and checksums from a clean rebuild
```

Proof skeleton, each step a numbered result in the paper:

```
Nodal.curveModel ................. Lemma 2.2 (PROVED, on Z(X²+Y²) = X³)
  └─ collinearity criterion
       ├─ no_four_collinear ....... Lemma 2.3 (proved, never assumed)
       │    └─ noKCollinear_pts ... the k ≥ 4 half of Admissible
       └─ ordinaryLine_iff ........ Prop 2.4 reduction: geometry ⇄ ZMod arithmetic
            └─ edgeCount_eq_ord ... e(G_A) = ord(A), exact halving via ordered pairs
                 ├─ ord_A₀_ge ..... Prop 2.4: ord(A₀) ≥ 3m²
                 ├─ Aset_bipartite  Prop 2.5(2): G_A bipartite ⇒ K_r-free (r ≥ 3)
                 └─ ord_Aset_ge ... Prop 2.5(3): ord(A) ≥ 3m² − 3ms
                      └─ erdos960_unconditional ... §2.3, the stated bound
```

## Known limits

1. **The curve is not the paper's.** The bound proved is exactly the paper's Theorem 2.1, but
   the point configuration comes from the nodal cubic `Z(X² + Y²) = X³` rather than from
   `y² = x³ − x + 1`. The paper's §2.2 licenses changing the curve; a reader who wants that
   specific curve will not find it carrying the main theorem here.
2. **The `Concrete` namespace is still detached.** It proves what Mathlib supports today for
   `y² = x³ − x + 1`: discriminant `−368` (`= 16 ×` the paper's `−23` under Mathlib's LMFDB
   normalisation), non-vanishing, non-singularity, and Lemma 2.3 for that curve via
   `Polynomial.card_roots'`. The main theorem uses none of it. Connecting it still needs
   `E(ℝ) ≅ ℝ/ℤ`, the gate-0 obstruction.
3. **`collinear_iff` is stated for pairwise distinct triples**, where the paper's "counted with
   multiplicity" is vacuous. Tangency cases fall outside the criterion, and the counting
   argument never needs them.
4. No paper or literature review is produced; the deliverable is the source and its audit.

## References

- Alexeev, Putterman, Sawhney, Sellke, Valiant, *Short proofs in combinatorics, probability and
  number theory II*, [arXiv:2604.06609](https://arxiv.org/abs/2604.06609), §2.
- [Erdős Problem 960](https://www.erdosproblems.com/960)

## License

Apache-2.0, see [`LICENSE`](LICENSE).
