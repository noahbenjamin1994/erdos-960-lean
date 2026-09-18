# Erdős 960 — a *conditional* Lean 4 formalisation of Theorem 2.1

[![Lean](https://img.shields.io/badge/Lean-4.34.0-blue)](lean-toolchain)
[![Mathlib](https://img.shields.io/badge/Mathlib-5ed2965-blue)](lake-manifest.json)
[![sorry-free](https://img.shields.io/badge/sorry-0-brightgreen)](docs/ACCEPTANCE.md)
[![axioms](https://img.shields.io/badge/axioms-standard%203%20only-brightgreen)](docs/ACCEPTANCE.md)
[![scope](https://img.shields.io/badge/scope-conditional%20theorem-orange)](#-read-this-first-the-theorem-is-conditional)

A machine-checked Lean 4 development of **Theorem 2.1** of Alexeev–Putterman–Sawhney–Sellke–Valiant,
*Short proofs in combinatorics, probability and number theory II*
([arXiv:2604.06609](https://arxiv.org/abs/2604.06609), §2), which answers
[Erdős Problem 960](https://www.erdosproblems.com/960) in the **negative**.

Prize ledger entry: **JSP-000799** (`TheJustinSunPrize/awards`).

---

## 🔴 Read this first: the theorem is conditional

The repository builds clean, contains **zero `sorry`**, and all **123** exported declarations
audit to the three standard Mathlib axioms. That is *not* the whole story:

**the paper's Lemma 2.2 is an explicit hypothesis in the main theorem's signature, not a proof.**

It is not an `axiom` (nothing is asserted) and not a `sorry` (no proof obligation is dodged) — it
is a `Prop`-valued definition that the caller must supply:

```lean
structure CurveModel (G : Type*) [AddCommGroup G] where
  emb : G → ℝ × ℝ
  emb_injective : Function.Injective emb
  collinear_iff : ∀ x y z : G, x ≠ y → y ≠ z → x ≠ z →
    (Collinear ℝ ({emb x, emb y, emb z} : Set (ℝ × ℝ)) ↔ x + y + z = 0)

def CurveModelAssumption (m : ℕ) : Prop := Nonempty (CurveModel (ZMod (7 * m)))
```

So what is delivered is: *given that a cyclic group of order `7m` embeds in the real plane with
collinearity governed by the group law, every argument of §2.2.2–§2.3 goes through.* **It is not a
complete machine verification of Theorem 2.1**, and it must not be described as one.

Why the gap exists: the paper gets that embedding from `E(ℝ)` being connected, hence isomorphic to
the circle group `ℝ/ℤ`. Mathlib has no `TopologicalSpace` instance on
`WeierstrassCurve.Affine.Point` at all — let alone a Lie group structure or the uniformisation
`ℂ/Λ ≅ E(ℂ)` — so that route means building an entire theory first. The gate-0 search that
established this (zero hits across `Mathlib/AlgebraicGeometry/EllipticCurve/`) is in
[`docs/GATE0.md`](docs/GATE0.md).

One thing came out **better** than gate 0 predicted: the paper's Lemma 2.3 (no four collinear
points) was expected to be assumed too. It is not — `CurveModel.no_four_collinear` is *proved*
from the collinearity criterion by pure group theory. The permanent gap is Lemma 2.2 alone.

## Documents

| Document | What it is |
|---|---|
| [`docs/GATE0.md`](docs/GATE0.md) | Why the Mathlib gap was routed around rather than filled: the full search for topology on elliptic-curve points, and the `PROCEED` verdict |
| [`docs/statement-fidelity.md`](docs/statement-fidelity.md) | Statement-by-statement comparison with the paper, plus the seven deliberate choices |
| [`docs/SORRY-LEDGER.md`](docs/SORRY-LEDGER.md) | All 13 original proof obligations, where each was discharged, and the one that became a hypothesis instead |
| [`docs/ACCEPTANCE.md`](docs/ACCEPTANCE.md) | Unedited output of the build, the `sorry` scan and the axiom audit |
| [`docs/COMBINATORIAL-REPORT.md`](docs/COMBINATORIAL-REPORT.md) | The `ZMod (7m)` side: Propositions 2.4 and 2.5, and where `n ≥ 72` is consumed |
| [`docs/CURVE-REPORT.md`](docs/CURVE-REPORT.md) | The curve side: `CurveModel`, Lemma 2.3 as a theorem, and the `Concrete` namespace |
| [`docs/SETUP.md`](docs/SETUP.md) | Environment reproduction, timings, disk footprint |
| [`docs/CLAIM.md`](docs/CLAIM.md) | Draft issue text. Deliberately **not** posted as an award claim, with the reasoning |
| [`docs/README.zh.md`](docs/README.zh.md) | Original Chinese repository notes |

## The question and the answer

For a planar point set `A`, `ord(A)` is the number of *ordinary lines* — lines meeting `A` in
exactly two points. `F_{r,k}(n)` is the maximum of `ord(A)` over `n`-point sets in which no line
carries `k` points and no `r` points pairwise span ordinary lines. Erdős conjectured
`F_{r,k}(n) = o(n²)`.

**False.** For `r ≥ 3`, `k ≥ 4`, `n ≥ 72`: `F_{r,k}(n) ≥ n²/12 − 10n/3`.

The construction lives on the real elliptic curve `y² = x³ − x + 1`, where three points are
collinear exactly when they sum to the identity. Taking a cyclic subgroup of order `7m` and
deleting one residue class turns the whole geometric argument into elementary arithmetic in
`ZMod (7m)`: the ordinary-line graph becomes bipartite, hence `K_r`-free.

## The main theorem

[`Erdos960/Main.lean`](Erdos960/Main.lean) — verbatim:

```lean
theorem erdos960
    (r k n : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) (hn : 72 ≤ n)
    (hcurve : ∀ m : ℕ, 0 < m → Nonempty (CurveModel (ZMod (7 * m)))) :
    (n : ℝ) ^ 2 / 12 - 10 * (n : ℝ) / 3 ≤ (F r k n : ℝ)
```

`hcurve` is the hypothesis discussed above. Everything else is proved. Points worth checking,
with the full table in [`docs/statement-fidelity.md`](docs/statement-fidelity.md):

- **`ord(A)` is genuine plane geometry**, not a combinatorial stand-in: `ptsOn`, `IsLine` and
  `ordinaryLine` are defined on `ℝ × ℝ` and `AffineSubspace ℝ (ℝ × ℝ)`.
- **Finiteness of `ord` is proved, not assumed.** `Set.ncard` returns `0` on infinite sets, so
  without `ordinaryLines_finite` the bound could silently be a statement about `0`.
- **The bound is stated over `ℝ`.** `n²/12` and `10n/3` are not integers in general; `ℕ`/`ℤ`
  truncation would quietly change the claim. `F` lands in `ℤ` because the paper's degenerate
  value is `−1`.
- **All three numeric hypotheses are consumed, none decorative.** `k ≥ 4` is used by
  `noKCollinear_pts` (the construction really does contain three collinear points, so it is false
  for `k = 3`); `r ≥ 3` by `cliqueFree_of_isBipartite`; `n ≥ 72` becomes `m ≥ 12` through
  `zsmul_hgen_inj`, and weakening it to `0 < m` was measured to break two `omega` calls.
- **Anti-vacuity checks**: the bound is `192 > 0` at `n = 72`, the degenerate `F = −1` branch is
  excluded *under the main theorem's own hypotheses*, and the hypothesis `hcurve` has two
  independent witnesses for its cyclic-subgroup part (`ZMod (7m)` and `AddCircle (1:ℝ)`), so it is
  not a vacuous assumption from which anything follows.

## Verification

```bash
lake exe cache get          # ~6.7 GB of prebuilt Mathlib oleans
lake build                  # 8930 jobs, 39.4 s from a clean .lake/build
lake env lean Axioms.lean   # the audit list: 123 `#print axioms`
```

Unedited command output is in [`docs/ACCEPTANCE.md`](docs/ACCEPTANCE.md); the retirement record for
all 13 original proof obligations is in [`docs/SORRY-LEDGER.md`](docs/SORRY-LEDGER.md). Headline:

```
Build completed successfully (8930 jobs).
$ grep -c -F "declaration uses 'sorry'" build.log   → 0
$ wc -l axioms.log                                  → 123
$ grep -c -F "sorryAx" axioms.log                   → 0
```

`grep -rn sorry Erdos960/` does match twice — both are the words `` `sorry`-free `` in file-header
prose. The mechanical criterion is Lean's own `declaration uses 'sorry'` count, which is 0.

Environment: Lean `leanprover/lean4:v4.34.0`, Mathlib tag `v4.34.0`, commit
`5ed2965256430c3649e86755f9576b54eca72435`. **Do not move the pins** — the proofs are written
against that Mathlib API.

## Credit

The mathematics is due to **Boris Alexeev, Mehtaab Putterman, Mehtaab Sawhney, Mark Sellke and
Gregory Valiant** (§2 of the paper). **Prover credit belongs entirely to them.** The construction,
the lemmas, the constants and the `n ≥ 72` threshold are all theirs.

What is claimed here is the independent **formalizer credit** for the conditional development
described above — and only that.

The paper explicitly licenses parameterising away the specific curve ("while we use a specific
elliptic curve below for concreteness, any (non-degenerate) elliptic curve suffices"). It does
**not** license skipping Lemma 2.2; that omission is this repository's choice, documented above.

## Layout

```
Erdos960.lean                   root module
Erdos960/
  Defs.lean               328   §2.1 — ptsOn / IsLine / ordinaryLine / ord / G_A / F
  Curve.lean              482   CurveModel, Lemma 2.3 (proved), the `Concrete` namespace
  Combinatorial.lean      873   §2.2.2–§2.3 — elementary arithmetic in ZMod (7m), Props 2.4, 2.5
  Bridge.lean             142   geometry ⇄ group theory: edgeCount = ord
  Main.lean               213   Theorem 2.1 plus numeric anti-vacuity instances
Axioms.lean               152   the 123-line `#print axioms` audit list
docs/                           acceptance log, sorry ledger, gate-0 report, fidelity table,
                                per-phase reports, setup notes, claim draft
```

Proof skeleton, each step a numbered result in the paper:

```
collinearity criterion (HYPOTHESIS)
  ├─ no_four_collinear ............. Lemma 2.3 (proved, not assumed)
  │    └─ noKCollinear_pts ......... half of Admissible, consumes k ≥ 4
  └─ ordinaryLine_iff .............. Prop 2.4 reduction: geometry ⇄ ZMod arithmetic
       └─ edgeCount_eq_ord ......... e(G_A) = ord(A), exact halving via ordered pairs
            ├─ ord_A₀_ge ........... Prop 2.4: ord(A₀) ≥ 3m²
            ├─ Aset_bipartite ...... Prop 2.5(2): G_A bipartite ⇒ K_r-free (r ≥ 3)
            └─ ord_Aset_ge ......... Prop 2.5(3): ord(A) ≥ 3m² − 3ms
                 └─ erdos960 ....... §2.3: drop the slack 7s²/12 ⇒ n²/12 − 10n/3
```

The `Concrete` namespace in `Curve.lean` proves what Mathlib *can* support today for
`y² = x³ − x + 1`: discriminant `−368` (`= 16 ×` the paper's `−23` under Mathlib's LMFDB
normalisation), non-vanishing, non-singularity, and a full algebraic proof of Lemma 2.3 for that
curve via `Polynomial.card_roots'` rather than Bézout. The main theorem uses none of it; its
purpose is to pin the remaining gap down to exactly one step.

## Known limits

1. **`hcurve` is not proved.** This is the only mathematical gap, and it is the whole of Lemma 2.2.
2. **The concrete curve is not connected to the main theorem** — what is missing is exactly
   turning the order-`7m` subgroup of `E(ℝ)` into a `CurveModel`.
3. **`collinear_iff` is narrower than the paper's sentence** (three pairwise distinct points, no
   tangency-with-multiplicity case). Since it sits in a *hypothesis*, narrower means the assumption
   is weaker and the theorem stronger.
4. No paper or literature review is produced; the deliverable is the source and its audit.

When submitting anywhere, describe this as a **conditional formalisation**. See
[`docs/CLAIM.md`](docs/CLAIM.md) for wording that does not overstate it.

## References

- Alexeev, Putterman, Sawhney, Sellke, Valiant, *Short proofs in combinatorics, probability and
  number theory II*, [arXiv:2604.06609](https://arxiv.org/abs/2604.06609), §2.
- [Erdős Problem 960](https://www.erdosproblems.com/960)
- [`docs/GATE0.md`](docs/GATE0.md) — why the Mathlib gap was routed around instead of filled
- [`docs/statement-fidelity.md`](docs/statement-fidelity.md) — statement-by-statement comparison

## License

Apache-2.0, see [`LICENSE`](LICENSE).
