# Draft issue — JSP-000799 (Erdős 960)

**⚠ This is deliberately not a `[Recipient]` claim.**

The development is a **conditional** formalization: the paper's Lemma 2.2 is an explicit
hypothesis in the main theorem's signature. A formalizer claim on JSP-000799 asserts that an
existing proof has been turned into a machine-checkable proof, and that is not yet true here.
Posting this as `[Recipient]` would overstate the work, and the awards repository has already
asked for one claim to be withdrawn for misrepresenting what was formalized.

Two honest options:

1. **Close the gap first** — prove `CurveModelAssumption`, i.e. construct an order-`7m` cyclic
   subgroup of `E(ℝ)` inside the plane with collinearity given by the group law. This means
   giving `WeierstrassCurve.Affine.Point` a topology and reaching `E(ℝ) ≅ ℝ/ℤ`, none of which
   exists in Mathlib today (see [`GATE0.md`](GATE0.md)). Then claim normally.
2. **Publish as-is, without claiming** — announce the conditional development, state the gap in
   the first paragraph, and invite someone to close it. Establishes a public timestamp on the
   combinatorial 95% without asserting something untrue.

Draft text for option 2 follows.

---

**Title:** `Conditional Lean 4 formalization of Erdős 960 / JSP-000799 (Lemma 2.2 still assumed)`

**Body:**

Posting this for the record rather than as a claim: the formalization is **conditional** and I am
not asserting that JSP-000799 has been formalized.

### What exists

A Lean 4 development of Theorem 2.1 of Alexeev–Putterman–Sawhney–Sellke–Valiant,
*Short proofs in combinatorics, probability and number theory II*, arXiv:2604.06609, §2:

```lean
theorem erdos960
    (r k n : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) (hn : 72 ≤ n)
    (hcurve : ∀ m : ℕ, 0 < m → Nonempty (CurveModel (ZMod (7 * m)))) :
    (n : ℝ) ^ 2 / 12 - 10 * (n : ℝ) / 3 ≤ (F r k n : ℝ)
```

Repository: https://github.com/noahbenjamin1994/erdos-960-lean. Lean `v4.34.0`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Zero `sorry`; all 123 exported declarations audit to `propext` / `Classical.choice` / `Quot.sound`;
builds in 39.4 s from a clean `.lake/build` (8930 jobs). Unedited command output is in
`docs/ACCEPTANCE.md`.

### What is assumed, and why

`hcurve` is the paper's Lemma 2.2 plus the collinearity criterion: a cyclic group of order `7m`
embeds in `ℝ²` so that three distinct points are collinear exactly when they sum to zero. It is
neither an `axiom` nor a `sorry` — it is a hypothesis in the signature, visible to any reader, and
the axiom audit stays clean precisely because nothing is asserted.

The paper obtains it from `E(ℝ)` being connected, hence isomorphic to the circle group. Mathlib has
no `TopologicalSpace` instance on `WeierstrassCurve.Affine.Point` at all, no Lie-group theory for
it, and no uniformization `ℂ/Λ ≅ E(ℂ)`; the search is logged in `docs/GATE0.md`. Filling this step
means building that theory.

Everything downstream of the assumption is proved: Proposition 2.4, Proposition 2.5, the bipartite
ordinary-line graph, `e(G_A) = ord(A)`, and the final bound. Lemma 2.3 (no four collinear points)
is **proved**, not assumed, from the collinearity criterion alone. For the concrete curve
`y² = x³ − x + 1` the repository also proves the discriminant is `−368` (Mathlib's LMFDB
normalization of the paper's `−23`), non-singularity, and Lemma 2.3 algebraically via
`Polynomial.card_roots'`; none of that is used by the main theorem — its purpose is to pin the gap
to exactly one step.

### Credit

The mathematics is entirely due to Alexeev, Putterman, Sawhney, Sellke and Valiant. Prover credit
belongs to them. Nothing new is contributed mathematically, and no prize claim is made here.

If someone closes the `E(ℝ) ≅ ℝ/ℤ` gap in Mathlib, this development plugs into it directly.

---

## Pre-submission checklist

- [ ] Decide between option 1 (close the gap, then claim) and option 2 (publish, do not claim).
- [ ] If option 2: keep "conditional" in the title and in the first sentence. Do not describe it as
      a formalization of Theorem 2.1.
- [x] Pushed public 2026-09-18T04:05Z. No issue posted anywhere for this problem yet.
- [ ] Re-check the competition state: JSP issues for 000799, GitHub repos matching `jsp-000799-*`,
      and `formal-conjectures` issue #1037 (still open; statement PR #5872 was closed).
- [ ] Post on its own. Do not batch it with other problems.
