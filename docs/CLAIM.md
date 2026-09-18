# Draft claim — JSP-000799 (Erdős 960)

**Posted 2026-09-18 as [TheJustinSunPrize/awards#1041](https://github.com/TheJustinSunPrize/awards/issues/1041).**

> Earlier versions of this file argued **against** claiming, because the paper's Lemma 2.2 was
> an explicit hypothesis of the main theorem, which made the development conditional. That gap
> is now closed: `Erdos960.curveModelAssumption` proves it, and
> `Erdos960.erdos960_unconditional` carries no hypothesis beyond the paper's own numeric ones.

---

**Title:** `[Award claim] JSP-000799 Lean formalization`

**Body:**

**Problem link:** https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000799

**Original Lean proof repository:** https://github.com/noahbenjamin1994/erdos-960-lean

**Follow-up contact email:** noahbenjamin1994@gmail.com

**Contribution being claimed:** Lean formalization

**Identity verification method:** Lean only. The repository is owned by this submitting account
and all commits are from it. Happy to follow any additional check the maintainers prefer.

### What is being claimed

A Lean 4 formalization of Theorem 2.1 of Alexeev, Putterman, Sawhney, Sellke and Valiant,
*Short proofs in combinatorics, probability and number theory II*, arXiv:2604.06609, §2, which
answers Erdős 960 in the negative.

The mathematics belongs entirely to those five authors. **Prover credit is theirs; this claim
is for formalizer credit only.** No new mathematics is contributed.

### The formalized statement

```lean
theorem erdos960_unconditional (r k n : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) (hn : 72 ≤ n) :
    (n : ℝ) ^ 2 / 12 - 10 * (n : ℝ) / 3 ≤ (F r k n : ℝ)
```

`F r k n` is the paper's `F_{r,k}(n)`, defined in `Erdos960/Defs.lean` as genuine plane
geometry: `ptsOn`, `IsLine` and `ordinaryLine` live on `ℝ × ℝ` and `AffineSubspace ℝ (ℝ × ℝ)`,
and `ord A` is the `Set.ncard` of the ordinary lines of `A`. `formal-conjectures` has no
statement for this problem, so the statement is ours and its fidelity is our own risk;
`docs/statement-fidelity.md` compares it with the paper clause by clause. Four points a
reviewer is most likely to probe:

- **Finiteness of `ord` is proved, not assumed** (`ordinaryLines_finite`). `Set.ncard` returns
  `0` on infinite sets, so without it the bound could silently be a claim about `0`.
- **The bound is stated over `ℝ`.** `n²/12` and `10n/3` are not integers in general, and `ℕ` or
  `ℤ` truncation would change the claim. `F` lands in `ℤ` because the paper's degenerate value
  is `−1`, and that branch is excluded under the theorem's own hypotheses.
- **All three numeric hypotheses are consumed.** `k ≥ 4` is used by `noKCollinear_pts`, and is
  false for `k = 3` since the construction does contain three collinear points; `r ≥ 3` by
  `cliqueFree_of_isBipartite`; `n ≥ 72` becomes `m ≥ 12` through `zsmul_hgen_inj`, and
  weakening it to `0 < m` was measured to break two `omega` calls.
- **Anti-vacuity.** The bound is `192 > 0` at `n = 72`, so the statement is not satisfied
  trivially.

### One deliberate departure from the paper: the curve

The paper builds its point configuration on the smooth curve `y² = x³ − x + 1` and obtains
cyclic subgroups of every order from `E(ℝ)` being connected, hence `E(ℝ) ≅ ℝ/ℤ`. That route is
unavailable in Mathlib today: there is no `TopologicalSpace` instance on
`WeierstrassCurve.Affine.Point`, no Lie theory for it, and no uniformization `ℂ/Λ ≅ E(ℂ)`. The
search is logged in `docs/GATE0.md`.

The counting argument does not need the specific curve, and the paper says so in §2.2: "while
we use a specific elliptic curve below for concreteness, any (non-degenerate) elliptic curve
suffices". What it needs is packaged as `CurveModel`: an injection of the group into the plane
under which three pairwise distinct points are collinear exactly when they sum to zero.

This repository supplies such a model on the **nodal** cubic `Z(X² + Y²) = X³`, which has an
acnode at `[0 : 0 : 1]`, so its real smooth locus is a circle and it carries cyclic subgroups of
every order. Parametrised by an angle, `Pt φ = (cos (φ + π/6), sin (φ + π/6), cos (φ + π/6)^3)`,
everything reduces to one identity:

```
det3 (Pt a) (Pt b) (Pt c) = sin (b - a) * sin (c - a) * sin (c - b) * sin (a + b + c)
```

so collinearity is `a + b + c ≡ 0 (mod π)`, and `φ = k·π/N` gives `ZMod N`. Two details matter:
the `π/6` shift puts the origin of the group law at an inflection point, without which the
criterion reads `≡ π/2`; and the affine chart is chosen after the subgroup, by dividing by the
linear form through reference points at angles `π/(4N)` and `2π/(4N)`, since for even `N` one
group point would otherwise sit on the line at infinity. The reference line meets the cubic at
angles whose numerators are `1`, `2` and `−3`, none divisible by `4`, so no `kπ/N` lands on it.

This is stated plainly rather than buried: **the bound proved is the paper's Theorem 2.1, but
the witnessing configuration is on a different cubic than the paper's.** The proof uses no
topology, no Lie groups and no uniformization.

The repository also contains a `Concrete` namespace proving what Mathlib does support for the
paper's own curve, namely discriminant `−368` (`= 16 ×` the paper's `−23` under Mathlib's LMFDB
normalization), non-singularity, and Lemma 2.3 for it via `Polynomial.card_roots'`. The main
theorem does not use it, and it is not claimed as part of the result.

Lemma 2.3 of the paper, no four collinear points, is a **theorem** here rather than an
assumption: it follows from the collinearity criterion by cancellation alone.

### How to verify

```bash
lake exe cache get
lake build                  # 8931 jobs
lake env lean Axioms.lean   # 133 `#print axioms`
```

- Zero `sorry`, no custom `axiom`, no `native_decide`, no `Lean.ofReduceBool`.
- All 133 audited declarations report only `propext`, `Classical.choice`, `Quot.sound`. Several
  report fewer, which is stronger.
- Raw output of a clean rebuild is committed in `verification/`: `build.log`, `axioms.log`,
  `scan.log` and `CHECKSUMS.txt`, so the numbers above can be diffed rather than trusted.
- `grep -rn sorry Erdos960/` matches twice, both times the words `` `sorry`-free `` in
  file-header prose. The mechanical criterion is Lean's own `declaration uses 'sorry'` count,
  which is 0.

Environment: Lean `leanprover/lean4:v4.34.0`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, both pinned in the repository.

### Related claims, attribution questions and conflicts

None. A competition check found no claim issue for JSP-000799, no public GitHub repository
formalizing this problem, and no open `formal-conjectures` PR; its statement PR #5872 was closed
and issue #1037 is still open. No co-contributors, and no professional relationship with the
paper's authors.

### Applicant declarations

- [x] I am applying for my own contribution using my own GitHub account, and am acting for no
      one else.
- [x] My claim concerns my own contribution to the Lean proof referenced in the identified
      problem bank entry. Attribution points that need review are identified above.
- [x] I have disclosed related claims and attribution conflicts and will complete the
      maintainer's contribution and identity verification before claiming payment.

---

## Pre-submission checklist

- [x] Lemma 2.2 proved, so the main theorem is unconditional.
- [x] Clean rebuild verified locally; evidence committed under `verification/`.
- [x] Repository pushed before posting, so the claim points at the unconditional theorem.
- [x] The curve departure is stated in the claim body, in its own section.
- [x] Competition state checked 2026-09-18 just before posting: nothing on any of the three
      channels.
- [x] Posted on its own.
