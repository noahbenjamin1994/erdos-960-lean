/-
# Erdős 960 — Theorem 2.1

The final statement, plus the numeric sanity checks that guard against a statement that
is vacuous or trivially true.

Paper (§2.1, Theorem 2.1, verbatim):

  > **Theorem 2.1.** Fix integers `r ≥ 3` and `k ≥ 4` and `n ≥ 72`. Then
  > `F_{r,k}(n) ≥ n²/12 − (10/3)·n`.

🔴 See `Curve.lean` and `README.md`: paper **Lemma 2.2** (a cyclic subgroup of order `7m`
inside `E(ℝ)`, which needs `E(ℝ) ≅ ℝ/ℤ`) together with the collinearity criterion is the
one unproved input. It enters `erdos960` as the explicit hypothesis `hcurve`, never as an
`axiom`, so `#print axioms` on every declaration here is clean and the theorem is an
honest *conditional* theorem. Paper Lemma 2.3 is **not** assumed — it is proved
(`CurveModel.no_four_collinear`).
-/

import Erdos960.Bridge

namespace Erdos960

/-! ## The construction, assembled

Given `m ≥ 12`, `s ≤ 5` and a curve model on `ZMod (7m)`, the point set `M.pts (Aset s)`
is an admissible `(6m+s)`-point configuration with at least `3m² − 3ms` ordinary lines.
This is Prop. 2.5 transported to the plane. -/

/-- **Prop. 2.5, transported to the real affine plane.**

The three components come from the three sides of the development:

  * `A.card = 6m + s` — `CurveModel.card_pts` (`emb` is injective) plus `card_Aset`;
  * `NoKCollinear A k` for `k ≥ 4` — `CurveModel.noKCollinear_pts`, i.e. paper Lemma 2.3,
    which is where the hypothesis `k ≥ 4` is consumed: the construction genuinely has
    three collinear points (a chord meets the cubic in three points), so it is admissible
    for `k = 4` and not for `k = 3`;
  * `CliqueFree r` for `r ≥ 3` — `Aset_bipartite` (paper Prop. 2.5 (2)) transported along
    `emb` to an `IsBipartiteWith` on `↥A`, then `cliqueFree_of_isBipartite`;
  * `3m² − 3ms ≤ ord A` — `ord_Aset_ge` (paper Prop. 2.5 (3)) through `edgeCount_eq_ord`. -/
theorem exists_admissible {m : ℕ} [NeZero m] (hm : 12 ≤ m) {s : ℕ} (hs : s ≤ 5)
    (M : CurveModel (ZMod (7 * m))) {r k : ℕ} (hr : 3 ≤ r) (hk : 4 ≤ k) :
    ∃ A : Finset (ℝ × ℝ),
      A.card = 6 * m + s ∧ Admissible r k A ∧
      3 * (m : ℤ) ^ 2 - 3 * m * s ≤ (ord A : ℤ) := by
  classical
  obtain ⟨P, Q, hPQ, -, hcross⟩ := Aset_bipartite hm hs
  refine ⟨M.pts (Aset (m := m) s), ?_, ⟨M.noKCollinear_pts _ k hk, ?_⟩, ?_⟩
  · rw [M.card_pts, card_Aset hm hs]
  · -- `G_A` is bipartite, hence `2`-colorable, hence `K_r`-free for `r ≥ 3`.
    refine cliqueFree_of_isBipartite (SimpleGraph.IsBipartiteWith.isBipartite
      (s := {v : ↥(M.pts (Aset (m := m) s)) | ∃ x ∈ P, M.emb x = (v : ℝ × ℝ)})
      (t := {v : ↥(M.pts (Aset (m := m) s)) | ∃ x ∈ Q, M.emb x = (v : ℝ × ℝ)}) ?_) hr
    constructor
    · -- the two halves are disjoint because `emb` is injective and `P`, `Q` are disjoint
      rw [Set.disjoint_left]
      rintro v ⟨x, hxP, hx⟩ ⟨y, hyQ, hy⟩
      have hxy : x = y := M.emb_injective (hx.trans hy.symm)
      rw [hxy] at hxP
      exact Finset.disjoint_left.mp hPQ hxP hyQ
    · -- every edge crosses, by Prop. 2.5 (2) pulled back along `emb`
      intro v w hadj
      obtain ⟨x, hxS, hx⟩ := M.mem_pts.mp (Finset.mem_coe.mpr v.2)
      obtain ⟨y, hyS, hy⟩ := M.mem_pts.mp (Finset.mem_coe.mpr w.2)
      have hne : x ≠ y := by
        intro h
        exact hadj.1 (by rw [← hx, ← hy, h])
      have hoa : ordAdj (Aset (m := m) s) x y := by
        refine ⟨hne, (M.ordinaryLine_iff (Aset (m := m) s) x y hxS hyS hne).mp ?_⟩
        rw [hx, hy]
        exact hadj.2
      rcases hcross x hxS y hyS hoa with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨⟨x, h1, hx⟩, ⟨y, h2, hy⟩⟩
      · exact Or.inr ⟨⟨x, h1, hx⟩, ⟨y, h2, hy⟩⟩
  · rw [← edgeCount_eq_ord M]
    exact ord_Aset_ge hm hs

/-! ## Theorem 2.1 -/

/-- **Theorem 2.1** (Alexeev–Putterman–Sawhney–Sellke–Valiant, arXiv:2604.06609).

For all `r ≥ 3`, `k ≥ 4` and `n ≥ 72`,

  `n²/12 − 10n/3 ≤ F_{r,k}(n)`.

The bound is stated over `ℝ` because `n²/12` and `10n/3` are not integers in general;
`F` lands in `ℤ` because of the paper's `F = −1` degenerate convention.

The proof is §2.3 verbatim: write `n = 6m + s` with `s ≤ 5` (`exists_decomp`), note
`n ≥ 72 ⇒ m ≥ 12` (`m_ge_twelve`), take the configuration of `exists_admissible`, and
discard the slack `7s²/12 + (10/3 − 2s/3)n ≥ 0` (`final_bound`).

🔴 **`hcurve` is an unproved input.** It asserts that `ZMod (7m)` carries a curve model —
paper Lemma 2.2 plus the collinearity criterion for the relevant cyclic subgroup of
`E(ℝ)`. Mathlib cannot currently supply it (Gate 0, G0-1/G0-3): there is no
`TopologicalSpace` instance on `WeierstrassCurve.Affine.Point` at all, hence no route to
`E(ℝ) ≅ ℝ/ℤ`, and no lemma connecting the group law to `Collinear`. Everything else in
this development is proved. -/
theorem erdos960
    (r k n : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) (hn : 72 ≤ n)
    (hcurve : ∀ m : ℕ, 0 < m → Nonempty (CurveModel (ZMod (7 * m)))) :
    (n : ℝ) ^ 2 / 12 - 10 * (n : ℝ) / 3 ≤ (F r k n : ℝ) := by
  -- §2.3: `n = 6m + s`, `s ≤ 5`, and `n ≥ 72` forces `m ≥ 12`.
  obtain ⟨a, s, hns, hs⟩ := exists_decomp n
  have ha : 12 ≤ a := m_ge_twelve hns hs hn
  have : NeZero a := ⟨by omega⟩
  obtain ⟨M⟩ := hcurve a (by omega)
  obtain ⟨A, hcard, hadm, hord⟩ := exists_admissible ha hs M hr hk
  have hcardn : A.card = n := by rw [hcard, hns]
  -- the construction is a witness for `F`
  have hF : (ord A : ℝ) ≤ (F r k n : ℝ) := by
    exact_mod_cast le_F hcardn hadm
  have hlow : (3 * (a : ℝ) ^ 2 - 3 * (a : ℝ) * (s : ℝ)) ≤ (ord A : ℝ) := by
    exact_mod_cast hord
  -- and the construction clears the stated bound
  have hslack := final_bound (a : ℝ) (s : ℝ) (Nat.cast_nonneg s) (by exact_mod_cast hs)
    (Nat.cast_nonneg a)
  have hnr : (n : ℝ) = 6 * (a : ℝ) + (s : ℝ) := by rw [hns]; push_cast; ring
  rw [hnr]
  linarith

/-! ## Anti-vacuity: numeric instances

A formalized statement can be worthless in two ways — contradictory hypotheses, or a
conclusion that holds trivially. These checks rule both out at `n = 72`. -/

section Sanity

/-- The hypotheses of `erdos960` are jointly satisfiable at `r = 3`, `k = 4`, `n = 72`:
`3 ≤ 3`, `4 ≤ 4`, `72 ≤ 72` all hold. So the theorem is not vacuous through its numeric
hypotheses. (`hcurve` is discussed in `Curve.lean`; it is consistent because it is true
of the actual elliptic curve.) -/
example : 3 ≤ 3 ∧ 4 ≤ 4 ∧ 72 ≤ 72 := by norm_num

/-- At `n = 72` the bound reads `F_{r,k}(72) ≥ 192`. Paper: `n = 72` means `m = 12`,
`s = 0`, and `3m² = 3·144 = 432` — consistent with, and stronger than, the stated
`n²/12 − 10n/3 = 432 − 240 = 192`. -/
theorem bound_at_72 : ((72 : ℕ) : ℝ) ^ 2 / 12 - 10 * ((72 : ℕ) : ℝ) / 3 = 192 := by
  norm_num

/-- **The bound is positive at `n = 72`**, so the conclusion is a genuine constraint and
not something every `F` satisfies for free. In particular it is not implied by
`F ≥ -1` (the degenerate value) nor by `F ≥ 0`. -/
theorem bound_pos_at_72 : 0 < ((72 : ℕ) : ℝ) ^ 2 / 12 - 10 * ((72 : ℕ) : ℝ) / 3 := by
  rw [bound_at_72]; norm_num

/-- The bound the *construction* gives at `m = 12`, `s = 0`: `3m² − 3ms = 432`. -/
theorem construction_at_72 : 3 * (12 : ℤ) ^ 2 - 3 * 12 * 0 = 432 := by norm_num

/-- And `432 ≥ 192`: the construction clears the stated bound with room to spare, which
is the slack `7s²/12` plus `(10/3 − 2s/3)n` that §2.3 discards. -/
theorem construction_clears_bound :
    ((72 : ℕ) : ℝ) ^ 2 / 12 - 10 * ((72 : ℕ) : ℝ) / 3 ≤ (432 : ℝ) := by
  rw [bound_at_72]; norm_num

/-- `n = 72` really does decompose as `6·12 + 0` with `s ≤ 5`, and `m = 12` meets the
`m ≥ 12` threshold of §2.2.3 exactly — `n ≥ 72` is tight for this construction. -/
theorem decomp_at_72 : (72 : ℕ) = 6 * 12 + 0 ∧ (0 : ℕ) ≤ 5 ∧ 12 ≤ 12 := by norm_num

/-- A second instance, `n = 73` (`m = 12`, `s = 1`), where the `−3ms` term is live:
construction gives `3·144 − 3·12·1 = 396`, bound asks for `73²/12 − 730/3 ≈ 200.7`. -/
theorem decomp_at_73 : (73 : ℕ) = 6 * 12 + 1 ∧ (1 : ℕ) ≤ 5 := by norm_num

theorem construction_at_73 : 3 * (12 : ℤ) ^ 2 - 3 * 12 * 1 = 396 := by norm_num

theorem bound_at_73_lt_construction :
    ((73 : ℕ) : ℝ) ^ 2 / 12 - 10 * ((73 : ℕ) : ℝ) / 3 < (396 : ℝ) := by
  norm_num

/-- `ordValues` is the set `F` takes its supremum over. For the statement to be
non-trivial we need `F` to not be stuck at the degenerate `−1`; that follows from
`exists_admissible`, which exhibits a member of `ordValues`. -/
theorem ordValues_nonempty_of_admissible {r k n : ℕ} {A : Finset (ℝ × ℝ)}
    (hcard : A.card = n) (hadm : Admissible r k A) : (ordValues r k n).Nonempty :=
  ⟨ord A, A, hcard, hadm, rfl⟩

/-- Consequently, under the theorem's hypotheses `F r k n ≠ -1`: the construction rules
out the degenerate branch. This is the precise sense in which `r ≥ 3` and `k ≥ 4` avoid
the paper's three degenerate cases (`k = 2`, `k = 3`, `r = 2`). -/
theorem F_ne_neg_one_of_admissible {r k n : ℕ} {A : Finset (ℝ × ℝ)}
    (hcard : A.card = n) (hadm : Admissible r k A) : F r k n ≠ -1 := by
  rw [F_eq_sSup (ordValues_nonempty_of_admissible hcard hadm)]
  omega

/-- The degenerate branch really is ruled out under the hypotheses of `erdos960`: from a
curve model one gets an admissible configuration, so `F_{r,k}(n) ≠ −1`. -/
theorem F_ne_neg_one_of_erdos960_hyps
    (r k n : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) (hn : 72 ≤ n)
    (hcurve : ∀ m : ℕ, 0 < m → Nonempty (CurveModel (ZMod (7 * m)))) :
    F r k n ≠ -1 := by
  obtain ⟨a, s, hns, hs⟩ := exists_decomp n
  have ha : 12 ≤ a := m_ge_twelve hns hs hn
  have : NeZero a := ⟨by omega⟩
  obtain ⟨M⟩ := hcurve a (by omega)
  obtain ⟨A, hcard, hadm, -⟩ := exists_admissible ha hs M hr hk
  exact F_ne_neg_one_of_admissible (by rw [hcard, hns]) hadm

end Sanity

/-! ## The assumption, named

`CurveModelAssumption` (`Curve.lean`) is exactly the hypothesis `hcurve` of `erdos960`,
one `m` at a time. Recorded so that the credit claim in `README.md` can point at a single
definition rather than at a hypothesis buried in a signature. -/

theorem erdos960_of_curveModelAssumption
    (r k n : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) (hn : 72 ≤ n)
    (hcurve : ∀ m : ℕ, 0 < m → CurveModelAssumption m) :
    (n : ℝ) ^ 2 / 12 - 10 * (n : ℝ) / 3 ≤ (F r k n : ℝ) :=
  erdos960 r k n hr hk hn hcurve

end Erdos960
