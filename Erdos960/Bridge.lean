/-
# Erdős 960 — the geometry ⇄ group-law bridge

`Combinatorial.lean` is the `ZMod (7m)` side and is `sorry`-free; this file holds the
single *geometric* step that connects it to the paper's `ord`. Split out of
`Combinatorial.lean` in step 4 so that the file boundary matches the obligation boundary;
proved in step 5.

`edgeCount_eq_ord` routes both counts through one intermediate `Finset` of *ordered*
plane pairs, `ordPairs A`:

  * the group side `S.offDiag.filter (ordAdj S)` maps onto it by `(x, y) ↦ (emb x, emb y)`,
    a bijection by `CurveModel.ordinaryLine_iff` (the chord construction) plus injectivity
    of `emb`;
  * the graph side `univ.filter ((ordGraph A).Adj)` maps onto it by `(P, Q) ↦ (↑P, ↑Q)`,
    a bijection because the vertex type of `ordGraph A` is literally `↥A`.

Both maps are *total* functions of their arguments, so no dependent `Finset.card_bij` is
needed. Mathlib's `two_mul_card_edgeFinset` then turns the graph-side ordered count into
`2 · e(G_A)`, and `card_edgeFinset_ordGraph` (`Defs.lean`) turns `e(G_A)` into `ord A`.
Halving is exact by construction, so the `/2` in `edgeCount` disappears with no parity
argument.
-/

import Erdos960.Combinatorial

-- `edgeCount_eq_ord` keeps `[NeZero m]` in its signature (it is the statement recorded in
-- `SORRY-LEDGER.md`, unchanged) even though the finished proof does not consume it.
set_option linter.unusedSectionVars false

namespace Erdos960

-- `ordinaryLine` and `ordAdj` are not decidable predicates; every `Finset.filter` in this
-- file is over one of them. Opening `Classical` once, rather than invoking the `classical`
-- tactic inside each proof, keeps a *single* `Decidable` instance in play — otherwise the
-- instance baked into `ordPairs` and the one a local `classical` introduces differ
-- syntactically and `rw` cannot match them.
open scoped Classical

/-! ## An instance-free edge count

`SimpleGraph.edgeFinset` carries a `Fintype G.edgeSet` instance argument, and the one
Mathlib synthesizes inside `two_mul_card_edgeFinset` (from `Fintype V` + `DecidableRel
G.Adj`) is not syntactically the `instFintypeOrdGraphEdgeSet` of `Defs.lean`. Both give
the same number — `Fintype` is a subsingleton — but `rw` cannot see that. Passing through
`Set.ncard`, which takes no instance at all, sidesteps the mismatch. -/

theorem card_edgeFinset_eq_ncard {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeFinset.card = G.edgeSet.ncard :=
  (Set.ncard_eq_toFinset_card' _).symm

/-! ## Ordered ordinary pairs of a plane point set

The common intermediate. This is an *ordered* count: each ordinary line of `A` contributes
exactly its two orderings, which is what makes the total equal `2 · ord A`. -/

/-- The ordered pairs of distinct `A`-points spanning an ordinary line of `A`. -/
noncomputable def ordPairs (A : Finset (ℝ × ℝ)) : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (A ×ˢ A).filter fun p => p.1 ≠ p.2 ∧ ordinaryLine A line[ℝ, p.1, p.2]

theorem mem_ordPairs {A : Finset (ℝ × ℝ)} {p : (ℝ × ℝ) × (ℝ × ℝ)} :
    p ∈ ordPairs A ↔
      p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2 ∧ ordinaryLine A line[ℝ, p.1, p.2] := by
  simp only [ordPairs, Finset.mem_filter, Finset.mem_product]
  tauto

/-- **The graph side.** `|ordPairs A| = 2 · e(G_A)`: the ordered pairs of adjacent
vertices of `G_A` are exactly `ordPairs A`, read through the coercion `↥A → ℝ × ℝ`. -/
theorem card_ordPairs_eq_two_mul (A : Finset (ℝ × ℝ)) :
    (ordPairs A).card = 2 * (ordGraph A).edgeSet.ncard := by
  classical
  have h2 := SimpleGraph.two_mul_card_edgeFinset (ordGraph A)
  rw [card_edgeFinset_eq_ncard] at h2
  rw [h2]
  refine (Finset.card_nbij (fun p : ↥A × ↥A => ((p.1 : ℝ × ℝ), (p.2 : ℝ × ℝ))) ?_ ?_ ?_).symm
  · rintro ⟨P, Q⟩ hPQ
    have hadj : (ordGraph A).Adj P Q := by
      simpa only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_coe,
        Finset.mem_filter, Finset.mem_univ, true_and] using hPQ
    exact Finset.mem_coe.mpr (mem_ordPairs.mpr ⟨P.2, Q.2, hadj.1, hadj.2⟩)
  · rintro ⟨P, Q⟩ - ⟨P', Q'⟩ - heq
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (Subtype.ext heq.1) (Subtype.ext heq.2)
  · rintro ⟨u, v⟩ huv
    obtain ⟨huA, hvA, huv', hline⟩ := mem_ordPairs.mp (Finset.mem_coe.mp huv)
    refine ⟨((⟨u, huA⟩ : ↥A), (⟨v, hvA⟩ : ↥A)), ?_, rfl⟩
    simpa only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_univ, true_and] using
      (show (ordGraph A).Adj ⟨u, huA⟩ ⟨v, hvA⟩ from ⟨huv', hline⟩)

variable {m : ℕ}

/-- **The group side.** Under a curve model, `(x, y) ↦ (emb x, emb y)` is a bijection from
the ordered `ordAdj`-pairs of `S` onto `ordPairs (M.pts S)`.

Injectivity is `emb_injective`; surjectivity is `mem_pts`; the two membership conditions
match by `CurveModel.ordinaryLine_iff`, whose right-hand side is *definitionally* the
disjunction in `ordAdj` (`third x y` unfolds to `-(x + y)`). -/
theorem card_filter_ordAdj_eq (M : CurveModel (ZMod (7 * m))) (S : Finset (ZMod (7 * m))) :
    haveI := Classical.decPred fun p : ZMod (7 * m) × ZMod (7 * m) => ordAdj S p.1 p.2
    (S.offDiag.filter fun p => ordAdj S p.1 p.2).card = (ordPairs (M.pts S)).card := by
  classical
  refine Finset.card_nbij (fun p => (M.emb p.1, M.emb p.2)) ?_ ?_ ?_
  · rintro ⟨x, y⟩ hxy
    obtain ⟨hoff, hadj⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hxy)
    obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hoff
    refine Finset.mem_coe.mpr (mem_ordPairs.mpr ⟨?_, ?_, M.emb_ne hne, ?_⟩)
    · exact Finset.mem_coe.mp (M.mem_pts.mpr ⟨x, hx, rfl⟩)
    · exact Finset.mem_coe.mp (M.mem_pts.mpr ⟨y, hy, rfl⟩)
    · exact (M.ordinaryLine_iff S x y hx hy hne).mpr hadj.2
  · rintro ⟨x, y⟩ - ⟨x', y'⟩ - heq
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (M.emb_injective heq.1) (M.emb_injective heq.2)
  · rintro ⟨u, v⟩ huv
    obtain ⟨huA, hvA, huv', hline⟩ := mem_ordPairs.mp (Finset.mem_coe.mp huv)
    obtain ⟨x, hx, rfl⟩ := M.mem_pts.mp (Finset.mem_coe.mpr huA)
    obtain ⟨y, hy, rfl⟩ := M.mem_pts.mp (Finset.mem_coe.mpr hvA)
    have hne : x ≠ y := fun h => huv' (congrArg M.emb h)
    refine ⟨(x, y), ?_, rfl⟩
    refine Finset.mem_coe.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hx, hy, hne⟩, hne, ?_⟩)
    exact (M.ordinaryLine_iff S x y hx hy hne).mp hline

variable [NeZero m]

/-- **`edgeCount S = ord (M.pts S)`.** The link that converts the combinatorial bound
`ord_Aset_ge` into a bound on the paper's `ord`.

Paper §2.1, verbatim: "so that `e(G_A) = ord(A)`"; §2.2.2 then counts `ord` on the group
side. The chain is

  `edgeCount S = |ordAdj-pairs| / 2 = |ordPairs (M.pts S)| / 2 = 2·e(G_A) / 2 = ord (M.pts S)`.

The division is exact because `ordPairs` is an *ordered* count. -/
theorem edgeCount_eq_ord (M : CurveModel (ZMod (7 * m))) (S : Finset (ZMod (7 * m))) :
    edgeCount S = ord (M.pts S) := by
  classical
  rw [edgeCount, card_filter_ordAdj_eq M S, card_ordPairs_eq_two_mul,
    ← card_edgeFinset_eq_ncard, card_edgeFinset_ordGraph]
  omega

end Erdos960
