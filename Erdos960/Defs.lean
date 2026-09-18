/-
# Erdős Problem 960 — definitions

Formalization of the definitions of §2.1 of

  B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, G. Valiant,
  *Short proofs in combinatorics, probability and number theory II*, arXiv:2604.06609,

namely `ord(A)`, the ordinary-line graph `G_A`, and the extremal function `F_{r,k}(n)`
whose lower bound is Theorem 2.1.

Everything in this file is stated for genuine point sets in the real affine plane
`ℝ × ℝ` and genuine affine lines, so that the final theorem is a statement about the
quantity the paper defines and not about a combinatorial surrogate.

The mathematical content is due to the authors above; this file claims only the
formalization.
-/

import Mathlib

namespace Erdos960

/-! ## Lines in the real affine plane -/

/-- `IsLine L` says the affine subspace `L ≤ ℝ²` is an (affine) line: it is spanned by
two distinct points.

Paper (§2.1) speaks of "lines `ℓ` in `ℝ²`" without further comment. Taking a line to be
an affine subspace spanned by two distinct points is the standard reading and rules out
both the empty subspace and single points, which would otherwise be swept up by
`Collinear`. -/
def IsLine (L : AffineSubspace ℝ (ℝ × ℝ)) : Prop :=
  ∃ p q : ℝ × ℝ, p ≠ q ∧ L = line[ℝ, p, q]

/-- The points of `A` lying on `L`, as a set. -/
def ptsOn (A : Finset (ℝ × ℝ)) (L : AffineSubspace ℝ (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  (A : Set (ℝ × ℝ)) ∩ (L : Set (ℝ × ℝ))

theorem ptsOn_finite (A : Finset (ℝ × ℝ)) (L : AffineSubspace ℝ (ℝ × ℝ)) :
    (ptsOn A L).Finite :=
  (A.finite_toSet).subset Set.inter_subset_left

theorem ptsOn_subset (A : Finset (ℝ × ℝ)) (L : AffineSubspace ℝ (ℝ × ℝ)) :
    ptsOn A L ⊆ (A : Set (ℝ × ℝ)) := Set.inter_subset_left

/-- `line[ℝ, p, q]` does not depend on the order of `p` and `q`. -/
theorem line_comm (p q : ℝ × ℝ) : line[ℝ, p, q] = line[ℝ, q, p] :=
  congrArg (affineSpan ℝ) (Set.pair_comm p q)

/-- A line, as a point set, is collinear.

(Mathlib states `Collinear` for sets of points but has no lemma for the carrier of an
`AffineSubspace` that happens to be a line. Moved here from `Curve.lean` in step 5 so
that `Defs.lean` can use it; the statement is unchanged.) -/
theorem collinear_coe_of_isLine {L : AffineSubspace ℝ (ℝ × ℝ)} (hL : IsLine L) :
    Collinear ℝ (L : Set (ℝ × ℝ)) := by
  obtain ⟨p, q, -, rfl⟩ := hL
  rw [Collinear, ← AffineSubspace.direction_eq_vectorSpan, direction_affineSpan]
  exact collinear_pair ℝ p q

/-- **A line is determined by any two distinct points on it.**

This is the fact that makes `ord` finite and makes "the line through the two `A`-points
on it" a well-defined inverse to "the pair of `A`-points on a line". -/
theorem IsLine.eq_line_of_mem {L : AffineSubspace ℝ (ℝ × ℝ)} (hL : IsLine L)
    {p q : ℝ × ℝ} (hp : p ∈ (L : Set (ℝ × ℝ))) (hq : q ∈ (L : Set (ℝ × ℝ)))
    (hpq : p ≠ q) : L = line[ℝ, p, q] :=
  (((collinear_coe_of_isLine hL).affineSpan_eq_of_ne hp hq hpq).trans
    (AffineSubspace.affineSpan_coe L)).symm

/-! ## Ordinary lines and `ord` -/

/-- `ordinaryLine A L`: `L` is an *ordinary line* of `A`, i.e. a line meeting `A` in
exactly two points.

Paper (§2.1), verbatim: "let `ord(A)` denote the number of lines `ℓ` with
`|ℓ ∩ A| = 2`". -/
def ordinaryLine (A : Finset (ℝ × ℝ)) (L : AffineSubspace ℝ (ℝ × ℝ)) : Prop :=
  IsLine L ∧ (ptsOn A L).ncard = 2

/-- The set of ordinary lines of `A`. -/
def ordinaryLines (A : Finset (ℝ × ℝ)) : Set (AffineSubspace ℝ (ℝ × ℝ)) :=
  {L | ordinaryLine A L}

theorem mem_ordinaryLines {A : Finset (ℝ × ℝ)} {L : AffineSubspace ℝ (ℝ × ℝ)} :
    L ∈ ordinaryLines A ↔ ordinaryLine A L := Iff.rfl

/-- A two-element `ptsOn` set is pinned down by any two distinct members. -/
theorem ptsOn_eq_pair_of_mem {A : Finset (ℝ × ℝ)} {L : AffineSubspace ℝ (ℝ × ℝ)}
    (hcard : (ptsOn A L).ncard = 2) {p q : ℝ × ℝ} (hp : p ∈ ptsOn A L) (hq : q ∈ ptsOn A L)
    (hpq : p ≠ q) : ptsOn A L = ({p, q} : Set (ℝ × ℝ)) := by
  refine (Set.eq_of_subset_of_ncard_le ?_ ?_ (ptsOn_finite A L)).symm
  · exact Set.insert_subset_iff.mpr ⟨hp, Set.singleton_subset_iff.mpr hq⟩
  · rw [hcard, Set.ncard_pair hpq]

/-- **The two `A`-points on an ordinary line**, together with the fact that they span it.
Paper (§2.1): an ordinary line is "a line `ℓ` with `|ℓ ∩ A| = 2`", so it comes with a
distinguished pair of `A`-points, and by `IsLine.eq_line_of_mem` it is their span. -/
theorem ordinaryLine.exists_pair {A : Finset (ℝ × ℝ)} {L : AffineSubspace ℝ (ℝ × ℝ)}
    (hL : ordinaryLine A L) :
    ∃ p q : ℝ × ℝ, p ∈ A ∧ q ∈ A ∧ p ≠ q ∧
      ptsOn A L = ({p, q} : Set (ℝ × ℝ)) ∧ L = line[ℝ, p, q] := by
  obtain ⟨p, q, hpq, hset⟩ := Set.ncard_eq_two.mp hL.2
  have hp : p ∈ ptsOn A L := by rw [hset]; exact Set.mem_insert _ _
  have hq : q ∈ ptsOn A L := by rw [hset]; exact Set.mem_insert_of_mem _ rfl
  exact ⟨p, q, Finset.mem_coe.mp hp.1, Finset.mem_coe.mp hq.1, hpq, hset,
    hL.1.eq_line_of_mem hp.2 hq.2 hpq⟩

/-- **`L ↦ ℓ ∩ A` is injective on ordinary lines.** Two ordinary lines carrying the same
pair of `A`-points coincide, because each is the span of that pair. This is the engine
behind both `ordinaryLines_finite` and `ord_le_choose`. -/
theorem ptsOn_injOn (A : Finset (ℝ × ℝ)) :
    Set.InjOn (fun L => ptsOn A L) (ordinaryLines A) := by
  intro L hL L' hL' heq
  have heq' : ptsOn A L = ptsOn A L' := heq
  obtain ⟨p, q, -, -, hpq, hset, hLeq⟩ := ordinaryLine.exists_pair hL
  have hp' : p ∈ ptsOn A L' := by rw [← heq', hset]; exact Set.mem_insert _ _
  have hq' : q ∈ ptsOn A L' := by rw [← heq', hset]; exact Set.mem_insert_of_mem _ rfl
  rw [hLeq, hL'.1.eq_line_of_mem hp'.2 hq'.2 hpq]

/-- An ordinary line of `A` is spanned by the two points of `A` on it; hence there are
at most `A.card.choose 2` of them and the set is finite.

This is what makes `ord` below (defined via `Set.ncard`, which returns `0` on infinite
sets) mean what it should. -/
theorem ordinaryLines_finite (A : Finset (ℝ × ℝ)) : (ordinaryLines A).Finite := by
  refine Set.Finite.of_finite_image ?_ (ptsOn_injOn A)
  refine (A.finite_toSet.finite_subsets).subset ?_
  rintro s ⟨L, -, rfl⟩
  exact ptsOn_subset A L

/-- `ord A`, the number of ordinary lines of `A`. -/
noncomputable def ord (A : Finset (ℝ × ℝ)) : ℕ := (ordinaryLines A).ncard

/-- `ord A ≤ A.card.choose 2`: each ordinary line is determined by the pair of `A`-points
on it. Needed to know `F` below is a supremum of a bounded set. -/
theorem ord_le_choose (A : Finset (ℝ × ℝ)) : ord A ≤ A.card.choose 2 := by
  classical
  rw [ord, ← Finset.card_powersetCard 2 A, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn (fun L => (ptsOn_finite A L).toFinset) ?_ ?_
    (Finset.finite_toSet _)
  · intro L hL
    refine Finset.mem_coe.mpr (Finset.mem_powersetCard.mpr ⟨?_, ?_⟩)
    · exact Set.Finite.toFinset_subset.mpr (ptsOn_subset A L)
    · rw [← Set.ncard_eq_toFinset_card _ (ptsOn_finite A L)]
      exact hL.2
  · intro L hL L' hL' heq
    exact ptsOn_injOn A hL hL' (Set.Finite.toFinset_inj.mp heq)

/-! ## The ordinary-line graph -/

/-- The *ordinary-line graph* `G_A` on the vertex set `A`.

Paper (§2.1), verbatim: "`V(G_A) = A` and `{p, q} ∈ E(G_A)` if and only if
`|ℓ_pq ∩ A| = 2`", where `ℓ_pq` is the line through `p` and `q`. -/
noncomputable def ordGraph (A : Finset (ℝ × ℝ)) : SimpleGraph ↥A where
  Adj p q := (p : ℝ × ℝ) ≠ (q : ℝ × ℝ) ∧ ordinaryLine A line[ℝ, (p : ℝ × ℝ), (q : ℝ × ℝ)]
  symm := ⟨fun p q h => ⟨h.1.symm, by rw [line_comm]; exact h.2⟩⟩
  loopless := ⟨fun p h => h.1 rfl⟩

theorem ordGraph_adj_iff {A : Finset (ℝ × ℝ)} {p q : ↥A} :
    (ordGraph A).Adj p q ↔
      (p : ℝ × ℝ) ≠ (q : ℝ × ℝ) ∧ ordinaryLine A line[ℝ, (p : ℝ × ℝ), (q : ℝ × ℝ)] :=
  Iff.rfl

noncomputable instance instFintypeOrdGraphEdgeSet (A : Finset (ℝ × ℝ)) :
    Fintype (ordGraph A).edgeSet :=
  Fintype.ofFinite _

/-- The line spanned by an edge of `ordGraph A`. Well defined on `Sym2` because
`line[ℝ, p, q] = line[ℝ, q, p]`. -/
noncomputable def lineOfEdge (A : Finset (ℝ × ℝ)) : Sym2 ↥A → AffineSubspace ℝ (ℝ × ℝ) :=
  Sym2.lift ⟨fun p q => line[ℝ, (p : ℝ × ℝ), (q : ℝ × ℝ)], fun _ _ => line_comm _ _⟩

@[simp] theorem lineOfEdge_mk (A : Finset (ℝ × ℝ)) (p q : ↥A) :
    lineOfEdge A s(p, q) = line[ℝ, (p : ℝ × ℝ), (q : ℝ × ℝ)] :=
  Sym2.lift_mk _ _ _

/-- For an edge `{p, q}` of `G_A`, the `A`-points on `ℓ_pq` are exactly `p` and `q`. -/
theorem ptsOn_line_eq_pair_of_adj {A : Finset (ℝ × ℝ)} {p q : ↥A}
    (hadj : (ordGraph A).Adj p q) :
    ptsOn A line[ℝ, (p : ℝ × ℝ), (q : ℝ × ℝ)]
      = ({(p : ℝ × ℝ), (q : ℝ × ℝ)} : Set (ℝ × ℝ)) := by
  refine ptsOn_eq_pair_of_mem hadj.2.2 ?_ ?_ hadj.1
  · exact ⟨Finset.mem_coe.mpr p.2, left_mem_affineSpan_pair ℝ _ _⟩
  · exact ⟨Finset.mem_coe.mpr q.2, right_mem_affineSpan_pair ℝ _ _⟩

/-- `lineOfEdge` is injective on edges: an ordinary line determines its pair. -/
theorem edge_eq_of_line_eq {A : Finset (ℝ × ℝ)} {p q p' q' : ↥A}
    (hadj : (ordGraph A).Adj p q) (hadj' : (ordGraph A).Adj p' q')
    (hline : line[ℝ, (p : ℝ × ℝ), (q : ℝ × ℝ)] = line[ℝ, (p' : ℝ × ℝ), (q' : ℝ × ℝ)]) :
    s(p, q) = s(p', q') := by
  have h1 := ptsOn_line_eq_pair_of_adj hadj
  rw [hline, ptsOn_line_eq_pair_of_adj hadj'] at h1
  rw [Sym2.eq_iff]
  rcases Set.pair_eq_pair_iff.mp h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl ⟨Subtype.ext e1.symm, Subtype.ext e2.symm⟩
  · exact Or.inr ⟨Subtype.ext e2.symm, Subtype.ext e1.symm⟩

/-- **`e(G_A) = ord(A)`.**

Paper (§2.1), verbatim: "so that `e(G_A) = ord(A)`". The map sending an edge `{p, q}`
to the line `ℓ_pq` is a bijection onto the ordinary lines of `A`: it is surjective
because an ordinary line carries exactly two `A`-points, and injective because a line
meeting `A` in exactly `{p, q}` determines that pair. -/
theorem card_edgeFinset_ordGraph (A : Finset (ℝ × ℝ)) :
    (ordGraph A).edgeFinset.card = ord A := by
  classical
  rw [ord, Set.ncard_eq_toFinset_card _ (ordinaryLines_finite A)]
  refine Finset.card_nbij (lineOfEdge A) ?_ ?_ ?_
  -- edges land on ordinary lines
  · intro e
    induction e using Sym2.ind with
    | _ p q =>
      intro he
      have hadj : (ordGraph A).Adj p q := by
        simpa only [Finset.mem_coe, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using he
      simpa only [Finset.mem_coe, Set.Finite.mem_toFinset, lineOfEdge_mk, mem_ordinaryLines]
        using hadj.2
  -- injective
  · intro e he e' he' hline
    induction e using Sym2.ind with
    | _ p q =>
      induction e' using Sym2.ind with
      | _ p' q' =>
        have hadj : (ordGraph A).Adj p q := by
          simpa only [Finset.mem_coe, SimpleGraph.mem_edgeFinset,
            SimpleGraph.mem_edgeSet] using he
        have hadj' : (ordGraph A).Adj p' q' := by
          simpa only [Finset.mem_coe, SimpleGraph.mem_edgeFinset,
            SimpleGraph.mem_edgeSet] using he'
        rw [lineOfEdge_mk, lineOfEdge_mk] at hline
        exact edge_eq_of_line_eq hadj hadj' hline
  -- surjective
  · intro L hL
    have hLord : ordinaryLine A L := by
      simpa only [Finset.mem_coe, Set.Finite.mem_toFinset, mem_ordinaryLines] using hL
    obtain ⟨p, q, hpA, hqA, hpq, -, hLeq⟩ := ordinaryLine.exists_pair hLord
    refine ⟨s((⟨p, hpA⟩ : ↥A), (⟨q, hqA⟩ : ↥A)), ?_, ?_⟩
    · refine Finset.mem_coe.mpr (SimpleGraph.mem_edgeFinset.mpr ?_)
      rw [SimpleGraph.mem_edgeSet]
      exact ⟨hpq, hLeq ▸ hLord⟩
    · rw [lineOfEdge_mk]; exact hLeq.symm

/-! ## Bipartite graphs are `K_r`-free for `r ≥ 3`

The paper uses "bipartite, hence triangle-free" (Prop. 2.4, 2.5) and then "triangle-free,
hence `K_r`-free for `r ≥ 3`" (§2.3). This is the bridge: `IsBipartite` is by definition
`Colorable 2`, and a `2`-colorable graph has no clique on `r > 2` vertices. -/

theorem cliqueFree_of_isBipartite {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (h : G.IsBipartite) (hr : 3 ≤ r) : G.CliqueFree r :=
  h.cliqueFree (by omega)

/-! ## The constraints defining `F_{r,k}(n)` -/

/-- No `k` points of `A` are collinear.

Paper (§2.1), verbatim: "`|ℓ ∩ A| ≤ k − 1` for every line `ℓ`". -/
def NoKCollinear (A : Finset (ℝ × ℝ)) (k : ℕ) : Prop :=
  ∀ L : AffineSubspace ℝ (ℝ × ℝ), IsLine L → (ptsOn A L).ncard ≤ k - 1

/-- `A` is an admissible configuration for `F_{r,k}`.

Paper (§2.1): the maximum defining `F_{r,k}(n)` ranges over `n`-point sets `A ⊂ ℝ²`
such that (i) `|ℓ ∩ A| ≤ k − 1` for every line `ℓ`, and (ii) `A` contains no subset
`A' ⊂ A` with `|A'| = r` such that every pair of distinct points of `A'` spans an
ordinary line of `A`.

Condition (ii) is exactly "`G_A` has no `r`-clique": the paper notes that the required
`r`-point subset "is precisely a `K_r` in `G_A`". -/
def Admissible (r k : ℕ) (A : Finset (ℝ × ℝ)) : Prop :=
  NoKCollinear A k ∧ (ordGraph A).CliqueFree r

/-- The set of values `ord A` attainable by an admissible `n`-point configuration. -/
def ordValues (r k n : ℕ) : Set ℕ :=
  {v | ∃ A : Finset (ℝ × ℝ), A.card = n ∧ Admissible r k A ∧ ord A = v}

theorem ordValues_bddAbove (r k n : ℕ) : BddAbove (ordValues r k n) := by
  refine ⟨n.choose 2, ?_⟩
  rintro v ⟨A, hA, -, rfl⟩
  exact hA ▸ ord_le_choose A

/-- **`F_{r,k}(n)`.**

Paper (§2.1): `F_{r,k}(n) := max ord(A)` over admissible `n`-point configurations `A`,
with the verbatim degenerate convention

  "If no such configuration exists, set `F_{r,k}(n) = −1`."

The `−1` is why the codomain is `ℤ` rather than `ℕ`. -/
noncomputable def F (r k n : ℕ) : ℤ :=
  haveI := Classical.dec (ordValues r k n).Nonempty
  if (ordValues r k n).Nonempty then ((sSup (ordValues r k n) : ℕ) : ℤ) else -1

/-- On the non-degenerate branch, `F` is literally `sSup (ordValues …)`. -/
theorem F_eq_sSup {r k n : ℕ} (h : (ordValues r k n).Nonempty) :
    F r k n = ((sSup (ordValues r k n) : ℕ) : ℤ) := by
  rw [F]
  split
  · rfl
  · exact absurd h (by assumption)

/-- On the degenerate branch, `F = -1`: the paper's convention, recorded. -/
theorem F_eq_neg_one {r k n : ℕ} (h : ¬ (ordValues r k n).Nonempty) : F r k n = -1 := by
  rw [F]
  split
  · exact absurd (by assumption) h
  · rfl

/-- On the non-degenerate branch `F` really is attained: it equals `ord A` for some
admissible `A`. (`Nat.sSup_mem` plus `ordValues_bddAbove`.) -/
theorem F_eq_of_nonempty {r k n : ℕ} (h : (ordValues r k n).Nonempty) :
    ∃ A : Finset (ℝ × ℝ), A.card = n ∧ Admissible r k A ∧ (ord A : ℤ) = F r k n := by
  obtain ⟨A, hcard, hadm, hord⟩ := Nat.sSup_mem h (ordValues_bddAbove r k n)
  exact ⟨A, hcard, hadm, by rw [F_eq_sSup h, hord]⟩

/-- The inequality we actually need in the main theorem: any admissible configuration
witnesses a lower bound on `F`. -/
theorem le_F {r k n : ℕ} {A : Finset (ℝ × ℝ)} (hcard : A.card = n)
    (hadm : Admissible r k A) : (ord A : ℤ) ≤ F r k n := by
  have hmem : ord A ∈ ordValues r k n := ⟨A, hcard, hadm, rfl⟩
  rw [F_eq_sSup ⟨ord A, hmem⟩]
  exact Int.ofNat_le.mpr (le_csSup (ordValues_bddAbove r k n) hmem)

end Erdos960
