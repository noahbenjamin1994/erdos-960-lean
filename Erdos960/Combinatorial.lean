/-
# Erdős 960 — the combinatorial side

§2.2.2 (base construction, Prop. 2.4) and §2.2.3 (size adjustment, Prop. 2.5) of the
paper, on the group `ZMod (7*m)`. Nothing here mentions the curve: by the reduction of
`Curve.lean` all ordinariness questions are questions about `x + y` in `ZMod (7*m)`.

Gate 0 verified that the arithmetic core of Prop. 2.4 (the three multipliers `-1`, `-2`,
`3` mapping `U = {1,2,4}` into `V = {3,5,6}`) is decidable and closes by `decide`.

**Status: this file is `sorry`-free.** The one obligation that used to live here,
`edgeCount_eq_ord` (the geometry ⇄ group-law bridge), is *geometry* rather than
combinatorics — it needs `CurveModel.ordinaryLine_iff`, i.e. the chord construction —
so it has been moved verbatim to `Erdos960/Bridge.lean`, where the curve-side
obligations belong. Nothing in this file depends on it.

Where `m ≥ 12` (i.e. `n ≥ 72`) is used: `zsmul_hgen_inj` and nowhere else. Every
consumer of the hypothesis — `card_T`, `T_ne_zero`, `T_induced_bipartite`,
`card_Aset`, `Aset_bipartite`, `ord_Aset_ge` — goes through it.
-/

import Erdos960.Curve

namespace Erdos960

/-! ## Residues mod 7 and the coset decomposition -/

section Defs

variable (m : ℕ)

instance neZero_seven_mul [NeZero m] : NeZero (7 * m) := ⟨by
  have : m ≠ 0 := NeZero.ne m
  positivity⟩

/-- The reduction `ZMod (7m) →+* ZMod 7`, i.e. "residue class mod 7".
Paper §2.2.2: `C_i = i·g + H` is the fibre of this map over `i`. -/
def resid : ZMod (7 * m) →+* ZMod 7 :=
  ZMod.castHom (Dvd.intro m rfl) (ZMod 7)

/-- `C i`, the `i`-th coset of `H` in `C = ZMod (7m)`.
Paper §2.2.2: "for `i ∈ ℤ/7ℤ` write `C_i = ig + H`". -/
noncomputable def C [NeZero m] (i : ZMod 7) : Finset (ZMod (7 * m)) :=
  {x : ZMod (7 * m) | resid m x = i}

/-- `H = C 0`, the index-7 subgroup of order `m`.
Paper §2.2.2: `H = ⟨7g⟩ ≤ C`, `|H| = m`, and `C_0 = H`. -/
noncomputable def H [NeZero m] : Finset (ZMod (7 * m)) := C m 0

end Defs

variable {m : ℕ}

theorem resid_surjective : Function.Surjective (resid m) :=
  ZMod.castHom_surjective (Dvd.intro m rfl)

theorem mem_C_iff [NeZero m] {x : ZMod (7 * m)} {i : ZMod 7} :
    x ∈ C m i ↔ resid m x = i := by
  simp [C]

theorem mem_H_iff [NeZero m] {x : ZMod (7 * m)} : x ∈ H m ↔ resid m x = 0 := mem_C_iff

/-- All seven fibres of `resid` have the same size: translating by a preimage of `i`
is a bijection `C_i → C_0`. -/
theorem card_C_eq_card_C_zero [NeZero m] (i : ZMod 7) : (C m i).card = (C m 0).card := by
  classical
  obtain ⟨x₀, hx₀⟩ := resid_surjective (m := m) i
  refine Finset.card_nbij' (fun x => x - x₀) (fun y => y + x₀) ?_ ?_ ?_ ?_ <;>
    intro x hx <;>
    simp only [Finset.mem_coe, mem_C_iff, map_sub, map_add, hx₀] at hx ⊢
  · rw [hx]; ring
  · rw [hx]; ring
  · ring
  · ring

theorem sum_card_C [NeZero m] : ∑ i : ZMod 7, (C m i).card = 7 * m := by
  classical
  have h : (Finset.univ : Finset (ZMod (7 * m))).card
      = ∑ i : ZMod 7, ((Finset.univ : Finset (ZMod (7 * m))).filter
          (fun x => resid m x = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
  have h2 : ∀ i : ZMod 7, ((Finset.univ : Finset (ZMod (7 * m))).filter
      (fun x => resid m x = i)) = C m i := by
    intro i; ext x; simp [C]
  simp only [h2] at h
  rw [← h, Finset.card_univ, ZMod.card]

/-- Each coset has exactly `m` elements. Paper §2.2.2 (`|H| = m` and `C` is the disjoint
union of the seven cosets). -/
theorem card_C [NeZero m] (i : ZMod 7) : (C m i).card = m := by
  classical
  have hsum := sum_card_C (m := m)
  simp only [card_C_eq_card_C_zero (m := m), Finset.sum_const, Finset.card_univ, ZMod.card,
    smul_eq_mul] at hsum
  rw [card_C_eq_card_C_zero (m := m) i]
  omega

theorem card_H [NeZero m] : (H m).card = m := card_C 0

/-- The seven cosets are pairwise disjoint and cover `C`.
Paper §2.2.2: "`C = C_0 ⊔ C_1 ⊔ ⋯ ⊔ C_6`". -/
theorem C_disjoint [NeZero m] {i j : ZMod 7} (h : i ≠ j) : Disjoint (C m i) (C m j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rw [mem_C_iff] at hxi hxj
  exact h (hxi ▸ hxj ▸ rfl)

/-! ## The base configuration `A₀` -/

/-- `A₀ = C \ H`, the paper's base configuration.
Paper §2.2.2, verbatim: "`A_0 = C \ H = C_1 ⊔ C_2 ⊔ C_3 ⊔ C_4 ⊔ C_5 ⊔ C_6`", `|A_0| = 6m`. -/
noncomputable def A₀ [NeZero m] : Finset (ZMod (7 * m)) :=
  {x : ZMod (7 * m) | resid m x ≠ 0}

theorem mem_A₀_iff [NeZero m] {x : ZMod (7 * m)} : x ∈ A₀ (m := m) ↔ resid m x ≠ 0 := by
  simp [A₀]

/-- `|A₀| = 6m`. Paper §2.2.2. -/
theorem card_A₀ [NeZero m] : (A₀ (m := m)).card = 6 * m := by
  classical
  have h : ((Finset.univ : Finset (ZMod (7 * m))).filter (fun x => resid m x ≠ 0)).card
      + ((Finset.univ : Finset (ZMod (7 * m))).filter (fun x => ¬ resid m x ≠ 0)).card
      = (Finset.univ : Finset (ZMod (7 * m))).card :=
    Finset.card_filter_add_card_filter_not _
  have e1 : ((Finset.univ : Finset (ZMod (7 * m))).filter (fun x => resid m x ≠ 0))
      = A₀ (m := m) := by ext x; simp [A₀]
  have e2 : ((Finset.univ : Finset (ZMod (7 * m))).filter (fun x => ¬ resid m x ≠ 0))
      = H m := by ext x; simp [H, C]
  rw [e1, e2, Finset.card_univ, ZMod.card, card_H] at h
  omega

/-- `A₀` and `H` are disjoint: `H` is exactly the zero residue class. -/
theorem A₀_disjoint_H [NeZero m] : Disjoint (A₀ (m := m)) (H m) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact mem_A₀_iff.1 hx (mem_H_iff.1 hx')

/-! ## The arithmetic heart of Proposition 2.4

Gate 0 proved these three by `decide`; they are the whole content of bipartiteness. -/

/-- `U = {1,2,4}` and `V = {3,5,6}`, the paper's bipartition of the nonzero residues. -/
def U : Finset (ZMod 7) := {1, 2, 4}
def V : Finset (ZMod 7) := {3, 5, 6}

/-- The three multipliers `-1`, `-2`, `3` of Prop. 2.4 all send `U` into `V`.
Paper §2.2.2: "the multipliers `-1`, `-2`, `3` all map `U` onto `V`". Proved. -/
theorem multipliers_send_U_to_V :
    ∀ i ∈ U, (-i ∈ V ∧ (-2 : ZMod 7) * i ∈ V ∧ (3 : ZMod 7) * i ∈ V) := by
  decide

/-- Symmetrically, the multipliers send `V` into `U`. Proved. -/
theorem multipliers_send_V_to_U :
    ∀ i ∈ V, (-i ∈ U ∧ (-2 : ZMod 7) * i ∈ U ∧ (3 : ZMod 7) * i ∈ U) := by
  decide

/-- `-2 * 3 = 1` in `ZMod 7`: why the third relation is `j ≡ 3i` and not a repeat of
`j ≡ -2i`. Paper §2.2.2. Proved. -/
theorem neg_two_mul_three : (-2 : ZMod 7) * 3 = 1 := by decide

/-- `U ⊔ V` is exactly the set of nonzero residues. Proved. -/
theorem U_union_V : U ∪ V = (Finset.univ : Finset (ZMod 7)).erase 0 := by decide

theorem U_disjoint_V : Disjoint U V := by decide

/-- Every nonzero residue is on one of the two sides. -/
theorem nonzero_mem_U_or_V : ∀ i : ZMod 7, i ≠ 0 → i ∈ U ∨ i ∈ V := by decide

theorem zero_notMem_U : (0 : ZMod 7) ∉ U := by decide
theorem zero_notMem_V : (0 : ZMod 7) ∉ V := by decide

/-! ## Proposition 2.4 -/

variable [NeZero m]

/-- The ordinary-line graph of the base configuration, pulled back to the group.
`{x, y}` is an edge iff `x ≠ y` and the third point `-(x+y)` is not a further point
of `A₀` on the line — which by Prop. 2.4 happens iff `x + y ∈ H`, `y = -2x`, or
`x = -2y`. -/
def ordAdj (S : Finset (ZMod (7 * m))) (x y : ZMod (7 * m)) : Prop :=
  x ≠ y ∧ (-(x + y) ∉ S ∨ -(x + y) = x ∨ -(x + y) = y)

/-- `ordAdj` is symmetric: the third point `-(x+y)` is symmetric in `x` and `y`, and so
is the disjunction. -/
theorem ordAdj_symm {S : Finset (ZMod (7 * m))} {x y : ZMod (7 * m)} (h : ordAdj S x y) :
    ordAdj S y x := by
  obtain ⟨hne, hc⟩ := h
  refine ⟨hne.symm, ?_⟩
  rw [add_comm y x]
  tauto

/-- Adding points can only destroy edges, never create them: if `x, y` are adjacent in
the larger configuration `S ⊇ A₀` then they were adjacent in `A₀`.
Paper §2.2.3: "if `{x,y} ⊂ A_0` is non-ordinary in `A_0`, its third point already lies in
`A_0`, so it stays non-ordinary after adding `T_s`." -/
theorem ordAdj_of_superset {S : Finset (ZMod (7 * m))} (hsub : A₀ (m := m) ⊆ S)
    {x y : ZMod (7 * m)} (h : ordAdj S x y) : ordAdj (A₀ (m := m)) x y := by
  obtain ⟨hne, hc⟩ := h
  refine ⟨hne, ?_⟩
  rcases hc with hz | hz | hz
  · exact Or.inl fun hmem => hz (hsub hmem)
  · exact Or.inr (Or.inl hz)
  · exact Or.inr (Or.inr hz)

/-- A pair is *not* adjacent as soon as its third point is a further point of the
configuration. -/
theorem not_ordAdj_of_third {S : Finset (ZMod (7 * m))} {x y : ZMod (7 * m)}
    (hmem : -(x + y) ∈ S) (h1 : -(x + y) ≠ x) (h2 : -(x + y) ≠ y) : ¬ ordAdj S x y := by
  rintro ⟨-, hc | hc | hc⟩
  · exact hc hmem
  · exact h1 hc
  · exact h2 hc

/-- The number of ordinary pairs inside `S`, i.e. `e(G_S)` computed on the group side.
Ordered pairs are counted and halved, so this is the number of unordered edges. -/
noncomputable def edgeCount (S : Finset (ZMod (7 * m))) : ℕ :=
  haveI := Classical.decPred (fun p : ZMod (7 * m) × ZMod (7 * m) => ordAdj S p.1 p.2)
  (S.offDiag.filter (fun p => ordAdj S p.1 p.2)).card / 2

/-- A lower bound on `edgeCount` from any family of `2k` ordered ordinary pairs.

No parity argument is needed: `Nat.le_div_iff_mul_le` turns `k ≤ N / 2` into `2k ≤ N`
outright, and `2k ≤ N` is what exhibiting `2k` ordered pairs gives. -/
theorem le_edgeCount {S : Finset (ZMod (7 * m))} {k : ℕ}
    {D : Finset (ZMod (7 * m) × ZMod (7 * m))}
    (hD : ∀ p ∈ D, p.1 ∈ S ∧ p.2 ∈ S ∧ ordAdj S p.1 p.2)
    (hk : 2 * k ≤ D.card) : k ≤ edgeCount S := by
  classical
  rw [edgeCount, Nat.le_div_iff_mul_le (by norm_num)]
  have hsub : D ⊆ S.offDiag.filter (fun p => ordAdj S p.1 p.2) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hD p hp
    simp only [Finset.mem_filter, Finset.mem_offDiag]
    exact ⟨⟨h1, h2, h3.1⟩, h3⟩
  have := Finset.card_le_card hsub
  omega

/-! ### The three residue identities of Prop. 2.4

Each of the three cases of `ordAdj` becomes one linear identity in `ZMod 7`, and each is
`decide`able because `ZMod 7` is a fintype. -/

theorem resid_case_notMem : ∀ a b : ZMod 7, -(a + b) = 0 → b = -a := by decide
theorem resid_case_eq_fst : ∀ a : ZMod 7, -(a + a) = (-2 : ZMod 7) * a := by decide
theorem resid_case_eq_snd : ∀ t : ZMod 7, t = (3 : ZMod 7) * -(t + t) := by decide

/-- **Prop. 2.4, edge classification.** Paper §2.2.2: if `{x,y}` is an edge of `G_{A₀}`
with `x ∈ C_i`, `y ∈ C_j`, then `j ≡ -i`, `j ≡ -2i`, or `j ≡ 3i` (mod 7).

The third case really is `j ≡ 3i`: it comes from `x = -2y`, i.e. `i ≡ -2j`, solved in
`ZMod 7` using `-2 · 3 = 1` (`neg_two_mul_three`). -/
theorem ordAdj_residues {x y : ZMod (7 * m)} (hx : x ∈ A₀ (m := m)) (hy : y ∈ A₀ (m := m))
    (h : ordAdj (A₀ (m := m)) x y) :
    resid m y = -resid m x ∨ resid m y = (-2 : ZMod 7) * resid m x ∨
      resid m y = (3 : ZMod 7) * resid m x := by
  obtain ⟨hne, hc⟩ := h
  rcases hc with hz | hz | hz
  · -- the third point is not in `A₀`, i.e. it lies in `H`: `x + y ∈ H`
    left
    have h0 : resid m (-(x + y)) = 0 := by
      by_contra hcon
      exact hz (mem_A₀_iff.2 hcon)
    rw [map_neg, map_add] at h0
    exact resid_case_notMem _ _ h0
  · -- the third point is `x`, i.e. `y = -2x`
    right; left
    have hy2 : y = -(x + x) := by linear_combination -hz
    rw [hy2, map_neg, map_add]
    exact resid_case_eq_fst _
  · -- the third point is `y`, i.e. `x = -2y`
    right; right
    have hx2 : x = -(y + y) := by linear_combination -hz
    rw [hx2, map_neg, map_add]
    exact resid_case_eq_snd _

/-- `X = C₁ ⊔ C₂ ⊔ C₄` and `Y = C₃ ⊔ C₅ ⊔ C₆`, the bipartition of `A₀`. -/
noncomputable def Xpart : Finset (ZMod (7 * m)) := {x : ZMod (7 * m) | resid m x ∈ U}
noncomputable def Ypart : Finset (ZMod (7 * m)) := {x : ZMod (7 * m) | resid m x ∈ V}

theorem mem_Xpart_iff {x : ZMod (7 * m)} : x ∈ Xpart (m := m) ↔ resid m x ∈ U := by
  simp [Xpart]

theorem mem_Ypart_iff {x : ZMod (7 * m)} : x ∈ Ypart (m := m) ↔ resid m x ∈ V := by
  simp [Ypart]

/-- The whole of Prop. 2.4's bipartiteness argument, as one decidable statement about
`ZMod 7`: a nonzero residue `i` lies in `U` or `V`, and each of the three relations
`j = -i`, `j = -2i`, `j = 3i` sends it to the other side. -/
theorem bipartite_arith : ∀ i j : ZMod 7, i ≠ 0 →
    (j = -i ∨ j = (-2 : ZMod 7) * i ∨ j = (3 : ZMod 7) * i) →
    ((i ∈ U ∧ j ∈ V) ∨ (i ∈ V ∧ j ∈ U)) := by decide

/-- **Prop. 2.4, bipartiteness.** Paper §2.2.2, verbatim: "The ordinary-line graph
`G_{A_0}` is bipartite, hence triangle-free." Every edge joins `Xpart` to `Ypart`. -/
theorem ordAdj_crosses {x y : ZMod (7 * m)} (hx : x ∈ A₀ (m := m)) (hy : y ∈ A₀ (m := m))
    (h : ordAdj (A₀ (m := m)) x y) :
    (x ∈ Xpart (m := m) ∧ y ∈ Ypart (m := m)) ∨
      (x ∈ Ypart (m := m) ∧ y ∈ Xpart (m := m)) := by
  have hres := ordAdj_residues hx hy h
  rcases bipartite_arith (resid m x) (resid m y) (mem_A₀_iff.1 hx) hres with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨mem_Xpart_iff.2 h1, mem_Ypart_iff.2 h2⟩
  · exact Or.inr ⟨mem_Ypart_iff.2 h1, mem_Xpart_iff.2 h2⟩

/-- The three *dual coset pairs* `(C₁,C₆)`, `(C₂,C₅)`, `(C₄,C₃)` of Prop. 2.4. -/
def dualPairs : List (ZMod 7) := [1, 2, 4]

/-- **Prop. 2.4, the guaranteed edges.** Paper §2.2.2: if `x ∈ C_i`, `y ∈ C_{-i}` with
`i ≠ 0`, then `x + y ∈ H`, so the third point lies in `H` and `ℓ_xy` is ordinary. -/
theorem ordAdj_of_dual {x y : ZMod (7 * m)} {i : ZMod 7} (hi : i ≠ 0)
    (hx : x ∈ C m i) (hy : y ∈ C m (-i)) (hxy : x ≠ y) :
    ordAdj (A₀ (m := m)) x y := by
  refine ⟨hxy, Or.inl ?_⟩
  intro hmem
  refine mem_A₀_iff.1 hmem ?_
  rw [map_neg, map_add, mem_C_iff.1 hx, mem_C_iff.1 hy]
  simp

/-! ### Counting the guaranteed edges

`Dual` is the set of *ordered* pairs `(x, y)` with `x ∈ C_i`, `y ∈ C_{-i}` for some
`i ≠ 0`. It has `6m²` elements — six nonzero residues, `m` choices on each side — and by
`ordAdj_of_dual` every one of them is an ordinary pair. Halving gives `3m²`. -/

/-- `i ≠ -i` for a nonzero residue mod 7 (7 is odd), so `C_i` and `C_{-i}` are distinct
cosets and a dual pair automatically has `x ≠ y`. -/
theorem ne_neg_self : ∀ i : ZMod 7, i ≠ 0 → i ≠ -i := by decide

/-- The ordered dual pairs of residue `i`. -/
noncomputable def dualSet (i : ZMod 7) : Finset (ZMod (7 * m) × ZMod (7 * m)) :=
  C m i ×ˢ C m (-i)

/-- All ordered dual pairs, over the six nonzero residues. -/
noncomputable def Dual : Finset (ZMod (7 * m) × ZMod (7 * m)) :=
  ((Finset.univ : Finset (ZMod 7)).erase 0).biUnion (dualSet (m := m))

theorem mem_Dual_iff {p : ZMod (7 * m) × ZMod (7 * m)} :
    p ∈ Dual (m := m) ↔ ∃ i : ZMod 7, i ≠ 0 ∧ p.1 ∈ C m i ∧ p.2 ∈ C m (-i) := by
  classical
  simp only [Dual, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true,
    dualSet, Finset.mem_product]

/-- Every ordered dual pair consists of two `A₀`-points spanning an ordinary line. -/
theorem Dual_mem_A₀ {p : ZMod (7 * m) × ZMod (7 * m)} (hp : p ∈ Dual (m := m)) :
    p.1 ∈ A₀ (m := m) ∧ p.2 ∈ A₀ (m := m) ∧ ordAdj (A₀ (m := m)) p.1 p.2 := by
  obtain ⟨i, hi, h1, h2⟩ := mem_Dual_iff.1 hp
  have hr1 : resid m p.1 = i := mem_C_iff.1 h1
  have hr2 : resid m p.2 = -i := mem_C_iff.1 h2
  have hne : p.1 ≠ p.2 := by
    intro hcon
    rw [hcon, hr2] at hr1
    exact ne_neg_self i hi hr1.symm
  refine ⟨mem_A₀_iff.2 (by rw [hr1]; exact hi), mem_A₀_iff.2 ?_,
    ordAdj_of_dual hi h1 h2 hne⟩
  rw [hr2]
  simpa using hi

theorem card_Dual : (Dual (m := m)).card = 6 * m * m := by
  classical
  have hdisj : (((Finset.univ : Finset (ZMod 7)).erase 0 : Finset (ZMod 7)) :
      Set (ZMod 7)).PairwiseDisjoint (dualSet (m := m)) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hq
    simp only [dualSet, Finset.mem_product] at hp hq
    exact hij ((mem_C_iff.1 hp.1).symm.trans (mem_C_iff.1 hq.1))
  have hcard : ∀ i : ZMod 7, (dualSet (m := m) i).card = m * m := by
    intro i; rw [dualSet, Finset.card_product, card_C, card_C]
  rw [Dual, Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun i _ => hcard i),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ZMod.card, smul_eq_mul]
  norm_num
  ring

/-- **Prop. 2.4, the count.** Paper §2.2.2, verbatim: "`ord(A_0) ≥ 3m²`" — each of the
three dual coset pairs contributes `m²` edges. -/
theorem ord_A₀_ge : 3 * m ^ 2 ≤ (edgeCount (A₀ (m := m)) : ℕ) := by
  refine le_edgeCount (D := Dual (m := m)) (fun p hp => Dual_mem_A₀ hp) ?_
  rw [card_Dual]
  exact le_of_eq (by ring)

/-! ## §2.2.3 — size adjustment -/

/-- A fixed generator of `H`: the paper's `h`, of additive order `m`.
Paper §2.2.3: "fix a generator `h` of `H`". -/
def hgen : ZMod (7 * m) := (7 : ℕ)

theorem addOrderOf_hgen (hm : 0 < m) : addOrderOf (hgen (m := m)) = m := by
  have h7 : (7 : ℕ) * m ≠ 0 := by positivity
  rw [hgen, ZMod.addOrderOf_coe 7 h7, Nat.gcd_comm, Nat.gcd_eq_left (Dvd.intro m rfl)]
  omega

theorem resid_hgen : resid m (hgen (m := m)) = 0 := by
  rw [hgen, map_natCast]; decide

theorem resid_zsmul_hgen (a : ℤ) : resid m (a • hgen (m := m)) = 0 := by
  rw [map_zsmul, resid_hgen, smul_zero]

theorem hgen_mem_H : hgen (m := m) ∈ H m := mem_H_iff.2 resid_hgen

theorem zsmul_hgen_mem_H (a : ℤ) : a • hgen (m := m) ∈ H m :=
  mem_H_iff.2 (resid_zsmul_hgen a)

/-- Small multiples of `h` are distinct: `a • h = b • h` forces `m ∣ a - b`, and here
`|a - b| < 12 ≤ m`.

🔴 **This is the one and only place `m ≥ 12` — i.e. `n ≥ 72` — is used.** The paper's
§2.2.3 says exactly this: "Because `m ≥ 12`, all listed points are distinct and nonzero."
The largest difference that actually arises below is `|7 - (-4)| = 11`, so the threshold
is genuinely needed and genuinely sufficient. -/
theorem zsmul_hgen_inj (hm : 12 ≤ m) {a b : ℤ} (hab : |a - b| < 12)
    (h : a • hgen (m := m) = b • hgen (m := m)) : a = b := by
  have hz : (a - b) • hgen (m := m) = 0 := by rw [sub_zsmul, h]; simp
  rw [← addOrderOf_dvd_iff_zsmul_eq_zero, addOrderOf_hgen (by omega)] at hz
  have := Int.eq_zero_of_abs_lt_dvd hz (by omega)
  omega

theorem zsmul_hgen_ne (hm : 12 ≤ m) {a b : ℤ} (hab : |a - b| < 12) (hne : a ≠ b) :
    a • hgen (m := m) ≠ b • hgen (m := m) :=
  fun h => hne (zsmul_hgen_inj hm hab h)

/-- `T s`, the set of added points. Paper §2.2.3, verbatim:

  `T_0 = ∅`, `T_1 = {h}`, `T_2 = {h, 2h}`, `T_3 = {h, 2h, -3h}`,
  `T_4 = {h, 2h, -3h, 3h}`, `T_5 = {h, 2h, -3h, 3h, -4h}`.

Defined as the first `s` entries of the list `[h, 2h, -3h, 3h, -4h]`, which reproduces
all six cases. -/
noncomputable def T (s : ℕ) : Finset (ZMod (7 * m)) :=
  (([hgen, 2 • hgen, -(3 • hgen), 3 • hgen, -(4 • hgen)] : List (ZMod (7 * m))).take s).toFinset

/-- The coefficient list of `T`, over `ℤ`. -/
def Tcoeff : List ℤ := [1, 2, -3, 3, -4]

theorem Tcoeff_cases {c : ℤ} (hc : c ∈ Tcoeff) :
    c = 1 ∨ c = 2 ∨ c = -3 ∨ c = 3 ∨ c = -4 := by
  simp only [Tcoeff, List.mem_cons, List.not_mem_nil, or_false] at hc
  tauto

/-- `T s` rewritten as the `ℤ`-multiples `c • h` for `c` in the first `s` coefficients.
This is the form every later proof uses: membership in `T s` becomes membership of a
small integer in a small list of small integers. -/
theorem T_eq_map (s : ℕ) :
    T (m := m) s = ((Tcoeff.take s).map (fun c : ℤ => c • hgen (m := m))).toFinset := by
  rw [T, List.map_take]
  congr 2
  simp [Tcoeff]

theorem mem_T_iff {s : ℕ} {x : ZMod (7 * m)} :
    x ∈ T (m := m) s ↔ ∃ c ∈ Tcoeff.take s, x = c • hgen (m := m) := by
  rw [T_eq_map]
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩

/-- `|T s| = s` for `s ≤ 5`, given `m ≥ 12`. Paper §2.2.3, verbatim: "Because `m ≥ 12`,
all listed points are distinct and nonzero, so `|T_s| = s`."

**This is the sole source of the hypothesis `n ≥ 72`.** -/
theorem card_T (hm : 12 ≤ m) {s : ℕ} (hs : s ≤ 5) : (T (m := m) s).card = s := by
  classical
  have hne : ∀ a b : ℤ, a ∈ Tcoeff → b ∈ Tcoeff → a ≠ b →
      a • hgen (m := m) ≠ b • hgen (m := m) := by
    intro a b ha hb hab
    refine zsmul_hgen_ne hm ?_ hab
    rcases Tcoeff_cases ha with rfl | rfl | rfl | rfl | rfl <;>
      rcases Tcoeff_cases hb with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hnodup : ((Tcoeff.take s).map (fun c : ℤ => c • hgen (m := m))).Nodup := by
    refine List.Nodup.map_on ?_ (List.Nodup.sublist (List.take_sublist _ _) (by decide))
    intro a ha b hb hab
    by_contra hcon
    exact hne a b (List.mem_of_mem_take ha) (List.mem_of_mem_take hb) hcon hab
  rw [T_eq_map, List.toFinset_card_of_nodup hnodup, List.length_map, List.length_take]
  simp only [Tcoeff, List.length_cons, List.length_nil]
  omega

/-- The added points are nonzero, as the paper requires (they must be genuine points of
`E(ℝ) \ {O}`, and `O` is the group identity). -/
theorem T_ne_zero (hm : 12 ≤ m) {s : ℕ} {x : ZMod (7 * m)} (hx : x ∈ T (m := m) s) :
    x ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := mem_T_iff.1 hx
  have hcT : c ∈ Tcoeff := List.mem_of_mem_take hc
  have h : c • hgen (m := m) ≠ (0 : ℤ) • hgen := by
    refine zsmul_hgen_ne hm ?_ ?_ <;>
      (rcases Tcoeff_cases hcT with rfl | rfl | rfl | rfl | rfl <;> norm_num)
  simpa using h

theorem T_subset_H {s : ℕ} (hs : s ≤ 5) : T (m := m) s ⊆ H m := by
  intro x hx
  obtain ⟨c, _, rfl⟩ := mem_T_iff.1 hx
  exact zsmul_hgen_mem_H c

/-- `A = A₀ ∪ T s`, the final configuration. Paper §2.2.3: "set `A = A_0 ∪ T_s`, so
`|A| = 6m + s = n`". -/
noncomputable def Aset (s : ℕ) : Finset (ZMod (7 * m)) := A₀ ∪ T s

theorem A₀_subset_Aset (s : ℕ) : A₀ (m := m) ⊆ Aset (m := m) s := Finset.subset_union_left

theorem T_subset_Aset (s : ℕ) : T (m := m) s ⊆ Aset (m := m) s := Finset.subset_union_right

theorem A₀_disjoint_T {s : ℕ} (hs : s ≤ 5) : Disjoint (A₀ (m := m)) (T (m := m) s) :=
  Finset.disjoint_of_subset_right (T_subset_H hs) A₀_disjoint_H

/-- `|A| = 6m + s = n`. Paper §2.2.3. -/
theorem card_Aset (hm : 12 ≤ m) {s : ℕ} (hs : s ≤ 5) :
    (Aset (m := m) s).card = 6 * m + s := by
  classical
  rw [Aset, Finset.card_union_of_disjoint (A₀_disjoint_T hs), card_A₀, card_T hm hs]

/-! ### Proposition 2.5 -/

/-- The three residue facts behind "no edges between `A₀` and `T_s`": for `i ≠ 0`, the
third point's residue `-(0 + i) = -i` is nonzero (so it lies in `A₀`), and differs from
both `0` (the residue of `t ∈ H`) and `i` (the residue of `x`). -/
theorem no_edge_arith :
    ∀ i : ZMod 7, i ≠ 0 → (-(0 + i) ≠ 0 ∧ -(0 + i) ≠ 0 ∧ -(0 + i) ≠ i) := by decide

/-- **Prop. 2.5, no edges between `A₀` and `T_s`.** Paper §2.2.3: for `t ∈ T_s ⊆ H` and
`x ∈ C_i` with `i ≠ 0`, the third point `z = -t-x` lies in `C_{-i} ⊆ A₀` and differs from
both `t` and `x`, so `ℓ_tx` is not ordinary. -/
theorem no_edge_A₀_T (hm : 12 ≤ m) {s : ℕ} (hs : s ≤ 5)
    {t x : ZMod (7 * m)} (ht : t ∈ T (m := m) s) (hx : x ∈ A₀ (m := m)) :
    ¬ ordAdj (Aset (m := m) s) t x := by
  have hrt : resid m t = 0 := mem_H_iff.1 (T_subset_H hs ht)
  have hrx : resid m x ≠ 0 := mem_A₀_iff.1 hx
  have hz : resid m (-(t + x)) = -(0 + resid m x) := by rw [map_neg, map_add, hrt]
  obtain ⟨h1, h2, h3⟩ := no_edge_arith (resid m x) hrx
  rintro ⟨-, hc | hc | hc⟩
  · -- the third point lies in `A₀ ⊆ Aset s`
    exact hc (A₀_subset_Aset s (mem_A₀_iff.2 (by rw [hz]; exact h1)))
  · -- `z = t` would force `-i = 0`
    exact h2 (by rw [← hz, hc, hrt])
  · -- `z = x` would force `-i = i`
    exact h3 (by rw [← hz, hc])

/-- The non-edges inside `T_s`, in coefficient form: the third point of `a • h` and
`b • h` is `(-(a+b)) • h`; if that point is itself in `T_s` and is neither endpoint, the
pair is not an edge. -/
theorem not_ordAdj_within (hm : 12 ≤ m) {s : ℕ} {a b : ℤ}
    (hmem : (-(a + b)) • hgen (m := m) ∈ T (m := m) s)
    (h1 : |(-(a + b)) - a| < 12) (h1' : -(a + b) ≠ a)
    (h2 : |(-(a + b)) - b| < 12) (h2' : -(a + b) ≠ b) :
    ¬ ordAdj (Aset (m := m) s) (a • hgen) (b • hgen) := by
  have hthird : -((a • hgen (m := m)) + b • hgen) = (-(a + b)) • hgen (m := m) := by
    rw [neg_zsmul, add_zsmul]
  refine not_ordAdj_of_third ?_ ?_ ?_
  · rw [hthird]; exact T_subset_Aset s hmem
  · rw [hthird]; exact zsmul_hgen_ne hm h1 h1'
  · rw [hthird]; exact zsmul_hgen_ne hm h2 h2'

/-- **Prop. 2.5, the induced subgraph on `T_s` is bipartite.** Paper §2.2.3 works the six
cases out by direct computation: `s ≤ 2` gives clique number `≤ 2`; `s = 3` gives no
edges (because `h + 2h + (-3h) = O`); `s = 4` gives the star `{h,3h}`, `{2h,3h}`,
`{3h,-3h}`; `s = 5` gives the 4-cycle `{2h,3h}`, `{2h,-4h}`, `{3h,-3h}`, `{-4h,-3h}`.

The formalization needs only *two* bipartitions rather than six, which is why this proof
is short:

* `s ≤ 2`: `T_s ⊆ {h, 2h}`. Put the two points on opposite sides and *every* pair
  crosses, so no edge analysis is required at all — this covers the paper's
  "`s = 0,1,2`: clique number `≤ 2`" uniformly.
* `3 ≤ s ≤ 5`: `P = {h, 2h, -3h}`, `Q = {3h, -4h}`. This single partition works for all
  three of the paper's cases (`s = 3` no edges, `s = 4` star, `s = 5` 4-cycle), because
  the only pairs it would fail on are the three inside `P` and the one inside `Q`, and
  each of those four has its third point (`-3h`, `2h`, `h`, `h` respectively) already in
  `T_s` — so none of them is an edge. -/
theorem T_induced_bipartite (hm : 12 ≤ m) {s : ℕ} (hs : s ≤ 5) :
    ∃ P Q : Finset (ZMod (7 * m)),
      Disjoint P Q ∧ T (m := m) s ⊆ P ∪ Q ∧
      ∀ x ∈ T (m := m) s, ∀ y ∈ T (m := m) s, ordAdj (Aset (m := m) s) x y →
        ((x ∈ P ∧ y ∈ Q) ∨ (x ∈ Q ∧ y ∈ P)) := by
  classical
  by_cases hs2 : s ≤ 2
  · -- `T_s ⊆ {h, 2h}`, on opposite sides: every pair crosses.
    have hsub2 : ∀ c : ℤ, c ∈ Tcoeff.take s → c = 1 ∨ c = 2 := by
      intro c hc
      interval_cases s <;> simp_all [Tcoeff]
    refine ⟨{(1 : ℤ) • hgen (m := m)}, {(2 : ℤ) • hgen (m := m)}, ?_, ?_, ?_⟩
    · simp only [Finset.disjoint_singleton]
      exact zsmul_hgen_ne hm (by norm_num) (by norm_num)
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := mem_T_iff.1 hx
      simp only [Finset.mem_union, Finset.mem_singleton]
      rcases hsub2 c hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro x hx y hy hadj
      obtain ⟨c, hc, rfl⟩ := mem_T_iff.1 hx
      obtain ⟨d, hd, rfl⟩ := mem_T_iff.1 hy
      have hcd : c ≠ d := fun h => hadj.1 (by rw [h])
      simp only [Finset.mem_singleton]
      rcases hsub2 c hc with rfl | rfl <;> rcases hsub2 d hd with rfl | rfl <;>
        first
          | exact absurd rfl hcd
          | exact Or.inl ⟨rfl, rfl⟩
          | exact Or.inr ⟨rfl, rfl⟩
  · -- `3 ≤ s ≤ 5`
    have hs3 : 3 ≤ s := by omega
    -- for `s ≥ 3` the multiples `h`, `2h`, `-3h` are all available in `T_s`
    have hmemT : ∀ c : ℤ, (c = 1 ∨ c = 2 ∨ c = -3) → c • hgen (m := m) ∈ T (m := m) s := by
      intro c hc
      refine mem_T_iff.2 ⟨c, ?_, rfl⟩
      interval_cases s <;> (rcases hc with rfl | rfl | rfl <;> simp [Tcoeff])
    -- the four internal non-edges: three inside `P`, one inside `Q`
    have key : ∀ c d : ℤ, c ≠ d →
        ((c = 1 ∨ c = 2 ∨ c = -3) ∧ (d = 1 ∨ d = 2 ∨ d = -3)) ∨
          ((c = 3 ∨ c = -4) ∧ (d = 3 ∨ d = -4)) →
        ¬ ordAdj (Aset (m := m) s) (c • hgen) (d • hgen) := by
      intro c d hcd hlist
      rcases hlist with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;>
        [ (rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl);
          (rcases hc with rfl | rfl <;> rcases hd with rfl | rfl) ] <;>
        first
          | exact absurd rfl hcd
          | exact not_ordAdj_within hm (hmemT _ (by norm_num)) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num)
    -- `P` holds the coefficients `1, 2, -3`; `Q` holds `3, -4`
    have hmemP : ∀ e : ℤ, (e = 1 ∨ e = 2 ∨ e = -3) →
        e • hgen (m := m) ∈ ({(1 : ℤ) • hgen (m := m), (2 : ℤ) • hgen, (-3 : ℤ) • hgen} :
          Finset (ZMod (7 * m))) := by
      intro e he
      rcases he with rfl | rfl | rfl <;> simp
    have hmemQ : ∀ e : ℤ, (e = 3 ∨ e = -4) →
        e • hgen (m := m) ∈ ({(3 : ℤ) • hgen (m := m), (-4 : ℤ) • hgen} :
          Finset (ZMod (7 * m))) := by
      intro e he
      rcases he with rfl | rfl <;> simp
    refine ⟨{(1 : ℤ) • hgen (m := m), (2 : ℤ) • hgen, (-3 : ℤ) • hgen},
            {(3 : ℤ) • hgen (m := m), (-4 : ℤ) • hgen}, ?_, ?_, ?_⟩
    · -- disjointness: six pairwise inequalities of small multiples
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with h | h <;>
        exact zsmul_hgen_ne hm (by norm_num) (by norm_num) h
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := mem_T_iff.1 hx
      have hcT := Tcoeff_cases (List.mem_of_mem_take hc)
      rw [Finset.mem_union]
      rcases hcT with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (hmemP _ (by norm_num))
      · exact Or.inl (hmemP _ (by norm_num))
      · exact Or.inl (hmemP _ (by norm_num))
      · exact Or.inr (hmemQ _ (by norm_num))
      · exact Or.inr (hmemQ _ (by norm_num))
    · intro x hx y hy hadj
      obtain ⟨c, hc, rfl⟩ := mem_T_iff.1 hx
      obtain ⟨d, hd, rfl⟩ := mem_T_iff.1 hy
      have hcd : c ≠ d := fun h => hadj.1 (by rw [h])
      -- each coefficient is on one of the two sides
      have hside : ∀ e : ℤ, e ∈ Tcoeff → (e = 1 ∨ e = 2 ∨ e = -3) ∨ (e = 3 ∨ e = -4) := by
        intro e he
        rcases Tcoeff_cases he with rfl | rfl | rfl | rfl | rfl <;> norm_num
      rcases hside c (List.mem_of_mem_take hc) with hcP | hcQ <;>
        rcases hside d (List.mem_of_mem_take hd) with hdP | hdQ
      · exact absurd hadj (key _ _ hcd (Or.inl ⟨hcP, hdP⟩))
      · exact Or.inl ⟨hmemP _ hcP, hmemQ _ hdQ⟩
      · exact Or.inr ⟨hmemQ _ hcQ, hmemP _ hdP⟩
      · exact absurd hadj (key _ _ hcd (Or.inr ⟨hcQ, hdQ⟩))

/-- **Prop. 2.5 (2).** Paper §2.2.3, verbatim: "The ordinary-line graph `G_A` is
bipartite, in particular triangle-free."

The bipartition is `Xpart ∪ (P ∩ H)` versus `Ypart ∪ (Q ∩ H)`. The three kinds of edge
are handled by the three preceding results: `A₀`-internal edges cross by Prop. 2.4
(`ordAdj_crosses`, pulled back along `ordAdj_of_superset`), `T_s`-internal edges cross by
`T_induced_bipartite`, and mixed edges do not exist (`no_edge_A₀_T`). Intersecting `P`
and `Q` with `H` is what makes the two halves disjoint from `Xpart`/`Ypart ⊆ A₀`. -/
theorem Aset_bipartite (hm : 12 ≤ m) {s : ℕ} (hs : s ≤ 5) :
    ∃ P Q : Finset (ZMod (7 * m)),
      Disjoint P Q ∧ Aset (m := m) s ⊆ P ∪ Q ∧
      ∀ x ∈ Aset (m := m) s, ∀ y ∈ Aset (m := m) s, ordAdj (Aset (m := m) s) x y →
        ((x ∈ P ∧ y ∈ Q) ∨ (x ∈ Q ∧ y ∈ P)) := by
  classical
  obtain ⟨P, Q, hPQ, hTsub, hTcross⟩ := T_induced_bipartite hm hs
  have hXA : ∀ x : ZMod (7 * m), x ∈ Xpart (m := m) → x ∈ A₀ (m := m) := by
    intro x hx
    refine mem_A₀_iff.2 fun h0 => ?_
    exact zero_notMem_U (h0 ▸ mem_Xpart_iff.1 hx)
  have hYA : ∀ x : ZMod (7 * m), x ∈ Ypart (m := m) → x ∈ A₀ (m := m) := by
    intro x hx
    refine mem_A₀_iff.2 fun h0 => ?_
    exact zero_notMem_V (h0 ▸ mem_Ypart_iff.1 hx)
  refine ⟨Xpart (m := m) ∪ (P ∩ H m), Ypart (m := m) ∪ (Q ∩ H m), ?_, ?_, ?_⟩
  · rw [Finset.disjoint_union_left, Finset.disjoint_union_right,
      Finset.disjoint_union_right]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      exact fun x hx hy =>
        Finset.disjoint_left.1 U_disjoint_V (mem_Xpart_iff.1 hx) (mem_Ypart_iff.1 hy)
    · rw [Finset.disjoint_left]
      exact fun x hx hy =>
        Finset.disjoint_left.1 A₀_disjoint_H (hXA x hx) (Finset.mem_of_mem_inter_right hy)
    · rw [Finset.disjoint_left]
      exact fun x hx hy =>
        Finset.disjoint_left.1 A₀_disjoint_H (hYA x hy) (Finset.mem_of_mem_inter_right hx)
    · exact Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hPQ)
  · intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · -- `x ∈ A₀`: its residue is nonzero, hence in `U` or `V`
      rcases nonzero_mem_U_or_V (resid m x) (mem_A₀_iff.1 hx) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (mem_Xpart_iff.2 h))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (mem_Ypart_iff.2 h))
    · -- `x ∈ T s`: use the `T`-bipartition, intersected with `H`
      have hxH : x ∈ H m := T_subset_H hs hx
      rcases Finset.mem_union.1 (hTsub hx) with h | h
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨h, hxH⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨h, hxH⟩))
  · intro x hx y hy hadj
    rcases Finset.mem_union.1 hx with hxA | hxT
    · rcases Finset.mem_union.1 hy with hyA | hyT
      · -- both in `A₀`: Prop. 2.4
        rcases ordAdj_crosses hxA hyA (ordAdj_of_superset (A₀_subset_Aset s) hadj) with
          ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨Finset.mem_union_left _ h1, Finset.mem_union_left _ h2⟩
        · exact Or.inr ⟨Finset.mem_union_left _ h1, Finset.mem_union_left _ h2⟩
      · exact absurd (ordAdj_symm hadj) (no_edge_A₀_T hm hs hyT hxA)
    · rcases Finset.mem_union.1 hy with hyA | hyT
      · exact absurd hadj (no_edge_A₀_T hm hs hxT hyA)
      · -- both in `T s`
        have hxH : x ∈ H m := T_subset_H hs hxT
        have hyH : y ∈ H m := T_subset_H hs hyT
        rcases hTcross x hxT y hyT hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨Finset.mem_union_right _ (Finset.mem_inter.2 ⟨h1, hxH⟩),
            Finset.mem_union_right _ (Finset.mem_inter.2 ⟨h2, hyH⟩)⟩
        · exact Or.inr ⟨Finset.mem_union_right _ (Finset.mem_inter.2 ⟨h1, hxH⟩),
            Finset.mem_union_right _ (Finset.mem_inter.2 ⟨h2, hyH⟩)⟩

/-- **Prop. 2.5 (3), the edge-destruction count.** Paper §2.2.3, verbatim: "for each
`x ∈ C_i` there is a unique `y = -t-x ∈ C_{-i}`, so exactly `m` edges of that dual pair
are destroyed by `t`."

Stated as: for `i ≠ 0` and `t ∈ H`, the pairs of the dual coset `(C_i, C_{-i})` whose
third point is `t` — i.e. with `x + y = -t` — number exactly `m`, one per `x ∈ C_i`.
Summed over the three dual pairs this is the `3m` of the paper. The filter condition is
in fact automatic: `resid (-t-x) = -resid x` whenever `resid t = 0`. -/
theorem card_destroyed_by (hm : 12 ≤ m) {t : ZMod (7 * m)} (ht : t ∈ H m)
    {i : ZMod 7} (hi : i ≠ 0) :
    ((C m i).filter (fun x => -t - x ∈ C m (-i))).card = m := by
  classical
  have hrt : resid m t = 0 := mem_H_iff.1 ht
  have hall : ∀ x ∈ C m i, -t - x ∈ C m (-i) := by
    intro x hx
    refine mem_C_iff.2 ?_
    rw [map_sub, map_neg, hrt, mem_C_iff.1 hx]
    ring
  rw [Finset.filter_true_of_mem hall, card_C]

/-! ### The edges destroyed by the added points

`Bad` is the set of dual pairs whose third point landed in `T_s`; `Good` is the rest.
Each `t ∈ T_s` kills at most one pair per `x ∈ A₀` — namely `(x, -t-x)` — so
`|Bad| ≤ 6ms` and `|Good| ≥ 6m² - 6ms`. Halving gives the paper's `3m² - 3ms`. -/

/-- The dual pairs that the added points destroy. -/
noncomputable def Bad (s : ℕ) : Finset (ZMod (7 * m) × ZMod (7 * m)) :=
  (Dual (m := m)).filter (fun p => -(p.1 + p.2) ∈ T (m := m) s)

/-- The surviving dual pairs. -/
noncomputable def Good (s : ℕ) : Finset (ZMod (7 * m) × ZMod (7 * m)) :=
  (Dual (m := m)).filter (fun p => ¬ (-(p.1 + p.2) ∈ T (m := m) s))

theorem card_Bad_add_card_Good (s : ℕ) :
    (Bad (m := m) s).card + (Good (m := m) s).card = 6 * m * m := by
  classical
  rw [Bad, Good, ← card_Dual (m := m)]
  exact Finset.card_filter_add_card_filter_not _

/-- `|Bad| ≤ 6ms`: each of the `s` added points `t` destroys at most `|A₀| = 6m` ordered
pairs, since such a pair is determined by its first coordinate via `y = -t-x`. -/
theorem card_Bad_le (hm : 12 ≤ m) {s : ℕ} (hs : s ≤ 5) :
    (Bad (m := m) s).card ≤ 6 * m * s := by
  classical
  have hsub : Bad (m := m) s ⊆
      (T (m := m) s).biUnion (fun t => (A₀ (m := m)).image (fun x => (x, -t - x))) := by
    intro p hp
    rw [Bad, Finset.mem_filter] at hp
    obtain ⟨hpD, hpT⟩ := hp
    refine Finset.mem_biUnion.2 ⟨-(p.1 + p.2), hpT, ?_⟩
    refine Finset.mem_image.2 ⟨p.1, (Dual_mem_A₀ hpD).1, Prod.ext rfl ?_⟩
    show -(-(p.1 + p.2)) - p.1 = p.2
    ring
  calc (Bad (m := m) s).card
      ≤ ((T (m := m) s).biUnion
          (fun t => (A₀ (m := m)).image (fun x => (x, -t - x)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ _t ∈ T (m := m) s, (A₀ (m := m)).card :=
        le_trans Finset.card_biUnion_le
          (Finset.sum_le_sum (fun _ _ => Finset.card_image_le))
    _ = 6 * m * s := by
        rw [Finset.sum_const, card_T hm hs, card_A₀, smul_eq_mul]; ring

/-- Every surviving dual pair really is an ordinary pair of the *enlarged* configuration:
its third point has residue `0`, so it is outside `A₀`, and `Good` checked it is not in
`T_s` either. -/
theorem Good_mem_Aset {s : ℕ} (hs : s ≤ 5) {p : ZMod (7 * m) × ZMod (7 * m)}
    (hp : p ∈ Good (m := m) s) :
    p.1 ∈ Aset (m := m) s ∧ p.2 ∈ Aset (m := m) s ∧ ordAdj (Aset (m := m) s) p.1 p.2 := by
  classical
  rw [Good, Finset.mem_filter] at hp
  obtain ⟨hpD, hpT⟩ := hp
  obtain ⟨h1, h2, hadj⟩ := Dual_mem_A₀ hpD
  obtain ⟨i, hi, hc1, hc2⟩ := mem_Dual_iff.1 hpD
  have hthird : resid m (-(p.1 + p.2)) = 0 := by
    rw [map_neg, map_add, mem_C_iff.1 hc1, mem_C_iff.1 hc2]
    simp
  refine ⟨A₀_subset_Aset s h1, A₀_subset_Aset s h2, hadj.1, Or.inl ?_⟩
  intro hmem
  rcases Finset.mem_union.1 hmem with h | h
  · exact mem_A₀_iff.1 h hthird
  · exact hpT h

/-- **Prop. 2.5 (3).** Paper §2.2.3, verbatim: "`ord(A) ≥ 3m² − 3ms`".

`m ≥ 12` and `s ≤ 5` give `s ≤ m`, so the natural-number subtraction `m - s` is exact and
the `ℕ`-level bound casts to the stated `ℤ`-level one without loss. -/
theorem ord_Aset_ge (hm : 12 ≤ m) {s : ℕ} (hs : s ≤ 5) :
    3 * (m : ℤ) ^ 2 - 3 * m * s ≤ (edgeCount (Aset (m := m) s) : ℤ) := by
  classical
  have hsm : s ≤ m := by omega
  have hkey : 6 * m * (m - s) + 6 * m * s = 6 * m * m := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hsm]
  -- `|Good| ≥ 6m² - 6ms`, stated additively to stay inside `ℕ`
  have hGood : 6 * m * (m - s) ≤ (Good (m := m) s).card := by
    refine Nat.le_of_add_le_add_right (b := (Bad (m := m) s).card) ?_
    calc 6 * m * (m - s) + (Bad (m := m) s).card
        ≤ 6 * m * (m - s) + 6 * m * s := Nat.add_le_add_left (card_Bad_le hm hs) _
      _ = 6 * m * m := hkey
      _ = (Bad (m := m) s).card + (Good (m := m) s).card :=
          (card_Bad_add_card_Good (m := m) s).symm
      _ = (Good (m := m) s).card + (Bad (m := m) s).card := Nat.add_comm _ _
  have hnat : 3 * m * (m - s) ≤ edgeCount (Aset (m := m) s) := by
    refine le_edgeCount (D := Good (m := m) s) (fun p hp => Good_mem_Aset hs hp) ?_
    calc 2 * (3 * m * (m - s)) = 6 * m * (m - s) := by ring
      _ ≤ (Good (m := m) s).card := hGood
  have hcast : ((3 * m * (m - s) : ℕ) : ℤ) = 3 * (m : ℤ) ^ 2 - 3 * m * s := by
    push_cast [Nat.cast_sub hsm]
    ring
  calc 3 * (m : ℤ) ^ 2 - 3 * m * s = ((3 * m * (m - s) : ℕ) : ℤ) := hcast.symm
    _ ≤ (edgeCount (Aset (m := m) s) : ℤ) := Int.ofNat_le.2 hnat

/-! ## The final arithmetic of §2.3

Gate 0 proved all three of these outright; they are restated here in the shape the main
theorem consumes. -/

/-- The exact identity of §2.3: with `n = 6m + s`,
`3m² − 3ms = n²/12 − (2s/3)n + 7s²/12`. Proved by `ring`. -/
theorem key_identity (a s : ℝ) :
    3 * a ^ 2 - 3 * a * s
      = (6 * a + s) ^ 2 / 12 - (2 * s / 3) * (6 * a + s) + 7 * s ^ 2 / 12 := by
  ring

/-- §2.3: for `0 ≤ s ≤ 5`, `3m² − 3ms ≥ n²/12 − (10/3)n` where `n = 6m + s`.
The slack discarded is the nonnegative `7s²/12`, plus `2s/3 ≤ 10/3`. Proved. -/
theorem final_bound (a s : ℝ) (hs0 : 0 ≤ s) (hs5 : s ≤ 5) (ha : 0 ≤ a) :
    (6 * a + s) ^ 2 / 12 - 10 * (6 * a + s) / 3 ≤ 3 * a ^ 2 - 3 * a * s := by
  nlinarith [sq_nonneg s, sq_nonneg a, mul_nonneg ha hs0]

/-- §2.3: `n ≥ 72` is equivalent to `m ≥ 12` given `n = 6m + s`, `s ≤ 5`. Proved. -/
theorem m_ge_twelve {a s n : ℕ} (hn : n = 6 * a + s) (hs : s ≤ 5) (h72 : 72 ≤ n) :
    12 ≤ a := by
  omega

/-- Every `n` decomposes as `6m + s` with `s ≤ 5`. Proved. -/
theorem exists_decomp (n : ℕ) : ∃ m s : ℕ, n = 6 * m + s ∧ s ≤ 5 :=
  ⟨n / 6, n % 6, by omega, by omega⟩

end Erdos960
