/-
# Erdős 960 — the curve side

§2.2.1 of the paper works on the real elliptic curve `E : y² = x³ - x + 1` and uses
exactly three facts about it:

  * **Lemma 2.2**  `E(ℝ)` is connected, hence `≅ ℝ/ℤ` as a Lie group, hence contains a
    cyclic subgroup of order `M` for every `M ≥ 1`.
  * **Lemma 2.3**  every affine line meets `E(ℝ) \ {O}` in at most three points; so no
    four points of a finite subset are collinear.
  * **Collinearity criterion**  three points of `E` are collinear, counted with
    multiplicity, iff they sum to `O` in the group law.

Gate 0 established (see `GATE0.md`) that Mathlib has **no topology at all** on
`WeierstrassCurve.Affine.Point` — no `TopologicalSpace` instance, no Lie group theory,
no uniformization — and **no** link between the group law and `Collinear`.

## What this file assumes, and what it proves

🔴 **Scope reduction, stated plainly.** `CurveModel` below packages the *collinearity
criterion* as a hypothesis. That single field is the only unproved geometric input.

Everything else the paper's §2.2.1 supplies is **proved here**, not assumed:

  * **Lemma 2.3 is a theorem, not an axiom** (`CurveModel.no_four_collinear`). Gate 0 and
    the step-3 draft of this file both listed it as a second assumption; it is not one.
    If `w+x+y = 0` and `w+x+z = 0` force `y = z`, four distinct points cannot be
    collinear, so the criterion *implies* no-four-collinear with no geometry at all.
    This strictly shrinks the assumption set relative to `GATE0.md`'s route (0).
  * The bridge `ordinaryLine_iff` between the plane-geometry `ordinaryLine` of
    `Defs.lean` and the `ZMod (7m)` arithmetic of `Combinatorial.lean`.
  * `noKCollinear_pts`, discharging the `NoKCollinear` half of `Admissible`.

What remains assumed is therefore: *some* abelian group of order `7m` embeds in the plane
with collinearity governed by the group law (`CurveModelAssumption`). This is paper
Lemma 2.2 together with the criterion. It is **not** proved for `y² = x³ - x + 1`; it
enters `erdos960` as an explicit hypothesis, never as an axiom, so `#print axioms` on
every declaration in this development is clean.

The `Concrete` section at the end proves what *is* reachable about the actual curve from
Mathlib today: its discriminant is nonzero (paper Lemma 2.2's smoothness half, with the
sign conventions reconciled) and every affine line meets it in at most three points
(paper Lemma 2.3, by the algebraic route rather than Bézout).

The paper's own remark (§2.2, verbatim: "while we use a specific elliptic curve below for
concreteness, any (non-degenerate) elliptic curve suffices") licenses parameterizing over
the curve; it does not license omitting Lemma 2.2, and that omission is ours and is
flagged as such in `README.md`, `GATE0.md` and `statement-fidelity.md`.
-/

import Erdos960.Defs

namespace Erdos960

/-! ## The cyclic-subgroup interface (paper Lemma 2.2) -/

/-- `HasCyclicSubgroupOfOrder G M`: the additive group `G` has an element of order `M`,
equivalently a cyclic subgroup of order `M`.

This is the entire conclusion of paper Lemma 2.2. Gate 0 verified it is satisfiable, with
two independent witnesses (`ZMod (7*m)` and `AddCircle (1:ℝ)`), so it is not a vacuous
hypothesis. -/
def HasCyclicSubgroupOfOrder (G : Type*) [AddCommGroup G] (M : ℕ) : Prop :=
  ∃ g : G, addOrderOf g = M

/-- `ZMod (7*m)` satisfies the interface, generator `1`. Anti-vacuity witness #1. -/
theorem zmod_hasCyclicSubgroup (m : ℕ) (hm : 0 < m) :
    HasCyclicSubgroupOfOrder (ZMod (7 * m)) (7 * m) := by
  have h7m : 7 * m ≠ 0 := by omega
  have : NeZero (7 * m) := ⟨h7m⟩
  exact ⟨1, ZMod.addOrderOf_one _⟩

/-- The circle group satisfies it too, via `AddCircle.addOrderOf_period_div`.
Anti-vacuity witness #2: the interface is not tied to the `ZMod` side. -/
theorem addCircle_hasCyclicSubgroup (M : ℕ) (hM : 0 < M) :
    HasCyclicSubgroupOfOrder (AddCircle (1 : ℝ)) M :=
  ⟨_, AddCircle.addOrderOf_period_div (p := (1 : ℝ)) hM⟩

/-! ## The curve model

A `CurveModel` is an abstract stand-in for `E(ℝ) \ {O}` sitting inside the plane: an
abelian group `G` together with an injection into `ℝ × ℝ`, such that collinearity of
images is controlled by the group law exactly as the chord–tangent construction dictates.
-/

/-- A **curve model**: the properties of `E(ℝ)` that §2.2.2–§2.3 actually consume.

The single non-structural field is `collinear_iff`, the paper's collinearity criterion.
Paper Lemma 2.3 is *derived* from it below (`no_four_collinear`), not assumed. -/
structure CurveModel (G : Type*) [AddCommGroup G] where
  /-- The embedding of the point group into the affine plane. -/
  emb : G → ℝ × ℝ
  /-- Distinct group elements are distinct plane points. -/
  emb_injective : Function.Injective emb
  /-- **Paper collinearity criterion** (§2.2.1, verbatim: "three points `x, y, z ∈ E`
  are collinear, counted with multiplicity, if and only if `x + y + z = O`"), restricted
  to triples of pairwise-distinct points, where "counted with multiplicity" is vacuous. -/
  collinear_iff : ∀ x y z : G, x ≠ y → y ≠ z → x ≠ z →
    (Collinear ℝ ({emb x, emb y, emb z} : Set (ℝ × ℝ)) ↔ x + y + z = 0)

/-- The *third point* of the line through `x` and `y`: by the collinearity criterion it
is forced to be `-(x + y)`. This depends only on the group, not on the model.

Gate 0 note: defining the third point this way rather than deriving it makes
`x + y + third x y = 0` free (`neg_add_cancel`), which is the only direction of the
criterion the paper's counting argument uses. -/
def third {G : Type*} [AddCommGroup G] (x y : G) : G := -(x + y)

theorem sum_third {G : Type*} [AddCommGroup G] (x y : G) : x + y + third x y = 0 := by
  simp [third]

/-- `x + y + z = 0` is exactly `z = third x y`. The arithmetic half of the criterion. -/
theorem third_eq_iff {G : Type*} [AddCommGroup G] (x y z : G) :
    x + y + z = 0 ↔ third x y = z := by
  constructor
  · intro h
    have h2 : -(x + y) + (x + y + z) = -(x + y) + 0 := by rw [h]
    rw [neg_add_cancel_left, add_zero] at h2
    exact h2.symm
  · rintro rfl
    exact sum_third x y

namespace CurveModel

variable {G : Type*} [AddCommGroup G] (M : CurveModel G)

/-- The image of a finite set of group elements, as a point set in the plane. -/
noncomputable def pts (S : Finset G) : Finset (ℝ × ℝ) := S.image M.emb

theorem card_pts (S : Finset G) : (M.pts S).card = S.card :=
  Finset.card_image_of_injective _ M.emb_injective

theorem emb_ne {x y : G} (h : x ≠ y) : M.emb x ≠ M.emb y :=
  fun he => h (M.emb_injective he)

theorem mem_pts {S : Finset G} {p : ℝ × ℝ} :
    p ∈ (M.pts S : Set (ℝ × ℝ)) ↔ ∃ z ∈ S, M.emb z = p := by
  simp [pts]

/-! ### Membership in the line through two model points -/

/-- **The criterion, in the form the counting argument uses.** For three pairwise-distinct
group elements, the third lies on the line through the first two exactly when the three
sum to zero — equivalently, exactly when it *is* the third point `-(x+y)`.

This is `collinear_iff` re-expressed through `line[ℝ, ·, ·]`; the translation between
`Collinear` on a triple and membership in the span of a pair is Mathlib's
`collinear_insert_of_mem_affineSpan_pair` / `Collinear.mem_affineSpan_of_mem_of_ne`. -/
theorem mem_line_iff {x y z : G} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    M.emb z ∈ line[ℝ, M.emb x, M.emb y] ↔ third x y = z := by
  rw [← third_eq_iff]
  constructor
  · intro h
    refine (M.collinear_iff x y z hxy hyz hxz).mp ?_
    have hc : Collinear ℝ ({M.emb z, M.emb x, M.emb y} : Set (ℝ × ℝ)) :=
      collinear_insert_of_mem_affineSpan_pair h
    refine hc.subset ?_
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
    tauto
  · intro h
    have hc := (M.collinear_iff x y z hxy hyz hxz).mpr h
    exact hc.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) (M.emb_ne hxy)

/-- **Paper Lemma 2.3, proved (not assumed).**

If four points of the model were collinear, then in particular `w, x, y` and `w, x, z`
would each be collinear triples, so `w + x + y = 0 = w + x + z`, so `y = z`. No geometry
is used: the collinearity criterion alone forbids four collinear points.

Gate 0 (`GATE0.md`, G0-3) listed Lemma 2.3 as a second thing to assume. It is not: this
theorem removes it from the hypothesis set. -/
theorem no_four_collinear (w x y z : G) (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ¬ Collinear ℝ ({M.emb w, M.emb x, M.emb y, M.emb z} : Set (ℝ × ℝ)) := by
  intro h
  have hsub₁ : ({M.emb w, M.emb x, M.emb y} : Set (ℝ × ℝ)) ⊆
      {M.emb w, M.emb x, M.emb y, M.emb z} := by
    intro p hp; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢; tauto
  have hsub₂ : ({M.emb w, M.emb x, M.emb z} : Set (ℝ × ℝ)) ⊆
      {M.emb w, M.emb x, M.emb y, M.emb z} := by
    intro p hp; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢; tauto
  have h₁ : w + x + y = 0 := (M.collinear_iff w x y hwx hxy hwy).mp (h.subset hsub₁)
  have h₂ : w + x + z = 0 := (M.collinear_iff w x z hwx hxz hwz).mp (h.subset hsub₂)
  exact hyz (add_left_cancel (h₁.trans h₂.symm))

/-! ### The bridge to `Combinatorial.lean`

(`collinear_coe_of_isLine`, previously proved here, moved to `Defs.lean` in step 5: the
finiteness of `ordinaryLines` needs it too, and `Curve.lean` imports `Defs.lean`. The
statement and proof are unchanged; only the file boundary moved.) -/

/-- **Ordinariness is a group-theoretic condition.** For distinct `x, y` in a finite
`S ⊆ G`, the line `ℓ_xy` is ordinary for `M.pts S` exactly when the third intersection
point `-(x+y)` fails to be a *further* point of `S` on that line.

This is the paper's reduction (Prop. 2.4, verbatim: "`ℓ_xy` is ordinary for `A_0` iff
`z ∈ H` or `z = x` or `z = y`" — with `z ∈ H` reading, at this level of generality, as
`z ∉ S`). It is the bridge between the geometric `ordinaryLine` of `Defs.lean` and the
arithmetic of `Combinatorial.lean`, and the right-hand side is *definitionally* the
disjunction in `Combinatorial.ordAdj`. -/
theorem ordinaryLine_iff (S : Finset G) (x y : G) (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ordinaryLine (M.pts S) line[ℝ, M.emb x, M.emb y] ↔
      (third x y ∉ S ∨ third x y = x ∨ third x y = y) := by
  have hne : M.emb x ≠ M.emb y := M.emb_ne hxy
  have hline : IsLine (line[ℝ, M.emb x, M.emb y] : AffineSubspace ℝ (ℝ × ℝ)) :=
    ⟨M.emb x, M.emb y, hne, rfl⟩
  -- The `A`-points on `ℓ_xy` are the images of `x`, `y`, and possibly `third x y`.
  have hmem : ∀ p : ℝ × ℝ,
      p ∈ ptsOn (M.pts S) line[ℝ, M.emb x, M.emb y] ↔
        ∃ z ∈ S, (z = x ∨ z = y ∨ third x y = z) ∧ M.emb z = p := by
    intro p
    constructor
    · rintro ⟨hpS, hpL⟩
      obtain ⟨z, hzS, rfl⟩ := M.mem_pts.mp hpS
      refine ⟨z, hzS, ?_, rfl⟩
      by_cases hzx : z = x
      · exact Or.inl hzx
      by_cases hzy : z = y
      · exact Or.inr (Or.inl hzy)
      exact Or.inr (Or.inr ((M.mem_line_iff hxy (Ne.symm hzx) (Ne.symm hzy)).mp hpL))
    · rintro ⟨z, hzS, hz, rfl⟩
      refine ⟨M.mem_pts.mpr ⟨z, hzS, rfl⟩, ?_⟩
      by_cases hzx : z = x
      · subst hzx; exact left_mem_affineSpan_pair _ _ _
      by_cases hzy : z = y
      · subst hzy; exact right_mem_affineSpan_pair _ _ _
      have hz' : third x y = z := by tauto
      exact (M.mem_line_iff hxy (Ne.symm hzx) (Ne.symm hzy)).mpr hz'
  constructor
  · rintro ⟨-, hcard⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨hmemS, hnx, hny⟩ := hcon
    -- `x`, `y`, `third x y` are three distinct points of `A` on `ℓ_xy`.
    have hsub : ({M.emb x, M.emb y, M.emb (third x y)} : Set (ℝ × ℝ)) ⊆
        ptsOn (M.pts S) line[ℝ, M.emb x, M.emb y] := by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact (hmem _).mpr ⟨x, hx, Or.inl rfl, rfl⟩
      · exact (hmem _).mpr ⟨y, hy, Or.inr (Or.inl rfl), rfl⟩
      · exact (hmem _).mpr ⟨third x y, hmemS, Or.inr (Or.inr rfl), rfl⟩
    have h3 : ({M.emb x, M.emb y, M.emb (third x y)} : Set (ℝ × ℝ)).ncard = 3 :=
      Set.ncard_eq_three.mpr
        ⟨M.emb x, M.emb y, M.emb (third x y), hne, (M.emb_ne (Ne.symm hnx)),
          (M.emb_ne (Ne.symm hny)), rfl⟩
    have := Set.ncard_le_ncard hsub (ptsOn_finite _ _)
    omega
  · intro h
    refine ⟨hline, ?_⟩
    -- In this branch the point set is exactly `{emb x, emb y}`.
    have hset : ptsOn (M.pts S) line[ℝ, M.emb x, M.emb y] =
        ({M.emb x, M.emb y} : Set (ℝ × ℝ)) := by
      ext p
      rw [hmem p]
      constructor
      · rintro ⟨z, hzS, hz, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hz with rfl | rfl | hz
        · exact Or.inl rfl
        · exact Or.inr rfl
        · -- `z = third x y ∈ S`, so the first disjunct of `h` is out
          rcases h with hnS | hxeq | hyeq
          · exact absurd (hz ▸ hzS) hnS
          · exact Or.inl (congrArg M.emb (hz ▸ hxeq : z = x))
          · exact Or.inr (congrArg M.emb (hz ▸ hyeq : z = y))
      · intro hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl
        · exact ⟨x, hx, Or.inl rfl, rfl⟩
        · exact ⟨y, hy, Or.inr (Or.inl rfl), rfl⟩
    rw [hset, Set.ncard_pair hne]

/-- **Paper Lemma 2.3, transported.** Any finite set of model points has no `k` collinear
points for `k ≥ 4`; this discharges the `NoKCollinear` half of `Admissible`. -/
theorem noKCollinear_pts (S : Finset G) (k : ℕ) (hk : 4 ≤ k) :
    NoKCollinear (M.pts S) k := by
  intro L hL
  have h3 : (ptsOn (M.pts S) L).ncard ≤ 3 := by
    by_contra hgt
    push_neg at hgt
    obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
      (Set.three_lt_ncard (ptsOn_finite _ _)).mp hgt
    obtain ⟨w, hwS, rfl⟩ := M.mem_pts.mp ha.1
    obtain ⟨x, hxS, rfl⟩ := M.mem_pts.mp hb.1
    obtain ⟨y, hyS, rfl⟩ := M.mem_pts.mp hc.1
    obtain ⟨z, hzS, rfl⟩ := M.mem_pts.mp hd.1
    refine M.no_four_collinear w x y z
      (fun h => hab (congrArg M.emb h)) (fun h => hac (congrArg M.emb h))
      (fun h => had (congrArg M.emb h)) (fun h => hbc (congrArg M.emb h))
      (fun h => hbd (congrArg M.emb h)) (fun h => hcd (congrArg M.emb h)) ?_
    refine (collinear_coe_of_isLine hL).subset ?_
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    exacts [ha.2, hb.2, hc.2, hd.2]
  omega

end CurveModel

/-! ## The remaining assumption

This is the interface the main theorem is stated against: some curve model whose group is
cyclic of order `7m`. -/

/-- 🔴 **The one unproved geometric input of the whole development.**

`CurveModelAssumption m` says the cyclic group of order `7m` embeds in the plane with
collinearity governed by its group law. On the real elliptic curve this holds: take
`C = ⟨g⟩ ≤ E(ℝ)` of order `7m` (paper Lemma 2.2, which needs `E(ℝ) ≅ ℝ/ℤ`) and embed by
the inclusion, the criterion being the chord construction (§2.2.1).

It is deliberately stated as a `def ... : Prop` and **not** proved, and **not** declared
as an `axiom`. Downstream, `erdos960` takes it as an explicit hypothesis, so no
declaration in this development depends on an unproved axiom — `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound`. The price is that `erdos960` is a
*conditional* theorem, which `README.md` and `statement-fidelity.md` state plainly.

Establishing it inside Mathlib requires the topology / Lie-group theory of `E(ℝ)` (Gate 0,
G0-1) and a `Collinear`-to-group-law bridge (G0-3), neither of which Mathlib has.
Note that paper Lemma 2.3 is *not* part of this assumption: it is proved above, from the
criterion alone (`CurveModel.no_four_collinear`). -/
def CurveModelAssumption (m : ℕ) : Prop := Nonempty (CurveModel (ZMod (7 * m)))

/-! ## Concrete: the curve `y² = x³ - x + 1`

What follows is not needed by the main theorem — it is the part of §2.2.1 that *is*
reachable from Mathlib today, recorded so that the gap above is as small and as precisely
located as possible. -/

namespace Concrete

open Polynomial

/-- The paper's curve `E : y² = x³ - x + 1`, as a Weierstrass curve
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with `a₁ = a₂ = a₃ = 0`, `a₄ = -1`, `a₆ = 1`. -/
def E : WeierstrassCurve ℝ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -1
  a₆ := 1

@[simp] theorem E_a₁ : E.a₁ = 0 := rfl
@[simp] theorem E_a₂ : E.a₂ = 0 := rfl
@[simp] theorem E_a₃ : E.a₃ = 0 := rfl
@[simp] theorem E_a₄ : E.a₄ = -1 := rfl
@[simp] theorem E_a₆ : E.a₆ = 1 := rfl

/-- **Paper Lemma 2.2, smoothness half.** The discriminant is `-368 ≠ 0`.

⚠ **Sign-convention reconciliation.** The paper writes the discriminant of
`y² = x³ + a₄x + a₆` as `-4a₄³ - 27a₆²`, giving `-4(-1)³ - 27·1² = 4 - 27 = -23`.
Mathlib's `WeierstrassCurve.Δ` is the LMFDB normalization, which for `a₁ = a₂ = a₃ = 0`
is `16` times the paper's: `Δ = -b₂²b₈ - 8b₄³ - 27b₆² + 9b₂b₄b₆` with `b₂ = 0`,
`b₄ = 2a₄ = -2`, `b₆ = 4a₆ = 4`, `b₈ = -a₄² = -1`, i.e. `-8(-2)³ - 27·4² = 64 - 432`.
So `Δ_mathlib = -368 = 16 · (-23) = 16 · Δ_paper`, and the two vanish together. -/
theorem E_Δ : E.Δ = -368 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, E_a₁, E_a₂, E_a₃, E_a₄, E_a₆]
  norm_num

/-- The reconciliation of the previous docstring, as a checked identity: Mathlib's `Δ` is
exactly `16` times the paper's `-4a₄³ - 27a₆²`. -/
theorem E_Δ_eq_sixteen_mul_paper : E.Δ = 16 * (-4 * E.a₄ ^ 3 - 27 * E.a₆ ^ 2) := by
  rw [E_Δ]; norm_num

/-- The paper's value, `-23`. -/
theorem paper_discriminant : -4 * E.a₄ ^ 3 - 27 * E.a₆ ^ 2 = -23 := by norm_num

theorem E_Δ_ne_zero : E.Δ ≠ 0 := by rw [E_Δ]; norm_num

/-- Since `Δ ≠ 0`, every point of the curve is nonsingular: `E` is an elliptic curve and
`WeierstrassCurve.Affine.Point` carries its `AddCommGroup` instance. -/
theorem E_nonsingular {x y : ℝ} (h : E.toAffine.Equation x y) : E.toAffine.Nonsingular x y :=
  (E.toAffine.equation_iff_nonsingular_of_Δ_ne_zero E_Δ_ne_zero).mp h

/-- The affine equation of `E`, unfolded: `y² = x³ - x + 1`. -/
theorem E_equation_iff (x y : ℝ) : E.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - x + 1 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  show _ ↔ _
  constructor <;> intro h <;> simp only [E] at * <;> linarith

/-! ### Paper Lemma 2.3 for the concrete curve

Every affine line meets `E(ℝ)` in at most three points. The paper argues by Bézout; we go
algebraically, which is what Mathlib supports: substitute the line's parametrization into
the equation and bound the number of roots of the resulting cubic. -/

/-- The cubic obtained by substituting the parametrized line `t ↦ (p₁ + t·d₁, p₂ + t·d₂)`
into `y² - (x³ - x + 1)`, written out in expanded form so that its coefficients are
literally the `C _` in sight.

Expanding `(p₂ + t d₂)² - ((p₁ + t d₁)³ - (p₁ + t d₁) + 1)` in `t` gives

  `t³ · (-d₁³)`
  `t² · (d₂² - 3 p₁ d₁²)`
  `t¹ · (2 p₂ d₂ - 3 p₁² d₁ + d₁)`
  `t⁰ · (p₂² - p₁³ + p₁ - 1)`

`lineCubic_eval` below certifies that this expansion is correct (by `ring`), so nothing
depends on the expansion having been done by hand correctly. -/
noncomputable def lineCubic (p₁ p₂ d₁ d₂ : ℝ) : ℝ[X] :=
  C (-d₁ ^ 3) * X ^ 3 + C (d₂ ^ 2 - 3 * p₁ * d₁ ^ 2) * X ^ 2
    + C (2 * p₂ * d₂ - 3 * p₁ ^ 2 * d₁ + d₁) * X + C (p₂ ^ 2 - p₁ ^ 3 + p₁ - 1)

/-- **The expansion is correct**: evaluating `lineCubic` at `t` is substituting the point
`(p₁ + t d₁, p₂ + t d₂)` into `y² - (x³ - x + 1)`. -/
theorem lineCubic_eval (p₁ p₂ d₁ d₂ t : ℝ) :
    (lineCubic p₁ p₂ d₁ d₂).eval t =
      (p₂ + t * d₂) ^ 2 - ((p₁ + t * d₁) ^ 3 - (p₁ + t * d₁) + 1) := by
  simp only [lineCubic, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

theorem lineCubic_natDegree_le (p₁ p₂ d₁ d₂ : ℝ) :
    (lineCubic p₁ p₂ d₁ d₂).natDegree ≤ 3 := by
  unfold lineCubic
  compute_degree

theorem lineCubic_coeff_three (p₁ p₂ d₁ d₂ : ℝ) :
    (lineCubic p₁ p₂ d₁ d₂).coeff 3 = -d₁ ^ 3 := by
  rw [lineCubic]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem lineCubic_coeff_two (p₁ p₂ d₁ d₂ : ℝ) :
    (lineCubic p₁ p₂ d₁ d₂).coeff 2 = d₂ ^ 2 - 3 * p₁ * d₁ ^ 2 := by
  rw [lineCubic]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- The cubic is not the zero polynomial when the direction vector is nonzero: if `d₁ ≠ 0`
the `X³` coefficient is `-d₁³ ≠ 0`; if `d₁ = 0` (a vertical line) the `X²` coefficient is
`d₂² ≠ 0`. -/
theorem lineCubic_ne_zero {p₁ p₂ d₁ d₂ : ℝ} (hd : d₁ ≠ 0 ∨ d₂ ≠ 0) :
    lineCubic p₁ p₂ d₁ d₂ ≠ 0 := by
  by_cases hd₁ : d₁ = 0
  · -- vertical line: look at the `X²` coefficient
    have hd₂ : d₂ ≠ 0 := by rcases hd with h | h; exacts [absurd hd₁ h, h]
    intro h
    have hc := lineCubic_coeff_two p₁ p₂ d₁ d₂
    rw [h, coeff_zero, hd₁] at hc
    exact hd₂ (pow_eq_zero_iff (M₀ := ℝ) (a := d₂) (n := 2) (by norm_num) |>.mp (by linarith))
  · -- non-vertical: look at the `X³` coefficient
    intro h
    have hc := lineCubic_coeff_three p₁ p₂ d₁ d₂
    rw [h, coeff_zero] at hc
    exact hd₁ (pow_eq_zero_iff (M₀ := ℝ) (a := d₁) (n := 3) (by norm_num) |>.mp (by linarith))

/-- **Paper Lemma 2.3 for the concrete curve, algebraic route.**

Any affine line meets `E(ℝ) = {(x,y) : y² = x³ - x + 1}` in at most three points.

Proof: parametrize the line as `t ↦ (p₁ + t d₁, p₂ + t d₂)` with `(d₁, d₂) ≠ 0`. A point
of the line lies on `E` exactly when its parameter is a root of `lineCubic`, which is a
nonzero polynomial of degree `≤ 3`, hence has at most three roots. Distinct points of the
line have distinct parameters, so there are at most three of them.

The paper argues by Bézout; Mathlib has no intersection-multiplicity theory, so this goes
through `Polynomial.card_roots'` instead. -/
theorem card_le_three_of_line {p₁ p₂ d₁ d₂ : ℝ} (hd : d₁ ≠ 0 ∨ d₂ ≠ 0)
    (T : Finset ℝ) (hT : ∀ t ∈ T, E.toAffine.Equation (p₁ + t * d₁) (p₂ + t * d₂)) :
    T.card ≤ 3 := by
  classical
  set f := lineCubic p₁ p₂ d₁ d₂ with hf
  have hf0 : f ≠ 0 := lineCubic_ne_zero hd
  -- every parameter in `T` is a root of `f`
  have hroot : T ⊆ f.roots.toFinset := by
    intro t ht
    rw [Multiset.mem_toFinset, mem_roots hf0]
    have := (E_equation_iff _ _).mp (hT t ht)
    simp only [IsRoot.def, hf, lineCubic_eval]
    linarith
  calc T.card ≤ f.roots.toFinset.card := Finset.card_le_card hroot
    _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le f.roots
    _ ≤ f.natDegree := card_roots' f
    _ ≤ 3 := lineCubic_natDegree_le _ _ _ _

end Concrete

end Erdos960
