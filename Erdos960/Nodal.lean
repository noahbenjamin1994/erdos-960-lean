/-
# Paper Lemma 2.2, discharged on a nodal cubic

`Curve.lean` packages the paper's Lemma 2.2 as the hypothesis `CurveModelAssumption m`,
namely `Nonempty (CurveModel (ZMod (7 * m)))`. This file **proves** it, so the hypothesis
can be discharged and `erdos960` becomes unconditional.

## Why this route avoids the gate-0 obstruction

The paper works on the smooth cubic `y² = x³ - x + 1` and gets its cyclic subgroups from
`E(ℝ)` being connected, hence `≅ ℝ/ℤ`. Gate 0 established that Mathlib has no topology on
`WeierstrassCurve.Affine.Point` at all, so that route needs an entire theory built first.

But `CurveModel` asks only for *some* injection of the group into the plane whose collinear
triples are exactly its zero-sum triples; the paper itself notes (§2.2) that any
non-degenerate curve suffices. A **singular** cubic serves, and its group law is elementary.

Take the nodal cubic `Z(X² + Y²) = X³` in the projective plane. It has an acnode at
`[0 : 0 : 1]`, so its real smooth locus is a circle rather than a line, and it carries an
explicit rational parametrisation by an angle

  `Pt φ = [cos (φ + π/6) : sin (φ + π/6) : cos (φ + π/6) ^ 3]`,

under which collinearity is angle addition: three pairwise distinct points are collinear
exactly when `φ₁ + φ₂ + φ₃ ≡ 0 (mod π)`. Restricting to `φ = k * π / N` gives `ZMod N`.
The `π/6` shift puts the origin of the group law at an inflection point; without it the
criterion reads `≡ π/2` instead of `≡ 0`.

Everything here is trigonometry and determinants. No topology, no Lie groups, no
uniformisation, and no appeal to the smooth curve of the paper.
-/

import Erdos960.Main

namespace Erdos960
namespace Nodal

open Real

/-! ## Determinants -/

/-- The `3 × 3` determinant of three vectors of `ℝ³`, written out. Used for projective
collinearity: `det3 u v w = 0` says the three points of `ℙ²` lie on a line. -/
def det3 (u v w : ℝ × ℝ × ℝ) : ℝ :=
  u.1 * (v.2.1 * w.2.2 - v.2.2 * w.2.1)
    - u.2.1 * (v.1 * w.2.2 - v.2.2 * w.1)
    + u.2.2 * (v.1 * w.2.1 - v.2.1 * w.1)

/-- The `2 × 2` determinant attached to three points of the affine plane; it vanishes
exactly when they are collinear (`collinear_iff_det2`). -/
def det2 (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- **Collinearity in the plane is the vanishing of `det2`.** Mathlib states `Collinear`
through `vectorSpan`; this is the concrete form the rest of the file computes with. -/
theorem collinear_iff_det2 (p q r : ℝ × ℝ) :
    Collinear ℝ ({p, q, r} : Set (ℝ × ℝ)) ↔ det2 p q r = 0 := by
  constructor
  · intro h
    rw [collinear_iff_of_mem (Set.mem_insert p {q, r})] at h
    obtain ⟨v, hv⟩ := h
    obtain ⟨s, hs⟩ := hv q (by simp)
    obtain ⟨t, ht⟩ := hv r (by simp)
    have hq1 : q.1 - p.1 = s * v.1 := by rw [hs]; simp
    have hq2 : q.2 - p.2 = s * v.2 := by rw [hs]; simp
    have hr1 : r.1 - p.1 = t * v.1 := by rw [ht]; simp
    have hr2 : r.2 - p.2 = t * v.2 := by rw [ht]; simp
    simp only [det2, hq1, hq2, hr1, hr2]
    ring
  · intro h
    by_cases hqp : q = p
    · have hset : ({p, q, r} : Set (ℝ × ℝ)) = {p, r} := by rw [hqp]; simp
      rw [hset]
      exact collinear_pair ℝ p r
    · rw [collinear_iff_of_mem (Set.mem_insert p {q, r})]
      have hd : 0 < (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 := by
        rcases (by
          by_contra hcon
          push Not at hcon
          exact hqp (Prod.ext (by linarith [hcon.1]) (by linarith [hcon.2])) :
            q.1 - p.1 ≠ 0 ∨ q.2 - p.2 ≠ 0) with h1 | h1
        · positivity
        · positivity
      refine ⟨q - p, ?_⟩
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · -- the scalar is the orthogonal projection coefficient; `det2 = 0` makes it exact
        simp only [det2] at h
        refine ⟨((x.1 - p.1) * (q.1 - p.1) + (x.2 - p.2) * (q.2 - p.2))
                  / ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2), ?_⟩
        have h1 : ((x.1 - p.1) * (q.1 - p.1) + (x.2 - p.2) * (q.2 - p.2))
              / ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) * (q.1 - p.1) + p.1 = x.1 := by
          rw [div_mul_eq_mul_div, div_add' _ _ _ (ne_of_gt hd), div_eq_iff (ne_of_gt hd)]
          linear_combination (q.2 - p.2) * h
        have h2 : ((x.1 - p.1) * (q.1 - p.1) + (x.2 - p.2) * (q.2 - p.2))
              / ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) * (q.2 - p.2) + p.2 = x.2 := by
          rw [div_mul_eq_mul_div, div_add' _ _ _ (ne_of_gt hd), div_eq_iff (ne_of_gt hd)]
          linear_combination (-(q.1 - p.1)) * h
        exact Prod.ext (by simpa using h1.symm) (by simpa using h2.symm)

/-! ## The nodal cubic and its angle parametrisation -/

/-- Homogeneous coordinates of the point of the nodal cubic `Z(X² + Y²) = X³` at
parameter `φ`. The `π/6` shift is what makes the collinearity criterion read
`φ₁ + φ₂ + φ₃ ≡ 0 (mod π)` rather than `≡ π/2`. -/
noncomputable def Pt (φ : ℝ) : ℝ × ℝ × ℝ :=
  (cos (φ + π / 6), sin (φ + π / 6), cos (φ + π / 6) ^ 3)

/-- `Pt φ` really does lie on the cubic `Z(X² + Y²) = X³`. Not needed downstream; it
records that the parametrisation is of the advertised curve. -/
theorem Pt_mem_cubic (φ : ℝ) :
    (Pt φ).2.2 * ((Pt φ).1 ^ 2 + (Pt φ).2.1 ^ 2) = (Pt φ).1 ^ 3 := by
  simp only [Pt]
  linear_combination cos (φ + π / 6) ^ 3 * sin_sq_add_cos_sq (φ + π / 6)

/-- The collinearity identity, as a polynomial identity over any commutative ring, with
`sa, ca, …` standing for the sines and cosines of the three angles. Separating it from the
trigonometry keeps the proof a single `linear_combination`. -/
theorem det3_algebraic (sa ca sb cb sc cc : ℝ)
    (ea : sa ^ 2 + ca ^ 2 = 1) (eb : sb ^ 2 + cb ^ 2 = 1) (ec : sc ^ 2 + cc ^ 2 = 1) :
    ca * (sb * cc ^ 3 - cb ^ 3 * sc) - sa * (cb * cc ^ 3 - cb ^ 3 * cc)
        + ca ^ 3 * (cb * sc - sb * cc)
      = -((sb * ca - cb * sa) * (sc * ca - cc * sa) * (sc * cb - cc * sb)
            * (ca * cb * cc - ca * sb * sc - sa * cb * sc - sa * sb * cc)) := by
  linear_combination
    (ca * cb ^ 3 * cc ^ 2 * sc + ca * cb ^ 3 * sc ^ 3 - ca * cb ^ 2 * cc ^ 3 * sb
        - ca * cc ^ 3 * sb ^ 3 - cb ^ 3 * cc * sa * sc ^ 2 + cb * cc ^ 3 * sa * sb ^ 2) * ea
    + (-(ca ^ 3 * cb * cc ^ 2 * sc) - ca ^ 3 * cb * sc ^ 3 + ca ^ 3 * cc ^ 3 * sb
        + ca ^ 3 * cc * sb * sc ^ 2 - ca * cc ^ 3 * sb + cb * cc ^ 3 * sa) * eb
    + (-(ca ^ 3 * cb * sc) + ca ^ 3 * cc * sb + ca * cb ^ 3 * sc - cb ^ 3 * cc * sa) * ec

/-- The identity in terms of the three angles themselves, with the variables opaque so
that the expansion stops where it should. -/
theorem det3_angles (A B C : ℝ) :
    det3 (cos A, sin A, cos A ^ 3) (cos B, sin B, cos B ^ 3) (cos C, sin C, cos C ^ 3)
      = -(sin (B - A) * sin (C - A) * sin (C - B) * cos (A + B + C)) := by
  rw [sin_sub, sin_sub, sin_sub, cos_add, cos_add, sin_add]
  simp only [det3]
  linear_combination
    det3_algebraic (sin A) (cos A) (sin B) (cos B) (sin C) (cos C)
      (sin_sq_add_cos_sq A) (sin_sq_add_cos_sq B) (sin_sq_add_cos_sq C)

/-- **The collinearity identity.** The projective determinant of three points of the cubic
factors into the pairwise angle differences times the sine of the angle sum. Its vanishing
is therefore exactly `φ₁ + φ₂ + φ₃ ≡ 0 (mod π)`, once the angles are distinct mod `π`. -/
theorem det3_Pt (a b c : ℝ) :
    det3 (Pt a) (Pt b) (Pt c)
      = sin (b - a) * sin (c - a) * sin (c - b) * sin (a + b + c) := by
  have hkey := det3_angles (a + π / 6) (b + π / 6) (c + π / 6)
  have hb : (b + π / 6) - (a + π / 6) = b - a := by ring
  have hc : (c + π / 6) - (a + π / 6) = c - a := by ring
  have hcb : (c + π / 6) - (b + π / 6) = c - b := by ring
  have hs : (a + π / 6) + (b + π / 6) + (c + π / 6) = (a + b + c) + π / 2 := by ring
  rw [hb, hc, hcb, hs] at hkey
  have hcos : cos ((a + b + c) + π / 2) = -sin (a + b + c) := by
    rw [cos_add, cos_pi_div_two, sin_pi_div_two]; ring
  rw [hcos] at hkey
  rw [Pt, Pt, Pt, hkey]
  ring

/-! ## The affine chart

`Pt` lands in the projective plane, and one point of a finite subgroup can sit on the line
at infinity of any fixed chart. So the chart is chosen *after* the subgroup: divide by the
linear form vanishing on two reference points whose angles are `π/(4N)` and `π/(2N)`. The
third intersection of that line with the cubic is at angle `-3π/(4N)`, and none of the three
is congruent mod `π` to any `kπ/N`, for the elementary reason that `1`, `2` and `-3` are not
divisible by `4`. Projective transformations preserve collinearity, so the criterion
survives the chart unchanged. -/

/-- The linear form vanishing at the two reference points `p` and `q`. -/
noncomputable def lform (p q v : ℝ × ℝ × ℝ) : ℝ := det3 v p q

/-- The affine chart determined by the reference points: send `[X : Y : Z]` to
`(X / L, Y / L)` where `L` is the linear form vanishing at `p` and `q`. -/
noncomputable def chart (p q v : ℝ × ℝ × ℝ) : ℝ × ℝ :=
  (v.1 / lform p q v, v.2.1 / lform p q v)

/-- Dividing each homogeneous coordinate triple by its own last entry turns the `3 × 3`
determinant into the planar one. Pure algebra, stated separately to keep each `ring` small. -/
theorem det2_div (Xu Yu Lu Xv Yv Lv Xw Yw Lw : ℝ)
    (hu : Lu ≠ 0) (hv : Lv ≠ 0) (hw : Lw ≠ 0) :
    det2 (Xu / Lu, Yu / Lu) (Xv / Lv, Yv / Lv) (Xw / Lw, Yw / Lw)
      = (Xu * (Yv * Lw - Lv * Yw) - Yu * (Xv * Lw - Lv * Xw) + Lu * (Xv * Yw - Yv * Xw))
          / (Lu * Lv * Lw) := by
  simp only [det2]
  field_simp
  ring

/-- Replacing the third homogeneous coordinate by the linear form `lform p q` rescales the
determinant by `p.1 * q.2.1 - p.2.1 * q.1`, the coefficient of that coordinate in the form. -/
theorem det3_with_lform (p q u v w : ℝ × ℝ × ℝ) :
    u.1 * (v.2.1 * lform p q w - lform p q v * w.2.1)
        - u.2.1 * (v.1 * lform p q w - lform p q v * w.1)
        + lform p q u * (v.1 * w.2.1 - v.2.1 * w.1)
      = (p.1 * q.2.1 - p.2.1 * q.1) * det3 u v w := by
  simp only [lform, det3]
  ring

/-- **Collinearity survives the chart.** The planar determinant of three charted points is
the projective determinant, up to the factor `p.1 * q.2.1 - p.2.1 * q.1` and the three
denominators. -/
theorem det2_chart (p q u v w : ℝ × ℝ × ℝ)
    (hu : lform p q u ≠ 0) (hv : lform p q v ≠ 0) (hw : lform p q w ≠ 0) :
    det2 (chart p q u) (chart p q v) (chart p q w)
      = (p.1 * q.2.1 - p.2.1 * q.1) * det3 u v w
          / (lform p q u * lform p q v * lform p q w) := by
  simp only [chart]
  rw [det2_div _ _ _ _ _ _ _ _ _ hu hv hw, det3_with_lform]

/-- The charted points are collinear exactly when the projective determinant vanishes. -/
theorem collinear_chart_iff (p q u v w : ℝ × ℝ × ℝ)
    (hpq : p.1 * q.2.1 - p.2.1 * q.1 ≠ 0)
    (hu : lform p q u ≠ 0) (hv : lform p q v ≠ 0) (hw : lform p q w ≠ 0) :
    Collinear ℝ ({chart p q u, chart p q v, chart p q w} : Set (ℝ × ℝ))
      ↔ det3 u v w = 0 := by
  rw [collinear_iff_det2, det2_chart p q u v w hu hv hw, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact (mul_eq_zero.mp h).resolve_left hpq
    · exact absurd h (by exact mul_ne_zero (mul_ne_zero hu hv) hw)
  · intro h
    exact Or.inl (by rw [h, mul_zero])

/-! ## Rational angles

Every angle in play is `j * π / (4 * N)` for an integer `j`: the group points use
`j = 4k`, the two reference points use `j = 1` and `j = 2`, and the third intersection of
the reference line uses `j = -3`. Vanishing of a sine is then divisibility of `j` by
`4 * N`, and the three reference values are ruled out by looking mod `4` alone. -/

/-- The angle `j * π / (4 * N)`. -/
noncomputable def ang (N : ℕ) (j : ℤ) : ℝ := (j : ℝ) * π / (4 * N)

theorem ang_sub (N : ℕ) (hN : (N : ℝ) ≠ 0) (i j : ℤ) :
    ang N j - ang N i = ang N (j - i) := by
  simp only [ang, Int.cast_sub]
  field_simp

theorem ang_add3 (N : ℕ) (hN : (N : ℝ) ≠ 0) (i j k : ℤ) :
    ang N i + ang N j + ang N k = ang N (i + j + k) := by
  simp only [ang, Int.cast_add]
  field_simp

/-- A sine at a rational angle vanishes exactly when `4 * N` divides the numerator. -/
theorem sin_ang_eq_zero_iff {N : ℕ} (hN : 0 < N) (j : ℤ) :
    sin (ang N j) = 0 ↔ (4 * N : ℤ) ∣ j := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have : (n : ℝ) * π * (4 * N) = (j : ℝ) * π := by
      rw [hn]; simp only [ang]; field_simp
    have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
    have hcast : ((4 * N * n : ℤ) : ℝ) = (j : ℝ) := by
      push_cast
      field_simp at this
      linarith [this]
    exact_mod_cast hcast.symm
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    simp only [ang]
    push_cast
    field_simp

/-- The sine does not vanish when the numerator is not a multiple of `4`. This is the whole
reason the reference angles were taken over `4 * N` rather than over `N`. -/
theorem sin_ang_ne_zero {N : ℕ} (hN : 0 < N) {j : ℤ} (hj : ¬ (4 : ℤ) ∣ j) :
    sin (ang N j) ≠ 0 := by
  rw [Ne, sin_ang_eq_zero_iff hN]
  intro hdvd
  exact hj (dvd_trans ⟨(N : ℤ), by ring⟩ hdvd)

/-- The group point at `k`, in homogeneous coordinates. -/
noncomputable def gpt (N : ℕ) (k : ℤ) : ℝ × ℝ × ℝ := Pt (ang N (4 * k))

/-- First reference point of the chart, at angle `π / (4 * N)`. -/
noncomputable def ref₁ (N : ℕ) : ℝ × ℝ × ℝ := Pt (ang N 1)

/-- Second reference point of the chart, at angle `2 * π / (4 * N)`. -/
noncomputable def ref₂ (N : ℕ) : ℝ × ℝ × ℝ := Pt (ang N 2)

/-- The cross product of the first two homogeneous coordinates of two curve points is the
sine of the angle difference; the `π/6` shift cancels. -/
theorem Pt_cross (a b : ℝ) :
    (Pt a).1 * (Pt b).2.1 - (Pt a).2.1 * (Pt b).1 = sin (b - a) := by
  have h : b - a = (b + π / 6) - (a + π / 6) := by ring
  rw [h, sin_sub]
  simp only [Pt]
  ring

/-- The chart is nondegenerate: the two reference points span distinct directions. -/
theorem ref_nondegenerate {N : ℕ} (hN : 0 < N) :
    (ref₁ N).1 * (ref₂ N).2.1 - (ref₁ N).2.1 * (ref₂ N).1 ≠ 0 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [ref₁, ref₂, Pt_cross, ang_sub N hN']
  exact sin_ang_ne_zero hN (by decide)

/-- No group point lies on the reference line, so the chart is defined at all of them. -/
theorem lform_gpt_ne_zero {N : ℕ} (hN : 0 < N) (k : ℤ) :
    lform (ref₁ N) (ref₂ N) (gpt N k) ≠ 0 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [lform, gpt, ref₁, ref₂, det3_Pt]
  rw [ang_sub N hN', ang_sub N hN', ang_sub N hN', ang_add3 N hN']
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · exact sin_ang_ne_zero hN (by omega)
  · exact sin_ang_ne_zero hN (by omega)
  · exact sin_ang_ne_zero hN (by decide)
  · exact sin_ang_ne_zero hN (by omega)

/-! ## The model on `ZMod N`

The group point of `k : ZMod N` sits at angle `4 * k.val * π / (4 * N) = k.val * π / N`, and
the collinearity identity turns the criterion into `N ∣ x.val + y.val + z.val`. -/

variable {N : ℕ}

/-- The embedding of `ZMod N` into the affine plane. -/
noncomputable def emb [NeZero N] (k : ZMod N) : ℝ × ℝ :=
  chart (ref₁ N) (ref₂ N) (gpt N (k.val : ℤ))

theorem pos_of_neZero [NeZero N] : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)

/-- Two residues whose `val`s differ by a multiple of `N` are equal. -/
theorem eq_of_dvd_val_sub [NeZero N] {x y : ZMod N}
    (h : (N : ℤ) ∣ ((y.val : ℤ) - (x.val : ℤ))) : x = y := by
  have hx : (x.val : ℤ) < (N : ℤ) := by exact_mod_cast ZMod.val_lt x
  have hy : (y.val : ℤ) < (N : ℤ) := by exact_mod_cast ZMod.val_lt y
  have hx0 : (0 : ℤ) ≤ (x.val : ℤ) := Int.natCast_nonneg _
  have hy0 : (0 : ℤ) ≤ (y.val : ℤ) := Int.natCast_nonneg _
  obtain ⟨c, hc⟩ := h
  have hc0 : c = 0 := by
    rcases lt_trichotomy c 0 with hneg | h0 | hpos
    · nlinarith
    · exact h0
    · nlinarith
  rw [hc0, mul_zero] at hc
  exact ZMod.val_injective N (by exact_mod_cast (by linarith : (x.val : ℤ) = (y.val : ℤ)))

/-- Distinct residues give a nonvanishing sine, which is the nondegeneracy the criterion
needs: the three pairwise factors of the collinearity identity never vanish. -/
theorem sin_ang_sub_ne_zero [NeZero N] {x y : ZMod N} (hxy : x ≠ y) :
    sin (ang N (4 * (y.val : ℤ) - 4 * (x.val : ℤ))) ≠ 0 := by
  rw [Ne, sin_ang_eq_zero_iff pos_of_neZero]
  intro hdvd
  refine hxy (eq_of_dvd_val_sub ?_).symm
  obtain ⟨c, hc⟩ := hdvd
  exact ⟨-c, by linarith⟩

/-- `N ∣ x.val + y.val + z.val` is exactly `x + y + z = 0`. -/
theorem dvd_val_sum_iff [NeZero N] (x y z : ZMod N) :
    (N : ℤ) ∣ ((x.val : ℤ) + (y.val : ℤ) + (z.val : ℤ)) ↔ x + y + z = 0 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  simp [ZMod.natCast_val, ZMod.cast_id]

/-- **The collinearity criterion on `ZMod N`.** -/
theorem collinear_emb_iff [NeZero N] {x y z : ZMod N}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    Collinear ℝ ({emb x, emb y, emb z} : Set (ℝ × ℝ)) ↔ x + y + z = 0 := by
  have hN : 0 < N := pos_of_neZero
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [emb, emb, emb,
    collinear_chart_iff _ _ _ _ _ (ref_nondegenerate hN)
      (lform_gpt_ne_zero hN _) (lform_gpt_ne_zero hN _) (lform_gpt_ne_zero hN _)]
  simp only [gpt, det3_Pt]
  rw [ang_sub N hN', ang_sub N hN', ang_sub N hN', ang_add3 N hN']
  rw [mul_eq_zero, mul_eq_zero, mul_eq_zero]
  constructor
  · rintro (((h | h) | h) | h)
    · exact absurd h (sin_ang_sub_ne_zero hxy)
    · exact absurd h (sin_ang_sub_ne_zero hxz)
    · exact absurd h (sin_ang_sub_ne_zero hyz)
    · rw [sin_ang_eq_zero_iff hN] at h
      refine (dvd_val_sum_iff x y z).mp ?_
      obtain ⟨c, hc⟩ := h
      exact ⟨c, by linarith⟩
  · intro h
    refine Or.inr ?_
    rw [sin_ang_eq_zero_iff hN]
    have hdvd := (dvd_val_sum_iff x y z).mpr h
    obtain ⟨c, hc⟩ := hdvd
    exact ⟨c, by rw [show 4 * (x.val : ℤ) + 4 * (y.val : ℤ) + 4 * (z.val : ℤ)
      = 4 * ((x.val : ℤ) + (y.val : ℤ) + (z.val : ℤ)) from by ring, hc]; ring⟩

/-- The embedding is injective: two residues with the same image would give a vanishing
angle-difference sine. -/
theorem emb_injective [NeZero N] : Function.Injective (emb : ZMod N → ℝ × ℝ) := by
  have hN : 0 < N := pos_of_neZero
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  intro x y hxy
  by_contra hne
  have hLx := lform_gpt_ne_zero hN (x.val : ℤ)
  have hLy := lform_gpt_ne_zero hN (y.val : ℤ)
  set u := gpt N (x.val : ℤ) with hu
  set v := gpt N (y.val : ℤ) with hv
  -- the two charted points agree, so the homogeneous triples are proportional
  have h1 : u.1 / lform (ref₁ N) (ref₂ N) u = v.1 / lform (ref₁ N) (ref₂ N) v := by
    have := congrArg Prod.fst hxy
    simpa [emb, chart, hu, hv] using this
  have h2 : u.2.1 / lform (ref₁ N) (ref₂ N) u = v.2.1 / lform (ref₁ N) (ref₂ N) v := by
    have := congrArg (fun p => p.2) hxy
    simpa [emb, chart, hu, hv] using this
  rw [div_eq_div_iff hLx hLy] at h1 h2
  -- hence the cross product vanishes, contradicting distinctness of the angles
  have hcross : u.1 * v.2.1 - u.2.1 * v.1 = 0 := by
    have hkey : (u.1 * v.2.1 - u.2.1 * v.1) * lform (ref₁ N) (ref₂ N) u = 0 := by
      linear_combination u.2.1 * h1 - u.1 * h2
    exact (mul_eq_zero.mp hkey).resolve_right hLx
  rw [hu, hv, gpt, gpt, Pt_cross, ang_sub N hN'] at hcross
  exact sin_ang_sub_ne_zero hne hcross

/-- **Paper Lemma 2.2, proved.** Every `ZMod N` with `N ≠ 0` carries a `CurveModel`. -/
noncomputable def curveModel [NeZero N] : CurveModel (ZMod N) where
  emb := emb
  emb_injective := emb_injective
  collinear_iff := fun _ _ _ hxy hyz hxz => collinear_emb_iff hxy hyz hxz

end Nodal

/-- **`CurveModelAssumption` is a theorem, not an assumption.** This discharges the only
hypothesis of `erdos960` that gate 0 had routed around. -/
theorem curveModelAssumption (m : ℕ) (hm : 0 < m) : CurveModelAssumption m :=
  have : NeZero (7 * m) := ⟨by omega⟩
  ⟨Nodal.curveModel⟩

/-- **Theorem 2.1 of the paper, unconditionally.**

`erdos960` carries the paper's Lemma 2.2 as the hypothesis `hcurve`. `curveModelAssumption`
proves that hypothesis for every `m > 0`, so this version has no hypotheses beyond the
paper's own `r ≥ 3`, `k ≥ 4`, `n ≥ 72`. -/
theorem erdos960_unconditional (r k n : ℕ) (hr : 3 ≤ r) (hk : 4 ≤ k) (hn : 72 ≤ n) :
    (n : ℝ) ^ 2 / 12 - 10 * (n : ℝ) / 3 ≤ (F r k n : ℝ) :=
  erdos960 r k n hr hk hn fun m hm => curveModelAssumption m hm

end Erdos960
