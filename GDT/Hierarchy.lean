/-
# Hierarchy of Controls, ASME Y14.5.1 §6.2

Y14.5.1 §6.2 states:

> An orientation tolerance, when applied to a plane surface, controls flatness
> to the extent of the orientation tolerance. When the flatness control in the
> orientation tolerance is not sufficient, a separate flatness tolerance should
> be considered. An orientation tolerance does not control the location of
> features. [6.2]

We prove the formal versions of these containment relationships:

  satisfiesPlanarOrientation  ⟹  satisfiesFlatness
  satisfiesCylindricalOrientation  ⟹  satisfiesStraightness
  satisfiesPosition (aligned datum)  ⟹  satisfiesCylindricalOrientation

The proof in each case is that the witness for the stronger control is also
a valid witness for the weaker one, the extra constraint (datum angle or true
position) is simply dropped.
-/

import GDT.Tolerance.Form
import GDT.Tolerance.Orientation
import GDT.Tolerance.Position

noncomputable section

/-! ## Flatness equivalence: scalar-offset vs. reference-point form

    The standard's §5.4.2.1 writes the zone as `|hat(T) . (P - A)| ≤ t/2`.
    `satisfiesFlatness` uses `|inner n p - c| ≤ t/2`, absorbing vec(A) into the
    scalar `c = ⟨n, A⟩`. The two forms are equivalent: setting `c = ⟨n, A⟩` gives
    `inner n (p - A) = inner n p - ⟨n, A⟩ = inner n p - c`. -/

/-- `satisfiesFlatness` is equivalent to the standard's reference-point form. -/
theorem satisfiesFlatness_iff (S : Set Point3) (t : ℝ) :
    satisfiesFlatness S t ↔
    ∃ (n : Vec3) (A : Point3), ‖n‖ = 1 ∧
      ∀ p ∈ S, |@inner ℝ _ _ n (p - A)| ≤ t / 2 := by
  constructor
  · rintro ⟨n, c, hn, hS⟩
    refine ⟨n, c • n, hn, fun p hp => ?_⟩
    convert hS p hp using 2
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow, mul_one]
  · rintro ⟨n, A, hn, hS⟩
    refine ⟨n, @inner ℝ _ _ n A, hn, fun p hp => ?_⟩
    convert hS p hp using 2
    rw [inner_sub_right]

/-! ## Planar orientation equivalence: scalar-offset vs. reference-point form -/

/-- `satisfiesPlanarOrientation` is equivalent to the standard's reference-point form.

    Analogous to `satisfiesFlatness_iff`: with `c = ⟨n, A⟩` the zone conditions
    `|inner n p − c| ≤ t/2` and `|inner n (p − A)| ≤ t/2` are the same. The angle
    constraint `|inner n datum.dir| = |sin θ|` is unchanged in both directions. -/
theorem satisfiesPlanarOrientation_iff
    (S : Set Point3) (t : ℝ) (datum : DatumDir) (θ : ℝ) :
    satisfiesPlanarOrientation S t datum θ ↔
    ∃ (n : Vec3) (A : Point3), ‖n‖ = 1 ∧
      |@inner ℝ _ _ n datum.dir| = |Real.sin θ| ∧
      ∀ p ∈ S, |@inner ℝ _ _ n (p - A)| ≤ t / 2 := by
  constructor
  · rintro ⟨n, c, hn, hang, hS⟩
    refine ⟨n, c • n, hn, hang, fun p hp => ?_⟩
    convert hS p hp using 2
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow, mul_one]
  · rintro ⟨n, A, hn, hang, hS⟩
    refine ⟨n, @inner ℝ _ _ n A, hn, hang, fun p hp => ?_⟩
    convert hS p hp using 2
    rw [inner_sub_right]

/-! ## Orientation controls form (§6.2) -/

/-- **Planar orientation implies flatness** (ASME Y14.5.1 §6.2).
    The orientation zone is a flatness zone with an additional datum angle
    constraint on the zone direction. Dropping the constraint gives flatness. -/
theorem orientation_controls_flatness
    {S : Set Point3} {t : ℝ} {datum : DatumDir} {θ : ℝ}
    (h : satisfiesPlanarOrientation S t datum θ) :
    satisfiesFlatness S t := by
  obtain ⟨n, c, hn, _, hS⟩ := h
  exact ⟨n, c, hn, hS⟩

/-- **Cylindrical orientation implies straightness** (ASME Y14.5.1 §6.2).
    The cylindrical orientation zone is a straightness zone with an additional
    datum angle constraint on the axis direction. Dropping the constraint gives
    straightness. -/
theorem orientation_controls_straightness
    {S : Set Point3} {t : ℝ} {datum : DatumDir} {θ : ℝ}
    (h : satisfiesCylindricalOrientation S t datum θ) :
    satisfiesStraightness S t := by
  obtain ⟨L, _, hS⟩ := h
  exact ⟨L, hS⟩

/-! ## Position controls orientation -/

/-- **Position implies cylindrical orientation** (for an aligned datum).
    When the true-position axis is parallel (or anti-parallel) to the datum
    direction, the cylindrical position zone is a cylindrical orientation zone
    with basic angle θ = 0.

    The angle constraint `|cos 0| = 1` is satisfied because parallel unit vectors
    have inner product ±1. The point-set constraint is unchanged: both use
    `distToLine p L ≤ t/2` with the same axis and the same tolerance. -/
theorem position_controls_cylindrical_orientation
    {S : Set Point3} {t : ℝ} {truePos : Line3} {datum : DatumDir}
    (hpar : truePos.dir = datum.dir ∨ truePos.dir = -datum.dir)
    (h : satisfiesPosition S t truePos) :
    satisfiesCylindricalOrientation S t datum 0 := by
  refine ⟨truePos, ?_, h⟩
  rw [Real.cos_zero, abs_one]
  rcases hpar with hd | hd
  · rw [hd, real_inner_self_eq_norm_sq, datum.unit, one_pow, abs_one]
  · rw [hd, inner_neg_left, real_inner_self_eq_norm_sq, datum.unit, one_pow,
        abs_neg, abs_one]

end
