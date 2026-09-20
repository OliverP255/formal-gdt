/-
# Lines in ℝ³ and distance-to-line

Distance from a point to a line, defined via orthogonal projection residual.
-/

import GDT.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct

noncomputable section

open Matrix WithLp InnerProductGeometry

/-- A directed line in ℝ³: a base point and a unit direction vector. -/
structure Line3 where
  point : Point3
  dir : Vec3
  unit : ‖dir‖ = 1

/-- Distance from a point to a line, defined as the norm of the
    component of (p - L.point) orthogonal to L.dir. -/
def distToLine (p : Point3) (L : Line3) : ℝ :=
  let v := p - L.point
  ‖v - (inner (𝕜 := ℝ) v L.dir) • L.dir‖

theorem distToLine_nonneg (p : Point3) (L : Line3) : 0 ≤ distToLine p L :=
  norm_nonneg _

theorem distToLine_self (L : Line3) : distToLine L.point L = 0 := by
  simp [distToLine]

theorem distToLine_on_line (L : Line3) (s : ℝ) :
    distToLine (L.point + s • L.dir) L = 0 := by
  simp only [distToLine, add_sub_cancel_left]
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, L.unit, one_pow, mul_one,
    sub_self, norm_zero]

/-- Translating a point along the line direction does not change its
    distance to the line. -/
theorem distToLine_translate (p : Point3) (L : Line3) (s : ℝ) :
    distToLine (p + s • L.dir) L = distToLine p L := by
  simp only [distToLine]
  congr 1
  set v := p - L.point
  have step : p + s • L.dir - L.point = v + s • L.dir := by simp [v]; abel
  rw [step, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    L.unit, one_pow, mul_one, add_smul]
  abel

/-! ## Cross-product bridge lemma

Why this is needed: distToLine is defined via projection residual to avoid
cross-product API friction. But Y14.5.1 §5.4.1.1, §5.4.4, and §7.2.2 all state
their tolerance zones using |hat(T) x (P - A)|. Without a proof that these are
equal, three definitions (satisfiesStraightness, satisfiesCylindricity,
satisfiesPosition) only match the standard up to an unverified equivalence claim.
This lemma closes that gap: it proves equality holds for any Line3 (unit direction).
-/

/-- The squared distance to a line equals ‖v‖² − ⟨v, d⟩²
    where v = p − L.point and d = L.dir. -/
private lemma distToLine_sq (p : Point3) (L : Line3) :
    (distToLine p L) ^ 2 =
    ‖p - L.point‖ ^ 2 - (inner (𝕜 := ℝ) (p - L.point) L.dir) ^ 2 := by
  simp only [distToLine]
  set v := p - L.point
  set c := @inner ℝ _ _ v L.dir with hc
  have hkey : @inner ℝ _ _ v (c • L.dir) = c ^ 2 := by
    rw [real_inner_smul_right, hc, sq]
  have hnorm : ‖c • L.dir‖ ^ 2 = c ^ 2 := by
    have hunit : ‖L.dir‖ ^ 2 = 1 := by rw [L.unit]; norm_num
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hunit, mul_one]
  linarith [norm_sub_sq_real v (c • L.dir)]

/-- **Cross-product bridge lemma.** The projection-residual definition of
    distToLine equals the norm of the cross product L.dir × (p − L.point),
    matching the |hat(T) x (P − A)| formula used in Y14.5.1.

    The cross product of EuclideanSpace ℝ (Fin 3) elements uses ofLp to
    coerce to Fin 3 → ℝ (where ⨯₃ is defined) and toLp 2 to return to
    the Euclidean space type. -/
theorem distToLine_eq_norm_cross (p : Point3) (L : Line3) :
    distToLine p L =
    ‖(toLp 2 (ofLp L.dir ⨯₃ ofLp (p - L.point)) : EuclideanSpace ℝ (Fin 3))‖ := by
  set v := p - L.point
  have hnn1 : 0 ≤ distToLine p L := distToLine_nonneg p L
  have hnn2 : 0 ≤ ‖(toLp 2 (ofLp L.dir ⨯₃ ofLp v) : EuclideanSpace ℝ (Fin 3))‖ := norm_nonneg _
  -- Show both squares are equal: ‖v‖² - ⟨L.dir, v⟩²
  have hsq : (distToLine p L) ^ 2 =
      ‖(toLp 2 (ofLp L.dir ⨯₃ ofLp v) : EuclideanSpace ℝ (Fin 3))‖ ^ 2 := by
    rw [distToLine_sq]
    -- Lagrange identity: ‖d × v‖² = ‖d‖²‖v‖² − ⟨d,v⟩²
    have hlag : ‖(toLp 2 (ofLp L.dir ⨯₃ ofLp v) : EuclideanSpace ℝ (Fin 3))‖ ^ 2 =
        ‖L.dir‖ ^ 2 * ‖v‖ ^ 2 - (inner (𝕜 := ℝ) L.dir v) ^ 2 := by
      simp_rw [norm_sq_eq_re_inner (𝕜 := ℝ), EuclideanSpace.inner_eq_star_dotProduct,
        star_trivial, RCLike.re_to_real, cross_dot_cross,
        dotProduct_comm (ofLp v) (ofLp L.dir), sq]
    rw [hlag, L.unit, one_pow, one_mul, real_inner_comm]
  -- Conclude from equal nonneg squares
  calc distToLine p L
      = Real.sqrt ((distToLine p L) ^ 2)    := (Real.sqrt_sq hnn1).symm
    _ = Real.sqrt (‖(toLp 2 (ofLp L.dir ⨯₃ ofLp v) :
          EuclideanSpace ℝ (Fin 3))‖ ^ 2)   := by rw [hsq]
    _ = ‖(toLp 2 (ofLp L.dir ⨯₃ ofLp v) : EuclideanSpace ℝ (Fin 3))‖ := Real.sqrt_sq hnn2

end
