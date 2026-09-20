/-
# Orientation Tolerances, ASME Y14.5.1 §6.4

Planar and cylindrical orientation zones, per §6.4.1 and §6.4.2.

Datums are modelled as unit direction vectors (DatumDir). This captures
exactly the information used in the angle constraints of §6.4.1 and §6.4.2
(hat(D_1) appears only in the dot-product condition on the zone direction).
Full datum reference frame construction is not needed for the hierarchy theorems.
-/

import GDT.Geometry.Line

noncomputable section

/-- A datum direction: a unit vector hat(D_1) as used in Y14.5.1 §6.4.1–6.4.2.
    Models either a datum axis direction or a datum plane normal. -/
structure DatumDir where
  dir : Vec3
  unit : ‖dir‖ = 1

/-! ## Planar Orientation, Y14.5.1 §6.4.1 -/

/-- A set S satisfies a planar orientation tolerance t relative to a datum
    plane (with normal datum.dir) at basic angle θ when it lies between two
    parallel planes separated by t and oriented at angle θ to the datum.
    Per Y14.5.1 §6.4.1 (Y14.5.1-definitions.md#planar-orientation).

    §6.4.1(a) Definition:

    > A planar orientation zone is a volume consisting of all points vec(P)
    > satisfying the condition
    >
    >     |hat(T) . (vec(P) - vec(A))| <= t/2
    >
    > The planar orientation zone is oriented such that, if hat(D_1) is the
    > direction vector of the primary datum, then
    >
    >     |hat(T) . hat(D_1)| = |sin(theta)|   for a primary datum plane

    The case |hat(T) . hat(D_1)| = |cos(theta)| for a primary datum axis is not
    modelled here. That case would use cos in place of sin; our datum is treated
    as a plane normal (hat(D_1) = normal to datum plane) throughout this definition.

    Our definition uses the reparametrized form |inner n p - c| ≤ t/2 (with
    c = ⟨n, A⟩) consistent with satisfiesFlatness in Form.lean. The
    equivalence to the standard's (P - A) form is proved in Hierarchy.lean
    as satisfiesPlanarOrientation_iff. -/
def satisfiesPlanarOrientation (S : Set Point3) (t : ℝ) (datum : DatumDir) (θ : ℝ) : Prop :=
  ∃ (n : Vec3) (c : ℝ), ‖n‖ = 1 ∧
    |@inner ℝ _ _ n datum.dir| = |Real.sin θ| ∧
    ∀ p ∈ S, |@inner ℝ _ _ n p - c| ≤ t / 2

theorem planarOrientation_monotone {S : Set Point3} {t t' : ℝ} {d : DatumDir} {θ : ℝ}
    (h : satisfiesPlanarOrientation S t d θ) (hle : t ≤ t') :
    satisfiesPlanarOrientation S t' d θ := by
  obtain ⟨n, c, hn, hang, hS⟩ := h
  exact ⟨n, c, hn, hang, fun p hp => le_trans (hS p hp) (by linarith)⟩

theorem planarOrientation_subset {S S' : Set Point3} {t : ℝ} {d : DatumDir} {θ : ℝ}
    (h : satisfiesPlanarOrientation S t d θ) (hsub : S' ⊆ S) :
    satisfiesPlanarOrientation S' t d θ := by
  obtain ⟨n, c, hn, hang, hS⟩ := h
  exact ⟨n, c, hn, hang, fun p hp => hS p (hsub hp)⟩

/-! ## Cylindrical Orientation, Y14.5.1 §6.4.2 -/

/-- A set S satisfies a cylindrical orientation tolerance t relative to a
    datum axis (direction datum.dir) at basic angle θ when its axis lies
    within a cylinder of diameter t oriented at angle θ to the datum.
    Per Y14.5.1 §6.4.2 (Y14.5.1-definitions.md#cylindrical-orientation).

    §6.4.2(a) Definition:

    > A cylindrical orientation zone is a volume consisting of all points vec(P)
    > satisfying the condition
    >
    >     |hat(T) x (vec(P) - vec(A))| <= t/2
    >
    > The axis of the cylindrical orientation zone is oriented such that, if
    > hat(D_1) is the direction vector of the primary datum, then
    >
    >     |hat(T) . hat(D_1)| = |cos(theta)|   for a primary datum axis

    The case |hat(T) . hat(D_1)| = |sin(theta)| for a primary datum plane is not
    modelled here. That case would use sin in place of cos; our datum is treated
    as an axis direction (hat(D_1) = axis direction vector) throughout this definition.

    We use distToLine for the cross-product magnitude, justified by the
    bridge lemma distToLine_eq_norm_cross in Geometry/Line.lean. -/
def satisfiesCylindricalOrientation (S : Set Point3) (t : ℝ) (datum : DatumDir) (θ : ℝ) : Prop :=
  ∃ (L : Line3), |@inner ℝ _ _ L.dir datum.dir| = |Real.cos θ| ∧
    ∀ p ∈ S, distToLine p L ≤ t / 2

theorem cylindricalOrientation_monotone {S : Set Point3} {t t' : ℝ} {d : DatumDir} {θ : ℝ}
    (h : satisfiesCylindricalOrientation S t d θ) (hle : t ≤ t') :
    satisfiesCylindricalOrientation S t' d θ := by
  obtain ⟨L, hang, hS⟩ := h
  exact ⟨L, hang, fun p hp => le_trans (hS p hp) (by linarith)⟩

theorem cylindricalOrientation_subset {S S' : Set Point3} {t : ℝ} {d : DatumDir} {θ : ℝ}
    (h : satisfiesCylindricalOrientation S t d θ) (hsub : S' ⊆ S) :
    satisfiesCylindricalOrientation S' t d θ := by
  obtain ⟨L, hang, hS⟩ := h
  exact ⟨L, hang, fun p hp => hS p (hsub hp)⟩

end
