/-
# Orientation Tolerances, ASME Y14.5.1 §6.4

Planar and cylindrical orientation zones, per §6.4.1 and §6.4.2.

Datums are modelled as unit direction vectors (DatumDir). 

This captures exactly the information used in the angle constraints of §6.4.1 and §6.4.2.
Full datum reference frame construction is not needed for the hierarchy theorems.
-/

import GDT.Geometry.Line

noncomputable section

/-- a unit datum direction hat(D_1), used in §6.4.1–6.4.2 as either a datum axis
    direction or a datum plane normal. -/
structure DatumDir where
  dir : Vec3
  unit : ‖dir‖ = 1

/-! ## Planar Orientation (§6.4.1) -/

/-- planar orientation tolerance (t) to a datum plane (normal datum.dir) at basic angle θ:
    lies between two parallel planes separated by t and oriented at angle θ to the datum. (§6.4.1)

    Only the primary-datum-plane case is modelled, not the
    primary-datum-axis case. Equivalence to the standard's (P - A) form is 
    satisfiesPlanarOrientation_iff in Hierarchy.lean. -/
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

/-! ## Cylindrical Orientation (§6.4.2) -/

/-- cylindrical orientation tolerance (t) to a datum axis (direction datum.dir) at basic
    angle θ: lies within a cylinder of diameter t oriented at angle θ to the datum. (§6.4.2)

    Only the primary-datum-axis case is modelled, not the primary-datum-plane case. 
    distToLine stands in for the cross-product magnitude, via distToLine_eq_norm_cross in Geometry/Line.lean. -/
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
