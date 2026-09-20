/-
Form Tolerances, ASME Y14.5.1 §5.4

Definitions and basic theorems for the four form tolerances:
flatness, straightness, circularity, cylindricity.
-/

import GDT.Basic
import GDT.Geometry.Line
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

/-! ## Flatness (§5.4.2) -/

/-- flatness tolerance (t): lies between two parallel planes separated by t. (§5.4.2.1) -/
def satisfiesFlatness (S : Set Point3) (t : ℝ) : Prop :=
  ∃ (n : Vec3) (c : ℝ), ‖n‖ = 1 ∧
    ∀ p ∈ S, |@inner ℝ _ _ n p - c| ≤ t / 2

theorem flatness_monotone {S : Set Point3} {t t' : ℝ}
    (h : satisfiesFlatness S t) (hle : t ≤ t') : satisfiesFlatness S t' := by
  obtain ⟨n, c, hn, hS⟩ := h
  exact ⟨n, c, hn, fun p hp => le_trans (hS p hp) (by linarith)⟩

theorem flatness_subset {S S' : Set Point3} {t : ℝ}
    (h : satisfiesFlatness S t) (hsub : S' ⊆ S) : satisfiesFlatness S' t := by
  obtain ⟨n, c, hn, hS⟩ := h
  exact ⟨n, c, hn, fun p hp => hS p (hsub hp)⟩

/-- points within δ of some plane satisfy flatness 2δ. -/
theorem bounded_deviation_flatness {S : Set Point3} {δ : ℝ} {n : Vec3} {c : ℝ}
    (hn : ‖n‖ = 1) (hbound : ∀ p ∈ S, |@inner ℝ _ _ n p - c| ≤ δ) :
    satisfiesFlatness S (2 * δ) :=
  ⟨n, c, hn, fun p hp => by linarith [hbound p hp]⟩

/-- a perfect plane satisfies flatness 0. -/
theorem plane_satisfies_flatness_zero (n : Vec3) (c : ℝ) (hn : ‖n‖ = 1) :
    satisfiesFlatness {p : Point3 | @inner ℝ _ _ n p = c} 0 :=
  ⟨n, c, hn, fun p hp => by simp [Set.mem_ofPred_eq.mp hp]⟩

/-! ## Straightness (§5.4.1) -/

/-- straightness tolerance (t): lies within a cylinder of diameter t around some line. (§5.4.1.1) -/
def satisfiesStraightness (S : Set Point3) (t : ℝ) : Prop :=
  ∃ (L : Line3), ∀ p ∈ S, distToLine p L ≤ t / 2

theorem straightness_monotone {S : Set Point3} {t t' : ℝ}
    (h : satisfiesStraightness S t) (hle : t ≤ t') : satisfiesStraightness S t' := by
  obtain ⟨L, hS⟩ := h
  exact ⟨L, fun p hp => le_trans (hS p hp) (by linarith)⟩

theorem straightness_subset {S S' : Set Point3} {t : ℝ}
    (h : satisfiesStraightness S t) (hsub : S' ⊆ S) : satisfiesStraightness S' t := by
  obtain ⟨L, hS⟩ := h
  exact ⟨L, fun p hp => hS p (hsub hp)⟩

/- Circularity (§5.4.3)
NOTE: Y14.5.1 allows curved spines; we restrict to a single cross-section. -/

/-- circularity tolerance (t): lies in a coplanar annular region of width t. (§5.4.3)

    Coplanarity is required so the definition isn't vacuous: without it, any finite
    set on a sphere could satisfy circularity 0 by moving the center off-plane. -/
def satisfiesCircularity (S : Set Point3) (t : ℝ) : Prop :=
  ∃ (center : Point3) (n : Vec3) (r : ℝ), ‖n‖ = 1 ∧ 0 < r ∧
    ∀ p ∈ S, @inner ℝ _ _ n (p - center) = 0 ∧ |dist center p - r| ≤ t / 2

theorem circularity_monotone {S : Set Point3} {t t' : ℝ}
    (h : satisfiesCircularity S t) (hle : t ≤ t') : satisfiesCircularity S t' := by
  obtain ⟨c, n, r, hn, hr, hS⟩ := h
  exact ⟨c, n, r, hn, hr, fun p hp => ⟨(hS p hp).1, le_trans (hS p hp).2 (by linarith)⟩⟩

theorem circularity_subset {S S' : Set Point3} {t : ℝ}
    (h : satisfiesCircularity S t) (hsub : S' ⊆ S) : satisfiesCircularity S' t := by
  obtain ⟨c, n, r, hn, hr, hS⟩ := h
  exact ⟨c, n, r, hn, hr, fun p hp => hS p (hsub hp)⟩

/-! ## Cylindricity (§5.4.4) -/

/-- cylindricity tolerance (t): lies between two coaxial cylinders of radii r ± t/2. (§5.4.4) -/
def satisfiesCylindricity (S : Set Point3) (t : ℝ) : Prop :=
  ∃ (L : Line3) (r : ℝ), 0 ≤ r ∧
    ∀ p ∈ S, |distToLine p L - r| ≤ t / 2

theorem cylindricity_monotone {S : Set Point3} {t t' : ℝ}
    (h : satisfiesCylindricity S t) (hle : t ≤ t') : satisfiesCylindricity S t' := by
  obtain ⟨L, r, hr, hS⟩ := h
  exact ⟨L, r, hr, fun p hp => le_trans (hS p hp) (by linarith)⟩

theorem cylindricity_subset {S S' : Set Point3} {t : ℝ}
    (h : satisfiesCylindricity S t) (hsub : S' ⊆ S) : satisfiesCylindricity S' t := by
  obtain ⟨L, r, hr, hS⟩ := h
  exact ⟨L, r, hr, fun p hp => hS p (hsub hp)⟩

/-- cylindricity implies circularity -/
theorem cylindricity_implies_circularity_of_distToLine_eq_dist
    {S : Set Point3} {t : ℝ} {L : Line3} {r : ℝ} {a : Point3} {n : Vec3}
    (hn : ‖n‖ = 1)
    (hr : 0 < r)
    (hbound : ∀ p ∈ S, |distToLine p L - r| ≤ t / 2)
    (hdist : ∀ p ∈ S, distToLine p L = dist a p)
    (hplane : ∀ p ∈ S, @inner ℝ _ _ n (p - a) = 0) :
    satisfiesCircularity S t :=
  ⟨a, n, r, hn, hr, fun p hp => ⟨hplane p hp, by rw [← hdist p hp]; exact hbound p hp⟩⟩

end
