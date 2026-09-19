/-
# Form Tolerances, ASME Y14.5.1 §5.4

Definitions and basic theorems for the four form tolerances:
flatness, straightness, circularity, cylindricity.

Key results:
- `bounded_deviation_flatness`: process capability δ → tolerance 2δ suffices
- `cylindricity_implies_circularity`: cross-sections inherit the tolerance

**Note on tolerance sign**: All definitions allow `t < 0`. For `t < 0` and
non-empty `S`, the zone condition `|expr| ≤ t/2 < 0` is unsatisfiable, so
`satisfiesFlatness S t` etc. are `False`. For empty `S` they are vacuously `True`.
The standard implicitly assumes `t ≥ 0`; we do not add this as a hypothesis because
the monotone theorems hold for all `t` and the definitions are otherwise consistent.
-/

import GDT.Basic
import GDT.Geometry.Line
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

/-! ## Flatness, Y14.5.1 §5.4.2 -/

/-- A set `S` satisfies a flatness tolerance `t` if it lies between
    two parallel planes separated by `t`. Per Y14.5.1 §5.4.2.1.

    The zone is { P⃗ | |n̂ · (P⃗ - A⃗)| ≤ t/2 } where n̂ is the unit normal. -/
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

/-- If every point of `S` has signed distance at most `δ` from some plane,
    then `S` satisfies flatness tolerance `2δ`. -/
theorem bounded_deviation_flatness {S : Set Point3} {δ : ℝ} {n : Vec3} {c : ℝ}
    (hn : ‖n‖ = 1) (hbound : ∀ p ∈ S, |@inner ℝ _ _ n p - c| ≤ δ) :
    satisfiesFlatness S (2 * δ) :=
  ⟨n, c, hn, fun p hp => by linarith [hbound p hp]⟩

/-- A perfect plane satisfies flatness 0. -/
theorem plane_satisfies_flatness_zero (n : Vec3) (c : ℝ) (hn : ‖n‖ = 1) :
    satisfiesFlatness {p : Point3 | @inner ℝ _ _ n p = c} 0 :=
  ⟨n, c, hn, fun p hp => by simp [Set.mem_ofPred_eq.mp hp]⟩

/-! ## Straightness, Y14.5.1 §5.4.1 -/

/-- A set `S` satisfies a straightness tolerance `t` if it lies within
    a cylinder of diameter `t` around some line. Per Y14.5.1 §5.4.1.1.

    **Note on generality**: §5.4.1.1 applies this zone to the *derived median line*
    of a cylindrical feature, a specific geometric construction from the feature's
    surface points, which we do not formalize. §5.4.1.3 (straightness of surface line
    elements) applies a related zone under additional cutting-plane constraints, also
    not formalized. Our definition is stated for an arbitrary point set `S` and is
    therefore more general than either application: a caller supplies whichever point
    set the standard's construction yields. The containment theorems below hold for
    any such `S`. -/
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

/-! ## Circularity, Y14.5.1 §5.4.3

NOTE: Y14.5.1 allows curved spines; we restrict to a single cross-section. -/

/-- A set `S` satisfies a circularity tolerance `t` if it lies in a
    coplanar annular region of width `t`. Per Y14.5.1 §5.4.3.

    The zone requires both coplanarity (hat(T) . (P - A) = 0) and the
    annular bound (| ||P - A|| - r | <= t/2).

    **Why coplanarity is required**: without it, the definition would be vacuous for
    any finite `S`. Given points at distinct distances from a candidate in-plane center,
    one can move the center off the plane of `S` along the normal until all 3-D
    distances to it are equal, satisfying the annular bound with `t = 0`. Every finite
    set lying on a sphere would then "satisfy circularity 0". The constraint
    `inner n (p - center) = 0` pins the center into the plane of the circular element,
    which is what §5.4.3 intends. -/
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

/-! ## Cylindricity, Y14.5.1 §5.4.4 -/

/-- A set `S` satisfies a cylindricity tolerance `t` if it lies between
    two coaxial cylinders of radii `r ± t/2`. Per Y14.5.1 §5.4.4.

    The standard states the zone is `| |hat(T) x (P - A)| - r | <= t/2` with
    `r` described only as "the radial distance from the cylindricity axis to the
    center of the zone" and no lower bound specified. We add `0 ≤ r` to exclude
    the degenerate case where the inner cylinder would have negative radius, which
    the standard precludes geometrically but not algebraically. For circularity
    (§5.4.3), the standard itself requires `r > 0 for all circular elements`; we
    apply the same convention here for consistency. -/
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

/-! ## cylindricity ⟹ circularity

The key insight: for a point `p` in a cutting plane perpendicular to the axis `L`
at a point `a` on `L`, we have `distToLine p L = dist a p`. This is because the
orthogonal projection of `(p - L.point)` onto `L.dir` places us at `a`, so the
residual is exactly `p - a`, and its norm is `dist a p`.

We state this in a form that avoids needing the cutting-plane machinery:
given a cylindricity witness (L, r), any point with `distToLine p L` bounded
has `dist (closest point on axis) p` bounded by the same amount. -/

/-- **Cylindricity implies circularity** (simplified form):
    if `S` satisfies cylindricity `t` with witness axis `L` and radius `r`,
    then for any coplanar subset of `S` where `distToLine` equals `dist a p`
    for some fixed `a`, that subset satisfies circularity `t`.

    The caller must supply the cutting-plane normal `n` and prove that all
    points of `S` are coplanar with the center `a`.

    **Note on `hr : 0 < r`**: `satisfiesCylindricity` only provides `0 ≤ r`, not
    `0 < r`. The caller must separately establish strict positivity before applying
    this theorem. The degenerate case `r = 0` (a solid cylinder of radius `t/2`)
    does not yield a valid `satisfiesCircularity` witness because that definition
    requires `0 < r`. A caller deriving this from a cylindricity witness should
    rule out `r = 0` by showing `S` is non-empty or that the feature has positive
    radius by construction. -/
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
