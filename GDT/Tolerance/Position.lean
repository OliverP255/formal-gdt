/-
# Position Tolerance, ASME Y14.5.1 §7.2

Position tolerance zone: the resolved geometry (axis) of the
feature must lie within a cylindrical zone of specified diameter,
centered on the true position axis.
-/

import GDT.Geometry.Line

noncomputable section

/-- position tolerance (t), "In Terms of the Resolved Geometry of a Feature" (§7.2.2):
    the resolved axis of the feature must lie within r(vec(P)) <= t/2 of truePos.

    Formalizes the cylindrical, RFS case (Table 7-3 gives b = t_0/2 here).

    Not formalized: spherical or parallel-plane tolerance zones, or the MMC/LMC cases, where b
    depends on the mating envelope radius. -/

def satisfiesPosition (S : Set Point3) (t : ℝ) (truePos : Line3) : Prop :=
  ∀ p ∈ S, distToLine p truePos ≤ t / 2

theorem position_monotone {S : Set Point3} {t t' : ℝ} {L : Line3}
    (h : satisfiesPosition S t L) (hle : t ≤ t') : satisfiesPosition S t' L :=
  fun p hp => le_trans (h p hp) (by linarith)

theorem position_subset {S S' : Set Point3} {t : ℝ} {L : Line3}
    (h : satisfiesPosition S t L) (hsub : S' ⊆ S) : satisfiesPosition S' t L :=
  fun p hp => h p (hsub hp)

end
