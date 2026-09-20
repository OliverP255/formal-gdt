/-
# Position Tolerance, ASME Y14.5.1 §7.2

Position tolerance zone: the resolved geometry (axis) of the
feature must lie within a cylindrical zone of specified diameter,
centered on the true position axis.
-/

import GDT.Geometry.Line

noncomputable section

/-- Position tolerance, "In Terms of the Resolved Geometry of a Feature"
    (§7.2.2, Y14.5.1-definitions.md#position-resolved).

    §7.2.2(a) Definition, on what the zone constrains:

    > For a pattern of features of size, a position tolerance specifies that
    > the resolved geometry (center point, axis, or center plane, as
    > applicable) of each unrelated actual mating envelope (for features at
    > MMC or RFS) or unrelated actual minimum material envelope (for
    > features at LMC) must lie within a corresponding position tolerance
    > zone.

    and on the zone itself:

    > A position tolerance zone is a spherical, cylindrical, or
    > parallel-plane volume defined by all points vec(P) that satisfy the
    > equation r(vec(P)) <= b, where b is the radius or half-width of the
    > tolerance zone.

    This definition formalizes one instance of that family: the
    **cylindrical** zone, taking r(vec(P)) = distToLine p truePos with
    truePos the true-position axis, at **RFS**, for which Table 7-3 gives
    b = t_0/2 in both rows:

    > **Table 7-3 Size of Position Tolerance Zone -- Resolved Geometry
    > Interpretation**
    >
    > | | | MMC | RFS | LMC |
    > |---|---|---|---|---|
    > | Feature Type | Internal | t_0/2 + (r_AM - r_MMC) | t_0/2 | t_0/2 + (r_LMC - r_AMM) |
    > | Feature Type | External | t_0/2 + (r_MMC - r_AM) | t_0/2 | t_0/2 + (r_AMM - r_LMC) |

    Not formalized: the spherical and parallel-plane zones, and the MMC and
    LMC columns of Table 7-3, where b additionally depends on r_AM, r_MMC,
    r_LMC, and r_AMM. -/
def satisfiesPosition (S : Set Point3) (t : ℝ) (truePos : Line3) : Prop :=
  ∀ p ∈ S, distToLine p truePos ≤ t / 2

theorem position_monotone {S : Set Point3} {t t' : ℝ} {L : Line3}
    (h : satisfiesPosition S t L) (hle : t ≤ t') : satisfiesPosition S t' L :=
  fun p hp => le_trans (h p hp) (by linarith)

theorem position_subset {S S' : Set Point3} {t : ℝ} {L : Line3}
    (h : satisfiesPosition S t L) (hsub : S' ⊆ S) : satisfiesPosition S' t L :=
  fun p hp => h p (hsub hp)

end
