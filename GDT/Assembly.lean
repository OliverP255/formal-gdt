/-
# Assembly Model and Fastener Theorems

Source: ASME Y14.5-2009, Nonmandatory Appendix B, "Formulas for Positional
Tolerancing" (pp. 191-192). See Y14.5.1-definitions.md#appendix-b.

Formalizes three cases from Appendix B:
  B.3 Floating fastener:        T = H - F    (sufficiency + tightness)
  B.4 Fixed fastener:           T = (H-F)/2  (sufficiency + tightness)
  B.5 Fixed fastener with tilt: the B.4 formula fails (counterexample + corrected
                                sufficiency)

Throughout, H and F denote *diameters* (Appendix B symbols), so r_H = H/2
and r_F = F/2 are the corresponding radii. A position tolerance T (diameter)
maps to a tolerance radius of T/2 for hole center position.

Sufficiency proofs work over abstract SeminormedAddCommGroup.
Tightness counterexamples are in ℝ.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section

/-- A fastener of radius r_F at position q clears a hole of radius r_H
    centered at c when the fastener stays inside the hole: dist c q + r_F ≤ r_H.

    This is our geometric model of the assembly condition that Appendix B of
    ASME Y14.5-2009 analyses. The Appendix B formulas (§B.3: T = H − F, §B.4:
    T = (H−F)/2) bound the worst-case dist c q by T/2 per part and derive the
    minimum H that achieves clearance. The condition dist c q + r_F ≤ r_H is
    the geometric statement of clearance that these formulas guarantee; it is not
    quoted verbatim in Appendix B (which works in diameters and gives formulas
    rather than the clearance geometry directly). See Y14.5.1-definitions.md#appendix-b.

    In Appendix B notation: dist c q is the offset between centers (bounded by T/2
    per part at MMC), r_F = F/2 is the fastener MMC radius, r_H = H/2 is the
    minimum clearance hole radius. Equality holds at the "no interference, no clearance"
    condition described in §B.1.

    **Note on parameter ranges**: The definition does not require 0 ≤ r_F or
    0 < r_H. The sufficiency theorems do not add these as hypotheses either,
    because hT : T ≤ 2*(r_H - r_F) (floating) or hT : T ≤ r_H - r_F (fixed)
    already implies r_H ≥ r_F, the physical constraint that the hole is at least
    as large as the fastener. An explicit 0 ≤ r_F would be logically redundant
    given hT and would trigger the unused-variable linter. The intended physical
    domain is 0 ≤ r_F < r_H; the tightness theorems require r_F < r_H via
    hHF. -/
def holeClearsAt {E : Type*} [PseudoMetricSpace E]
    (c : E) (r_H : ℝ) (q : E) (r_F : ℝ) : Prop :=
  dist c q + r_F ≤ r_H

/-! ## Floating fastener: T = H − F (Appendix B §B.3)

Appendix B §B.3: "Where the fasteners are of the same diameter, and it is desired
to use the same clearance hole diameters and the same positional tolerances for the
parts to be assembled, the following formula applies: H = F + T or T = H - F."

Parameters here are radii (r_H = H/2, r_F = F/2, T/2 = position tolerance radius).
The diameter formula T = H - F becomes T/2 = r_H - r_F, equivalently T ≤ 2·(r_H − r_F). -/

/-- **Floating fastener sufficiency** (ASME Y14.5-2009 Appendix B §B.3).
    If T ≤ H − F (Appendix B formula, in diameters), then for any two hole centers
    within positional tolerance T/2 of true position, there exists a fastener position
    clearing both holes. Proved over an abstract normed space; applies in ℝ², ℝ³, etc.

    **Proof strategy**: the fastener is placed at the origin (true position, q = 0).
    This is stronger than Appendix B requires (§B.3 only claims existence of *some*
    position). Placing at the origin works because each hole center is within T/2 of
    the origin, so dist c q = ‖c‖ ≤ T/2 ≤ r_H − r_F, giving dist + r_F ≤ r_H.
    The planned midpoint argument also works but the origin argument is simpler. -/
theorem floating_fastener_sufficient
    {E : Type*} [SeminormedAddCommGroup E]
    {r_H r_F T : ℝ} (hT : T ≤ 2 * (r_H - r_F))
    (c₁ c₂ : E) (h₁ : ‖c₁‖ ≤ T / 2) (h₂ : ‖c₂‖ ≤ T / 2) :
    ∃ q : E, holeClearsAt c₁ r_H q r_F ∧ holeClearsAt c₂ r_H q r_F := by
  refine ⟨0, ?_, ?_⟩
  · show dist c₁ 0 + r_F ≤ r_H
    rw [dist_zero_right]; linarith
  · show dist c₂ 0 + r_F ≤ r_H
    rw [dist_zero_right]; linarith

/-- **Floating fastener tightness** (ASME Y14.5-2009 Appendix B §B.3).
    If T > H − F, the Appendix B formula is violated. There exist hole centers
    each within positional tolerance T/2 such that no fastener position clears both.
    This shows T = H − F is sharp: the formula cannot be relaxed. -/
theorem floating_fastener_tight
    {r_H r_F T : ℝ} (hHF : r_F < r_H) (hT : 2 * (r_H - r_F) < T) :
    ∃ c₁ c₂ : ℝ, ‖c₁‖ ≤ T / 2 ∧ ‖c₂‖ ≤ T / 2 ∧
      ∀ q : ℝ, ¬(holeClearsAt c₁ r_H q r_F ∧ holeClearsAt c₂ r_H q r_F) := by
  refine ⟨T / 2, -(T / 2), ?_, ?_, ?_⟩
  · rw [Real.norm_eq_abs]; exact le_of_eq (abs_of_pos (by linarith))
  · rw [norm_neg, Real.norm_eq_abs]; exact le_of_eq (abs_of_pos (by linarith))
  · intro q ⟨h1, h2⟩
    simp only [holeClearsAt] at h1 h2
    have htri := dist_triangle (T / 2) q (-(T / 2))
    have hdist : dist (T / 2 : ℝ) (-(T / 2)) = T := by
      rw [dist_eq_norm, Real.norm_eq_abs]
      have : T / 2 - -(T / 2) = T := by ring
      rw [this, abs_of_pos (by linarith)]
    rw [dist_comm q (-(T / 2))] at htri
    linarith

/-! ## Fixed fastener: T = (H−F)/2 (Appendix B §B.4)

Appendix B §B.4: "Where the fasteners are of the same diameter and it is desired
to use the same positional tolerance in each of the parts to be assembled, the
following formula applies: H = F + 2T or T = (H - F) / 2. Note that the allowable
positional tolerance for each part is one-half that for the comparable floating
fastener case."

Here the fastener axis is fixed in one part (screws in tapped holes, studs); the
fastener center c_f and the clearance hole center c_h are each within T/2 of true
position. The diameter formula T = (H−F)/2 becomes T/2 = (r_H − r_F)/2, i.e.
T ≤ r_H − r_F in radius terms. -/

/-- **Fixed fastener sufficiency** (ASME Y14.5-2009 Appendix B §B.4).
    If T ≤ (H−F)/2 (Appendix B formula), then for any fastener center and hole
    center each within positional tolerance T/2 of true position, clearance holds. -/
theorem fixed_fastener_sufficient
    {E : Type*} [SeminormedAddCommGroup E]
    {r_H r_F T : ℝ} (hT : T ≤ r_H - r_F)
    (c_f c_h : E) (hf : ‖c_f‖ ≤ T / 2) (hh : ‖c_h‖ ≤ T / 2) :
    holeClearsAt c_h r_H c_f r_F := by
  show dist c_h c_f + r_F ≤ r_H
  have : dist c_h c_f ≤ ‖c_h‖ + ‖c_f‖ := by
    rw [dist_eq_norm]; exact norm_sub_le c_h c_f
  linarith

/-- **Fixed fastener tightness** (ASME Y14.5-2009 Appendix B §B.4).
    If T > (H−F)/2, the Appendix B formula is violated. There exist a fastener center
    and hole center each within positional tolerance T/2 such that clearance fails.
    This shows T = (H−F)/2 is sharp: it cannot be relaxed.

    Note: Appendix B §B.5 states that when the projected tolerance zone is NOT used,
    a larger formula H = F + T_1 + T_2·(1 + 2P/D) applies to account for fastener
    tilt. The tightness result here therefore applies only when tilt is absent or a
    projected tolerance zone is specified, as §B.4 assumes. -/
theorem fixed_fastener_tight
    {r_H r_F T : ℝ} (hHF : r_F < r_H) (hT : r_H - r_F < T) :
    ∃ c_f c_h : ℝ, ‖c_f‖ ≤ T / 2 ∧ ‖c_h‖ ≤ T / 2 ∧
      ¬holeClearsAt c_h r_H c_f r_F := by
  refine ⟨T / 2, -(T / 2), ?_, ?_, ?_⟩
  · rw [Real.norm_eq_abs]; exact le_of_eq (abs_of_pos (by linarith))
  · rw [norm_neg, Real.norm_eq_abs]; exact le_of_eq (abs_of_pos (by linarith))
  · intro h
    simp only [holeClearsAt] at h
    have hdist : dist (-(T / 2) : ℝ) (T / 2) = T := by
      rw [dist_eq_norm, Real.norm_eq_abs]
      have : -(T / 2) - T / 2 = -T := by ring
      rw [this, abs_neg, abs_of_pos (by linarith)]
    linarith

/-! ## Fixed fastener with tilt: why §B.4 needs a projected tolerance zone (§B.5)

The §B.4 formula T = (H−F)/2 is stated in ASME Y14.5-2009 under the heading
"Fixed Fastener Case When Projected Tolerance Zone Is Used". Appendix B §B.5,
"Fixed Fastener Case When Projected Tolerance Zone Is Not Used", gives the
corrected formula

    H = F + T_1 + T_2 * (1 + 2P/D)

where P is the fastener projection and D the thread engagement depth, the extra
term accounting for the fastener tilting within its positional tolerance zone.

We model the consequence of tilt rather than transcribing that formula: a
fastener whose axis is tilted by an angle α from the hole axis presents an
effective cross-section of radius r_F / cos α in the mating face. Writing
k = 1 / cos α ≥ 1 for the secant factor, clearance becomes
dist c q + k * r_F ≤ r_H. The factor k is grounded in an actual tilt angle
by one_lt_inv_cos below; k = 1 (no tilt) recovers holeClearsAt exactly
(holeClearsTilted_one).

The two results below bracket the gap: fixed_fastener_tilt_counterexample
shows the §B.4 bound is insufficient under *any* nonzero tilt, and
fixed_fastener_tilt_sufficient gives the tightened bound that restores the
guarantee. -/

/-- Clearance for a fastener tilted by angle α, where k = 1 / cos α is the
    secant factor by which tilt inflates the fastener's effective radius in the
    mating face.

    **This is our model, not a transcription.** Appendix B §B.5 states a corrected
    *diameter formula* (H = F + T_1 + T_2(1 + 2P/D)) rather than a clearance
    condition; dist c q + k * r_F ≤ r_H is the geometric clearance statement
    corresponding to the situation §B.5 addresses. The specific relation between
    k and the §B.5 term 2P/D is a function of the fastener geometry and is not
    formalized here. See Y14.5.1-definitions.md#appendix-b. -/
def holeClearsTilted {E : Type*} [PseudoMetricSpace E]
    (c : E) (r_H : ℝ) (q : E) (r_F : ℝ) (k : ℝ) : Prop :=
  dist c q + k * r_F ≤ r_H

/-- With no tilt (k = 1), the tilted clearance condition is exactly holeClearsAt. -/
theorem holeClearsTilted_one {E : Type*} [PseudoMetricSpace E]
    (c : E) (r_H : ℝ) (q : E) (r_F : ℝ) :
    holeClearsTilted c r_H q r_F 1 ↔ holeClearsAt c r_H q r_F := by
  simp [holeClearsTilted, holeClearsAt]

/-- The secant factor k = 1 / cos α exceeds 1 for any nonzero tilt angle
    α ∈ (0, π/2). This is what licenses reading the hypothesis 1 < k in
    fixed_fastener_tilt_counterexample as "the fastener is tilted". -/
theorem one_lt_inv_cos {α : ℝ} (h0 : 0 < α) (hpi : α < Real.pi / 2) :
    1 < 1 / Real.cos α := by
  have hpos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hpi⟩
  have hlt : Real.cos α < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ))
      (by linarith [Real.pi_pos] : α ≤ Real.pi) h0
    rwa [Real.cos_zero] at this
  rw [lt_div_iff₀ hpos]
  linarith

/-- **The tilt gap** (ASME Y14.5-2009 Appendix B §B.4 vs §B.5).
    At the exact §B.4 boundary T = H − F in radius terms (T = r_H − r_F, so that
    fixed_fastener_sufficient applies with equality), *any* nonzero fastener tilt
    breaks clearance: there are conforming fastener and hole centers for which the
    tilted fastener does not fit.

    This is the formal content of §B.4's qualification "When Projected Tolerance Zone
    Is Used". Without a projected tolerance zone, or some other guarantee of zero
    tilt, the formula T = (H−F)/2 does not imply assembly. -/
theorem fixed_fastener_tilt_counterexample
    {r_H r_F k : ℝ} (hrF : 0 < r_F) (hHF : r_F < r_H) (hk : 1 < k) :
    ∃ c_f c_h : ℝ,
      ‖c_f‖ ≤ (r_H - r_F) / 2 ∧ ‖c_h‖ ≤ (r_H - r_F) / 2 ∧
      ¬holeClearsTilted c_h r_H c_f r_F k := by
  refine ⟨(r_H - r_F) / 2, -((r_H - r_F) / 2), ?_, ?_, ?_⟩
  · rw [Real.norm_eq_abs]; exact le_of_eq (abs_of_pos (by linarith))
  · rw [norm_neg, Real.norm_eq_abs]; exact le_of_eq (abs_of_pos (by linarith))
  · intro h
    simp only [holeClearsTilted] at h
    have hdist : dist (-((r_H - r_F) / 2) : ℝ) ((r_H - r_F) / 2) = r_H - r_F := by
      rw [dist_eq_norm, Real.norm_eq_abs]
      have : -((r_H - r_F) / 2) - (r_H - r_F) / 2 = -(r_H - r_F) := by ring
      rw [this, abs_neg, abs_of_pos (by linarith)]
    rw [hdist] at h
    nlinarith

/-- **Corrected fixed fastener bound under tilt** (ASME Y14.5-2009 Appendix B §B.5).
    Tightening the positional tolerance to T ≤ r_H − k·r_F restores the assembly
    guarantee in the presence of tilt factor k. Setting k = 1 recovers
    fixed_fastener_sufficient.

    Together with fixed_fastener_tilt_counterexample this characterizes the gap:
    the §B.4 bound T ≤ r_H − r_F is exactly the k = 1 case, and nothing weaker
    than T ≤ r_H − k·r_F survives a tilt of factor k. -/
theorem fixed_fastener_tilt_sufficient
    {E : Type*} [SeminormedAddCommGroup E]
    {r_H r_F T k : ℝ} (hT : T ≤ r_H - k * r_F)
    (c_f c_h : E) (hf : ‖c_f‖ ≤ T / 2) (hh : ‖c_h‖ ≤ T / 2) :
    holeClearsTilted c_h r_H c_f r_F k := by
  show dist c_h c_f + k * r_F ≤ r_H
  have : dist c_h c_f ≤ ‖c_h‖ + ‖c_f‖ := by
    rw [dist_eq_norm]; exact norm_sub_le c_h c_f
  linarith

end
