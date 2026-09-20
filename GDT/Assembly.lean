/-
# Assembly Model and Fastener Theorems

Formalizes three cases from ASME-Y14.5-2019-Appendix-B.pdf:
  B.3 Floating fastener:        T = H - F    (sufficiency + tightness)
  B.4 Fixed fastener:           T = (H-F)/2  (sufficiency + tightness)
  B.5 Fixed fastener with tilt: the B.4 formula fails (counterexample + corrected
                                sufficiency)
            
Throughout, H and F denote diameters, so r_H = H/2
and r_F = F/2 are the corresponding radii.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section

/-- a fastener of radius r_F at position q clears a hole of radius r_H centered at c
    when it stays inside the hole -/
def holeClearsAt {E : Type*} [PseudoMetricSpace E]
    (c : E) (r_H : ℝ) (q : E) (r_F : ℝ) : Prop :=
  dist c q + r_F ≤ r_H

/-! ## Floating fastener: T = H − F

Appendix B §B.3: "Where the fasteners are of the same diameter, and it is desired
to use the same clearance hole diameters and the same positional tolerances for the
parts to be assembled, the following formula applies: H = F + T or T = H - F."

In radii: T ≤ 2·(r_H − r_F). -/

/-- floating fastener sufficiency -/
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

/-- If T > H − F, some pair of hole centers within T/2 admits no clearing fastener position. -/
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

/-! ## Fixed fastener: T = (H−F)/2

Appendix B §B.4: "Where the fasteners are of the same diameter and it is desired
to use the same positional tolerance in each of the parts to be assembled, the
following formula applies: H = F + 2T or T = (H - F) / 2." Half the floating case's
tolerance, since fastener and hole are now independently toleranced.

In radii: T ≤ r_H − r_F. -/

/-- If T ≤ (H−F)/2, a fastener center and hole center each within T/2 of true position clear. -/
theorem fixed_fastener_sufficient
    {E : Type*} [SeminormedAddCommGroup E]
    {r_H r_F T : ℝ} (hT : T ≤ r_H - r_F)
    (c_f c_h : E) (hf : ‖c_f‖ ≤ T / 2) (hh : ‖c_h‖ ≤ T / 2) :
    holeClearsAt c_h r_H c_f r_F := by
  show dist c_h c_f + r_F ≤ r_H
  have : dist c_h c_f ≤ ‖c_h‖ + ‖c_f‖ := by
    rw [dist_eq_norm]; exact norm_sub_le c_h c_f
  linarith

/-- fixed fastener tightness: T = (H−F)/2 holds only without tilt or with a projected tolerance zone -/
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

/-! ## Fixed fastener with tilt (§B.5)

§B.5 corrects §B.4 for when there is tilt. a fastener tilted by α has effective radius
r_F / cos α, so with k = 1 / cos α ≥ 1, clearance becomes dist c q + k * r_F ≤ r_H
(k = 1 recovers holeClearsAt). -/

/-- clearance for a fastener tilted by angle α, with secant factor k = 1 / cos α. -/
def holeClearsTilted {E : Type*} [PseudoMetricSpace E]
    (c : E) (r_H : ℝ) (q : E) (r_F : ℝ) (k : ℝ) : Prop :=
  dist c q + k * r_F ≤ r_H

/-- with no tilt (k = 1), holeClearsTilted is exactly holeClearsAt. -/
theorem holeClearsTilted_one {E : Type*} [PseudoMetricSpace E]
    (c : E) (r_H : ℝ) (q : E) (r_F : ℝ) :
    holeClearsTilted c r_H q r_F 1 ↔ holeClearsAt c r_H q r_F := by
  simp [holeClearsTilted, holeClearsAt]

/-- the secant factor k = 1 / cos α exceeds 1 for any nonzero tilt α ∈ (0, π/2). -/
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

/-- §B.4's bound isn't safe under tilt: right at its boundary T = H − F, even a
    little tilt can make an otherwise-conforming fastener and hole miss each other. -/
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

/-- §B.5's fix: tighten the tolerance to T ≤ r_H − k·r_F and clearance holds again,
    even with tilt factor k. Setting k = 1 (no tilt) gives back fixed_fastener_sufficient. -/
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
