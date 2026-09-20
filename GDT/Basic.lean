/-
# Basic types for GD&T formalization

We work in ℝ³ via Mathlib's EuclideanSpace ℝ (Fin 3), which provides
an inner product space structure with inner, norm, and dist.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open scoped InnerProductSpace

abbrev Point3 := EuclideanSpace ℝ (Fin 3)

abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

end
