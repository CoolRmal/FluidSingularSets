module

public import FluidSingularSets.Geometry

/-! # Covering growth and upper parabolic box dimension -/

@[expose] public section

open Set
open scoped ENNReal NNReal

noncomputable section

namespace FluidSingularSets

/-- A uniform polynomial bound on the covering number gives the corresponding box bound. -/
theorem upperParabolicBoxDimension_le_of_covering_bound
    {E : Set SpaceTime} {s C r₀ : ℝ} (hs : 0 ≤ s) (hC : 0 < C) (hr₀ : 0 < r₀)
    (hcover : ∀ r : ℝ, 0 < r → r < r₀ →
      (parabolicCoveringNumber E r.toNNReal).toENNReal ≤ ENNReal.ofReal (C * r ^ (-s))) :
    upperParabolicBoxDimension E ≤ ENNReal.ofReal s :=
  iInf_le_of_le s (iInf_le_of_le hs (iInf_le_of_le ⟨C, hC, r₀, hr₀, hcover⟩ le_rfl))

/-- Upper parabolic box dimension is monotone under inclusion. -/
theorem upperParabolicBoxDimension_mono {E F : Set SpaceTime} (hEF : E ⊆ F) :
    upperParabolicBoxDimension E ≤ upperParabolicBoxDimension F := by
  refine le_iInf fun s ↦ le_iInf fun hs ↦ le_iInf fun hgrowth ↦ ?_
  obtain ⟨C, hC, r₀, hr₀, hcover⟩ := hgrowth
  apply upperParabolicBoxDimension_le_of_covering_bound hs hC hr₀
  intro r hr hrsmall
  exact (ENat.toENNReal_mono
    (Metric.externalCoveringNumber_mono_set (image_mono hEF))).trans
      (hcover r hr hrsmall)

@[simp]
theorem upperParabolicBoxDimension_empty : upperParabolicBoxDimension ∅ = 0 := by
  apply le_antisymm _ zero_le
  have h := upperParabolicBoxDimension_le_of_covering_bound
    (E := (∅ : Set SpaceTime)) (s := 0) (C := 1) (r₀ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by
      intro r hr hrsmall
      simp [parabolicCoveringNumber])
  simpa using h

end FluidSingularSets
