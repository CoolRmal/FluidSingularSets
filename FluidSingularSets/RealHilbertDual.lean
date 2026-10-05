-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Real continuous linear Hilbert duality operators -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Real Riesz representation is a genuine continuous linear operator. -/
def realHilbertRieszInverse : (E →L[ℝ] ℝ) →L[ℝ] E where
  toFun := (InnerProductSpace.toDual ℝ E).symm
  map_add' := (InnerProductSpace.toDual ℝ E).symm.map_add
  map_smul' c F := by
    simpa only [RingHom.id_apply, starRingEnd_apply, star_trivial] using
      (InnerProductSpace.toDual ℝ E).symm.map_smulₛₗ c F
  cont := (InnerProductSpace.toDual ℝ E).symm.continuous

@[simp]
theorem realHilbertRieszInverse_apply (F : E →L[ℝ] ℝ) :
    realHilbertRieszInverse E F = (InnerProductSpace.toDual ℝ E).symm F := rfl

/-- The actual real Hilbert pairing is a continuous linear operator into the dual. -/
def realHilbertRiesz : E →L[ℝ] (E →L[ℝ] ℝ) where
  toFun := InnerProductSpace.toDual ℝ E
  map_add' := (InnerProductSpace.toDual ℝ E).map_add
  map_smul' c x := by
    simpa only [RingHom.id_apply, starRingEnd_apply, star_trivial] using
      (InnerProductSpace.toDual ℝ E).map_smulₛₗ c x
  cont := (InnerProductSpace.toDual ℝ E).continuous

@[simp]
theorem realHilbertRiesz_apply (x y : E) :
    realHilbertRiesz E x y = inner ℝ x y := rfl

variable {E} {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]

omit [CompleteSpace E] in
/-- Genuine restriction of continuous real functionals along a fixed linear map. -/
def realDualPrecompose (i : K →L[ℝ] E) : (E →L[ℝ] ℝ) →L[ℝ] (K →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ K E ℝ).flip i

omit [CompleteSpace E] in
@[simp]
theorem realDualPrecompose_apply (i : K →L[ℝ] E) (F : E →L[ℝ] ℝ) :
    realDualPrecompose i F = F.comp i := rfl

end FluidSingularSets
