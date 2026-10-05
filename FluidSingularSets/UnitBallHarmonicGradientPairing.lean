-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallHarmonicGradient

/-!
# Actual Hilbert pairing fields for the local harmonic pressure gradient

The genuine closed divergence-free Hilbert subspace admits its actual
orthogonal projection. Composing the proved local Stokes gradient with this
projection extends it to all square-integrable vector sources, while fixing
every divergence-free source. Riesz representation gives genuine spatial L²
fields for every point and coordinate evaluation.
-/

@[expose] public section

open CKN MeasureTheory Set
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual orthogonal extension of the genuine local harmonic Stokes gradient. -/
def unitBallHarmonicGradientExtended : UnitBallVectorL2 →L[ℝ]
    C(unitBallPressureCompactInterior, Vec3) :=
  unitBallHarmonicGradient.comp unitBallDivergenceFreeL2.toSubmodule.orthogonalProjectionOnto

/-- The orthogonal extension preserves every genuine divergence-free source. -/
theorem unitBallHarmonicGradientExtended_of_divergenceFree (u : unitBallDivergenceFreeL2) :
    unitBallHarmonicGradientExtended u.1 = unitBallHarmonicGradient u := by
  have hp := unitBallDivergenceFreeL2.toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨u.1, u.property⟩ : unitBallDivergenceFreeL2.toSubmodule)
  change unitBallDivergenceFreeL2.toSubmodule.orthogonalProjectionOnto u.1 = u at hp
  change unitBallHarmonicGradient
    (unitBallDivergenceFreeL2.toSubmodule.orthogonalProjectionOnto u.1) = _
  apply congrArg unitBallHarmonicGradient
  exact Subtype.ext (congrArg Subtype.val hp)

/-- The genuine extension retains the same universal source-norm bound. -/
theorem unitBallHarmonicGradientExtended_norm_le (u : UnitBallVectorL2) :
    ‖unitBallHarmonicGradientExtended u‖ ≤
      stokesVectorPressureGradientConstant * ‖u‖ := by
  exact (unitBallHarmonicGradientMap_norm_le
    (unitBallDivergenceFreeL2.toSubmodule.orthogonalProjectionOnto u)).trans
      (mul_le_mul_of_nonneg_left
        (unitBallDivergenceFreeL2.toSubmodule.norm_orthogonalProjectionOnto_apply_le u)
        stokesVectorPressureGradientConstant_nonneg)

/-- A true coordinate evaluation of the actual local harmonic pressure gradient. -/
def unitBallHarmonicGradientEvaluation (x : unitBallPressureCompactInterior) (i : Fin 3) :
    UnitBallVectorL2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).comp
    ((ContinuousMap.evalCLM ℝ x).comp unitBallHarmonicGradientExtended)

@[simp]
theorem unitBallHarmonicGradientEvaluation_apply (x : unitBallPressureCompactInterior)
    (i : Fin 3) (u : UnitBallVectorL2) :
    unitBallHarmonicGradientEvaluation x i u = unitBallHarmonicGradientExtended u x i := rfl

/-- The genuine Riesz field representing an interior pressure-gradient evaluation. -/
def unitBallHarmonicGradientPairingField (x : unitBallPressureCompactInterior) (i : Fin 3) :
    UnitBallVectorL2 :=
  realHilbertRieszInverse UnitBallVectorL2 (unitBallHarmonicGradientEvaluation x i)

/-- The true pointwise gradient coordinate is a pairing against the actual Hilbert field. -/
theorem unitBallHarmonicGradientExtended_pairing (x : unitBallPressureCompactInterior)
    (i : Fin 3) (u : UnitBallVectorL2) :
    unitBallHarmonicGradientExtended u x i =
      inner ℝ (unitBallHarmonicGradientPairingField x i) u := by
  exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := UnitBallVectorL2)
    (x := u) (y := unitBallHarmonicGradientEvaluation x i)).symm

/-- The actual pairing is the literal restricted spatial integral of Euclidean components. -/
theorem unitBallHarmonicGradientExtended_integral_pairing
    (x : unitBallPressureCompactInterior) (i : Fin 3) (u : UnitBallVectorL2) :
    unitBallHarmonicGradientExtended u x i =
      ∫ z in vec3Ball 0 1, ∑ j : Fin 3,
        unitBallHarmonicGradientPairingField x i z j * u z j := by
  rw [unitBallHarmonicGradientExtended_pairing, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The literal fixed-field integrand is genuinely integrable. -/
theorem unitBallHarmonicGradientPairingField_integrable
    (x : unitBallPressureCompactInterior) (i : Fin 3) (u : UnitBallVectorL2) :
    Integrable (fun z ↦ ∑ j : Fin 3,
      unitBallHarmonicGradientPairingField x i z j * u z j)
        (volume.restrict (vec3Ball 0 1)) := by
  have hi := L2.integrable_inner (𝕜 := ℝ) (unitBallHarmonicGradientPairingField x i) u
  apply hi.congr
  filter_upwards [] with z
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro j _
  ring

end FluidSingularSets
