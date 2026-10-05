-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.PolynomialBallDensity

/-!
# Actual mean-zero polynomial density and divergence range

The ball integral is a genuine bounded Hilbert functional. Removing the actual
ball mean projects onto its closed kernel. Polynomial density is preserved by
this projection, and compact test integration proves that every completed
zero-boundary divergence belongs to the same kernel.
-/

@[expose] public section

open CKN MvPolynomial MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The genuine constant-one class on the actual ball. -/
def unitBallOneL2 : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)) :=
  unitBallPolynomialL2 (C 1)

theorem unitBallOneL2_ae : unitBallOneL2 =ᵐ[volume.restrict (vec3Ball 0 1)] fun _ ↦ 1 := by
  have h := (unitBallPolynomial_memLp (C 1)).coeFn_toLp
  filter_upwards [h] with x hx
  change unitBallOneL2 x = ballPolynomialEval (C 1) x at hx
  rw [hx]
  simp [ballPolynomialEval]

/-- The literal ball integral, represented as a bounded Hilbert functional. -/
def unitBallL2Integral : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)) →L[ℝ] ℝ :=
  innerSL ℝ unitBallOneL2

theorem unitBallL2Integral_apply (f : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) :
    unitBallL2Integral f = ∫ x in vec3Ball 0 1, f x := by
  change inner ℝ unitBallOneL2 f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [unitBallOneL2_ae] with x hx
  simp [hx, RCLike.inner_apply]

theorem unitBallL2Integral_polynomial (p : BallPolynomial) :
    unitBallL2Integral (unitBallPolynomialL2 p) =
      ∫ x in vec3Ball 0 1, ballPolynomialEval p x := by
  rw [unitBallL2Integral_apply]
  exact integral_congr_ae (unitBallPolynomial_memLp p).coeFn_toLp

theorem unitBallL2Integral_one :
    unitBallL2Integral unitBallOneL2 = (volume (vec3Ball 0 1)).toReal := by
  rw [unitBallL2Integral_apply]
  calc
    _ = ∫ _x in vec3Ball 0 1, (1 : ℝ) := integral_congr_ae unitBallOneL2_ae
    _ = _ := by simp [Measure.real]

theorem unitBallVolume_toReal_pos : 0 < (volume (vec3Ball (0 : Vec3) 1)).toReal :=
  ENNReal.toReal_pos (volume_vec3Ball_pos (by norm_num)).ne' volume_vec3Ball_lt_top.ne

/-- The actual closed Hilbert space of functions with zero ball integral. -/
def unitBallMeanZeroL2 : ClosedSubmodule ℝ (Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) where
  toSubmodule := unitBallL2Integral.ker
  isClosed' := unitBallL2Integral.isClosed_ker

theorem unitBallMeanZeroL2_mem_iff (f : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) :
    f ∈ unitBallMeanZeroL2 ↔ (∫ x in vec3Ball 0 1, f x) = 0 := by
  change unitBallL2Integral f = 0 ↔ _
  rw [unitBallL2Integral_apply]

/-- Subtract the actual spatial mean in the ambient Hilbert space. -/
def unitBallRemoveMean : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)) →L[ℝ]
    Lp ℝ 2 (volume.restrict (vec3Ball 0 1)) :=
  ContinuousLinearMap.id ℝ _ -
    (volume (vec3Ball 0 1)).toReal⁻¹ • unitBallL2Integral.smulRight unitBallOneL2

theorem unitBallRemoveMean_apply (f : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) :
    unitBallRemoveMean f = f -
      ((volume (vec3Ball 0 1)).toReal⁻¹ * unitBallL2Integral f) • unitBallOneL2 := by
  simp [unitBallRemoveMean, smul_smul]

theorem unitBallRemoveMean_mem (f : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) :
    unitBallRemoveMean f ∈ unitBallMeanZeroL2 := by
  change unitBallL2Integral (unitBallRemoveMean f) = 0
  rw [unitBallRemoveMean_apply, map_sub, map_smul, unitBallL2Integral_one]
  simp only [smul_eq_mul]
  field_simp [unitBallVolume_toReal_pos.ne']
  ring

/-- Actual continuous mean removal with its codomain restricted to the actual closed kernel. -/
def unitBallMeanZeroProjection : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)) →L[ℝ]
    unitBallMeanZeroL2 :=
  unitBallRemoveMean.codRestrict unitBallMeanZeroL2.toSubmodule unitBallRemoveMean_mem

theorem unitBallMeanZeroProjection_surjective : Function.Surjective unitBallMeanZeroProjection := by
  intro f
  refine ⟨f.1, Subtype.ext ?_⟩
  change unitBallRemoveMean f.1 = f.1
  have hf : unitBallL2Integral f.1 = 0 := f.property
  simp [unitBallRemoveMean_apply, hf]

/-- Genuine mean-zero polynomial restrictions in the actual mean-zero Hilbert space. -/
def meanZeroUnitBallPolynomialL2 : BallPolynomial →ₗ[ℝ] unitBallMeanZeroL2 :=
  unitBallMeanZeroProjection.toLinearMap.comp unitBallPolynomialL2Linear

/-- The projected restriction is still an actual polynomial, with its literal ball mean removed. -/
theorem meanZeroUnitBallPolynomialL2_coe (p : BallPolynomial) :
    (meanZeroUnitBallPolynomialL2 p : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) =
      unitBallPolynomialL2 (p - C (unitBallPolynomialMean p)) := by
  change unitBallRemoveMean (unitBallPolynomialL2 p) = _
  rw [unitBallRemoveMean_apply, unitBallL2Integral_polynomial]
  change unitBallPolynomialL2 p - unitBallPolynomialMean p • unitBallOneL2 = _
  apply Lp.ext
  filter_upwards [(unitBallPolynomial_memLp p).coeFn_toLp,
    (unitBallPolynomial_memLp (p - C (unitBallPolynomialMean p))).coeFn_toLp,
    Lp.coeFn_sub (unitBallPolynomialL2 p) (unitBallPolynomialMean p • unitBallOneL2),
    Lp.coeFn_smul (unitBallPolynomialMean p) unitBallOneL2, unitBallOneL2_ae]
    with x hp hzero hsub hsmul hone
  change unitBallPolynomialL2 p x = _ at hp
  change unitBallPolynomialL2 (p - C (unitBallPolynomialMean p)) x = _ at hzero
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsmul, hzero]
  simp [Pi.smul_apply, hp, hone, ballPolynomialEval]

theorem meanZeroUnitBallPolynomial_integral (p : BallPolynomial) :
    (∫ x in vec3Ball 0 1,
      ballPolynomialEval (p - C (unitBallPolynomialMean p)) x) = 0 := by
  have hp : unitBallL2Integral (meanZeroUnitBallPolynomialL2 p) = 0 :=
    (meanZeroUnitBallPolynomialL2 p).property
  rw [meanZeroUnitBallPolynomialL2_coe, unitBallL2Integral_polynomial] at hp
  exact hp

/-- Actual mean-zero polynomials are dense in all actual mean-zero square-integrable functions. -/
theorem meanZeroUnitBallPolynomialL2_denseRange : DenseRange meanZeroUnitBallPolynomialL2 :=
  unitBallMeanZeroProjection_surjective.denseRange.comp unitBallPolynomialL2_denseRange
    unitBallMeanZeroProjection.continuous

/-- The genuine divergence on the completed zero-boundary energy space has zero integral. -/
theorem stokesEnergyDivergence_unitBall_meanZero
    (v : stokesGradientEnergySpace (vec3Ball 0 1)) :
    stokesEnergyDivergence (vec3Ball 0 1) v ∈ unitBallMeanZeroL2 := by
  let F : StokesGradientL2 (vec3Ball 0 1) →L[ℝ] ℝ :=
    unitBallL2Integral.comp (stokesMatrixTrace.compLpL 2 (volume.restrict (vec3Ball 0 1)))
  have htest : ∀ φ : StokesVectorTest (vec3Ball 0 1), F (stokesTestGradientL2 φ) = 0 := by
    intro φ
    change unitBallL2Integral (stokesEnergyDivergence (vec3Ball 0 1) (stokesEnergyTest φ)) = 0
    rw [unitBallL2Integral_apply]
    rw [integral_congr_ae (stokesEnergyDivergence_test_ae φ), integral_finsetSum]
    · exact Finset.sum_eq_zero fun i _ ↦ weakTest_partialDeriv_integral_eq_zero (φ i) i
    · intro i _
      exact continuous_integrableOn_unitBall
        (((φ i).contDiff.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hspan : Submodule.span ℝ (range (stokesTestGradientL2 (U := vec3Ball 0 1))) ≤ F.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨φ, rfl⟩
    exact htest φ
  have hclosure := Submodule.topologicalClosure_minimal _ hspan F.isClosed_ker
  exact hclosure v.property

/-- The genuine divergence, restricted to its mathematically correct mean-zero target. -/
def unitBallMeanZeroDivergence : stokesGradientEnergySpace (vec3Ball 0 1) →L[ℝ]
    unitBallMeanZeroL2 :=
  (stokesEnergyDivergence (vec3Ball 0 1)).codRestrict unitBallMeanZeroL2.toSubmodule
    stokesEnergyDivergence_unitBall_meanZero

end FluidSingularSets
