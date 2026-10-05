-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StokesEnergyVelocity

/-!
# Genuine vector sources for the zero-boundary Stokes problem

The actual reconstructed energy velocity turns square-integrable vector data
into a bounded variational force. Scalar coordinate pairings avoid imposing a
Hilbert norm on CKN's sup-norm `Vec3`. The force agrees with the literal vector
source integral on every genuine compact smooth test.
-/

@[expose] public section

open CKN MeasureTheory Set
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A velocity coordinate projection is a contraction in genuine `L²`. -/
theorem stokesVelocityComponent_opNorm_le (U : Set Vec3) (i : Fin 3) :
    ‖stokesVelocityComponent U i‖ ≤ 1 := by
  have hproj : ‖(ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)‖ ≤ 1 := by
    refine (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).opNorm_le_bound (by norm_num) ?_
    intro x
    simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm x i
  exact (ContinuousLinearMap.norm_compLpL_le
    (p := 2) (μ := volume.restrict U) (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)).trans
      hproj

/-- A velocity coordinate is bounded by the true vector `L²` norm. -/
theorem stokesVelocityComponent_norm_le {U : Set Vec3} (i : Fin 3)
    (u : Lp Vec3 2 (volume.restrict U)) : ‖stokesVelocityComponent U i u‖ ≤ ‖u‖ :=
  ((stokesVelocityComponent U i).le_opNorm u).trans
    (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (stokesVelocityComponent_opNorm_le U i) (norm_nonneg u))

/-- The actual coordinate of a genuine vector test is its scalar test class. -/
theorem stokesVelocityComponent_stokesTestVelocityL2 {U : Set Vec3}
    (φ : StokesVectorTest U) (i : Fin 3) :
    stokesVelocityComponent U i (stokesTestVelocityL2 φ) = stokesScalarTestL2 (φ i) := by
  apply Lp.ext
  have hc := (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).coeFn_compLpL
    (p := 2) (μ := volume.restrict U) (stokesTestVelocityL2 φ)
  have hv := (stokesTestVelocity_memLp φ).coeFn_toLp
  have hs := ((((φ i).contDiff.continuous.memLp_of_hasCompactSupport
    (φ i).hasCompactSupport).mono_measure Measure.restrict_le_self :
      MemLp (φ i).toFun 2 (volume.restrict U))).coeFn_toLp
  filter_upwards [hc, hv, hs] with x hcx hvx hsx
  change stokesVelocityComponent U i (stokesTestVelocityL2 φ) x =
    stokesTestVelocityL2 φ x i at hcx
  change stokesTestVelocityL2 φ x = stokesTestVelocity φ x at hvx
  change stokesScalarTestL2 (φ i) x = φ i x at hsx
  rw [hcx, hvx, hsx]
  rfl

/-- The true Stokes force of actual square-integrable vector data. -/
def stokesVectorForce (U : Set Vec3) (u : Lp Vec3 2 (volume.restrict U)) :
    StokesEnergyForce U :=
  ∑ i : Fin 3, ((innerSL ℝ (stokesVelocityComponent U i u)).comp
    (stokesVelocityComponent U i)).comp (stokesEnergyVelocity U)

/-- The actual force is the sum of its scalar coordinate pairings. -/
theorem stokesVectorForce_apply {U : Set Vec3} (u : Lp Vec3 2 (volume.restrict U))
    (v : stokesGradientEnergySpace U) :
    stokesVectorForce U u v = ∑ i : Fin 3, inner ℝ (stokesVelocityComponent U i u)
      (stokesVelocityComponent U i (stokesEnergyVelocity U v)) := by
  simp only [stokesVectorForce, sum_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply]

/-- Each genuine coordinate source-test product is actually integrable. -/
theorem stokesVectorForce_testProduct_integrable {U : Set Vec3}
    (u : Lp Vec3 2 (volume.restrict U)) (φ : StokesVectorTest U) (i : Fin 3) :
    Integrable (fun x ↦ u x i * φ i x) (volume.restrict U) := by
  have hu : MemLp (fun x ↦ u x i) 2 (volume.restrict U) :=
    (Lp.memLp u).continuousLinearMap_comp (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hφ : MemLp (φ i).toFun 2 (volume.restrict U) :=
    ((φ i).contDiff.continuous.memLp_of_hasCompactSupport
      (φ i).hasCompactSupport).mono_measure Measure.restrict_le_self
  exact hu.integrable_mul hφ

/-- The actual constructed force satisfies the literal source equation on genuine tests. -/
theorem stokesVectorForce_test {U : Set Vec3}
    (hU : MeasurableSet U) (hvol : volume U ≠ ∞)
    (u : Lp Vec3 2 (volume.restrict U)) (φ : StokesVectorTest U) :
    stokesVectorForce U u (stokesEnergyTest φ) =
      ∫ x in U, ∑ i : Fin 3, u x i * φ i x := by
  rw [stokesVectorForce_apply, stokesEnergyVelocity_test hU hvol]
  simp_rw [stokesVelocityComponent_stokesTestVelocityL2,
    real_inner_comm (stokesScalarTestL2 _), stokesVelocityComponent_pair]
  exact (integral_finsetSum Finset.univ
    (fun i _ ↦ stokesVectorForce_testProduct_integrable u φ i)).symm

/-- The genuine vector-source functional has the finite quantitative Stokes bound. -/
theorem stokesVectorForce_norm_le {U : Set Vec3}
    (hU : MeasurableSet U) (hvol : volume U ≠ ∞)
    (u : Lp Vec3 2 (volume.restrict U)) :
    ‖stokesVectorForce U u‖ ≤ 3 * (stokesTestPoincareConstant U).toReal * ‖u‖ := by
  refine (stokesVectorForce U u).opNorm_le_bound (by positivity) ?_
  intro v
  rw [stokesVectorForce_apply]
  calc
    ‖∑ i : Fin 3, inner ℝ (stokesVelocityComponent U i u)
        (stokesVelocityComponent U i (stokesEnergyVelocity U v))‖
      ≤ ∑ i : Fin 3, ‖inner ℝ (stokesVelocityComponent U i u)
          (stokesVelocityComponent U i (stokesEnergyVelocity U v))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖u‖ * ((stokesTestPoincareConstant U).toReal * ‖v‖) := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_inner_le_norm _ _).trans (mul_le_mul
        (stokesVelocityComponent_norm_le i u)
        ((stokesVelocityComponent_norm_le i _).trans
          (stokesEnergyVelocity_norm_le hU hvol v))
        (norm_nonneg _) (norm_nonneg _))
    _ = (3 * (stokesTestPoincareConstant U).toReal * ‖u‖) * ‖v‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end FluidSingularSets
