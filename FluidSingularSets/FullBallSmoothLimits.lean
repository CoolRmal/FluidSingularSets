-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallHessianSmoothApprox
public import FluidSingularSets.StrongOperatorCurveLimits

/-!
# Genuine compact force-operator limits at arbitrary interior radii

The actual smoothed values, gradients and Hessians converge on every force.
Their genuine uniform bounds give uniform convergence on continuous compact
force trajectories, including uniformly approximated moving trajectories.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

local instance fullBallLimitForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance fullBallLimitForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The literal actual compact value operator at any genuine interior margin. -/
def fullBallCompactValueOperator (ρ σ : ℝ) (hρ : 0 < ρ) (hρσ : ρ < σ) (hσ : σ < 1) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] C(fullBallCompactInterior ρ, ℝ) :=
  fullBallHarmonicValuesExtended (fullBallCompactInterior ρ)
    (fullBallCompactInterior_subset_unit hρ (hρσ.trans hσ)) hσ
    (fullBallCompactInterior_subset hρ hρσ)

/-- The literal actual compact gradient operator at any genuine interior margin. -/
def fullBallCompactGradientOperator (ρ σ : ℝ) (hρ : 0 < ρ) (hρσ : ρ < σ) (hσ : σ < 1) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] C(fullBallCompactInterior ρ, Vec3) :=
  fullBallHarmonicGradientExtended (fullBallCompactInterior ρ)
    (fullBallCompactInterior_subset_unit hρ (hρσ.trans hσ)) hσ
    (fullBallCompactInterior_subset hρ hρσ)

/-- The literal actual compact hessian operator at any genuine interior margin. -/
def fullBallCompactHessianOperator (ρ σ : ℝ) (hρ : 0 < ρ) (hρσ : ρ < σ) (hσ : σ < 1) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] C(fullBallCompactInterior ρ, StokesGradientMatrix) :=
  fullBallHarmonicHessianExtended (fullBallCompactInterior ρ)
    (fullBallCompactInterior_subset_unit hρ (hρσ.trans hσ)) hσ
    (fullBallCompactInterior_subset hρ hρσ)

private theorem fullBallLimit_hilbert_norm_le {A : StokesGradientMatrix} {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ ij, ‖A ij‖ ≤ M) : ‖A‖ ≤ 3 * M := by
  have hsq : ‖A‖ ^ 2 ≤ 9 * M ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _ij : Fin 3 × Fin 3, M ^ 2 := by
        apply Finset.sum_le_sum
        intro ij _
        exact (sq_le_sq₀ (norm_nonneg _) hM).mpr (hb ij)
      _ = _ := by norm_num
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hM)).mp
  nlinarith

variable (ρ σ θ : ℝ) (hρ : 0 < ρ) (hρσ : ρ < σ) (hσθ : σ < θ) (hθ : θ < 1)

/-- The true compact smooth value operator converges on each genuine force. -/
theorem fullBallSmoothCompactValue_tendsto
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n)
    (hsmall : ∀ n, ε n ≤ (σ - ρ) / 6) (F : StokesEnergyForce (vec3Ball 0 1)) :
    Tendsto (fun n ↦ fullBallSmoothCompactValue ρ σ θ hρ hρσ hσθ hθ (hpos n) (hsmall n) F)
      atTop (𝓝 (fullBallCompactValueOperator ρ σ hρ hρσ (hσθ.trans hθ) F)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have he : ∀ᶠ n in atTop, ∀ x : fullBallCompactInterior ρ,
      |fullBallSpatialSmoothPressure σ θ F (hpos n) x.1 - fullBallSpatialPressureRepresentative
        F x.1| < δ / 2 := by
    have ht := (fullBallSpatialSmoothPressure_tendstoUniformly
      (hρ.trans hρσ) hσθ hθ F hε hpos).comp
        (Subtype.val : fullBallCompactInterior ρ → Vec3)
    have heq : (fun x : fullBallCompactInterior ρ ↦ fullBallSpatialCutoffPressure σ θ F x.1) =
        fun x ↦ fullBallSpatialPressureRepresentative F x.1 := by
      funext x
      exact fullBallSpatialCutoffPressure_eqOn (hρ.trans hρσ) hσθ F
        (fullBallSpatial_compact_inner hρ hρσ x)
    change TendstoUniformly (fun n (x : fullBallCompactInterior ρ) ↦
      fullBallSpatialSmoothPressure σ θ F (hpos n) x.1)
      (fun x ↦ fullBallSpatialCutoffPressure σ θ F x.1) atTop at ht
    rw [heq] at ht
    have hd := Metric.tendstoUniformly_iff.mp ht (δ / 2) (by positivity)
    exact hd.mono fun n hn x ↦ by
      have hh := hn x
      rw [dist_comm] at hh
      simpa only [dist_eq_norm, Real.norm_eq_abs] using hh
  filter_upwards [he] with n hn
  have hb : ‖fullBallSmoothCompactValue ρ σ θ hρ hρσ hσθ hθ (hpos n) (hsmall n) F -
      fullBallCompactValueOperator ρ σ hρ hρσ (hσθ.trans hθ) F‖ ≤ δ / 2 := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    change |fullBallSpatialSmoothPressureKernel σ θ (hρ.trans hρσ) hσθ hθ (hpos n) x.1 F -
      fullBallSpatialPressureRepresentative F x.1| ≤ _
    rw [fullBallSpatialSmoothPressureKernel_apply]
    exact (hn x).le
  simpa only [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)] using
    hb.trans_lt (half_lt_self hδ)

/-- The actual smooth value converges uniformly along moving compact force trajectories. -/
theorem fullBallSmoothCompactValue_tendstoUniformly
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n)
    (hsmall : ∀ n, ε n ≤ (σ - ρ) / 6)
    {f : K → StokesEnergyForce (vec3Ball 0 1)}
    {fs : ℕ → K → StokesEnergyForce (vec3Ball 0 1)} (hf : Continuous f)
    (hfs : TendstoUniformly fs f atTop) :
    TendstoUniformly
      (fun n x ↦ fullBallSmoothCompactValue ρ σ θ hρ hρσ hσθ hθ (hpos n) (hsmall n) (fs n x))
      (fun x ↦ fullBallCompactValueOperator ρ σ hρ hρσ (hσθ.trans hθ) (f x)) atTop :=
  tendstoUniformly_moving_operator_on_compact_domain
    (fun n ↦ fullBallSmoothCompactValue_opNorm_le ρ σ θ hρ hρσ hσθ hθ (hpos n) (hsmall n))
    (fullBallSmoothCompactValue_tendsto ρ σ θ hρ hρσ hσθ hθ hε hpos hsmall) hf hfs

/-- The true compact smooth gradient operator converges on each genuine force. -/
theorem fullBallSmoothCompactGradient_tendsto
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n)
    (hsmall : ∀ n, ε n ≤ (σ - ρ) / 6) (F : StokesEnergyForce (vec3Ball 0 1)) :
    Tendsto (fun n ↦ fullBallSmoothCompactGradient ρ σ θ hρ hρσ hσθ hθ (hpos n) (hsmall n) F)
      atTop (𝓝 (fullBallCompactGradientOperator ρ σ hρ hρσ (hσθ.trans hθ) F)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have he (i : Fin 3) : ∀ᶠ n in atTop, ∀ x : fullBallCompactInterior ρ,
      |spatialDeriv (fullBallSpatialSmoothPressure σ θ F (hpos n)) i x.1 - spatialDeriv
        (fullBallSpatialPressureRepresentative F) i x.1| < δ / 2 := by
    have ht := (fullBallSpatialSmoothPressure_spatialDeriv_tendstoUniformly
      (hρ.trans hρσ) hσθ hθ F i hε hpos).comp
        (Subtype.val : fullBallCompactInterior ρ → Vec3)
    have heq : (fun x : fullBallCompactInterior ρ ↦ spatialDeriv (fullBallSpatialCutoffPressure
      σ θ F) i x.1) =
        fun x ↦ spatialDeriv (fullBallSpatialPressureRepresentative F) i x.1 := by
      funext x
      exact congrArg (fun v : Vec3 ↦ v i)
        (classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball 0 σ)
          (fullBallSpatialCutoffPressure_eqOn (hρ.trans hρσ) hσθ F)
          (fullBallSpatial_compact_inner hρ hρσ x))
    change TendstoUniformly (fun n (x : fullBallCompactInterior ρ) ↦ spatialDeriv
      (fullBallSpatialSmoothPressure σ θ F (hpos n)) i x.1)
      (fun x ↦ spatialDeriv (fullBallSpatialCutoffPressure σ θ F) i x.1) atTop at ht
    rw [heq] at ht
    have hd := Metric.tendstoUniformly_iff.mp ht (δ / 2) (by positivity)
    exact hd.mono fun n hn x ↦ by
      have hh := hn x
      rw [dist_comm] at hh
      simpa only [dist_eq_norm, Real.norm_eq_abs] using hh
  filter_upwards [Filter.eventually_all.mpr he] with n hn
  have hb : ‖fullBallSmoothCompactGradient ρ σ θ hρ hρσ hσθ hθ (hpos n) (hsmall n) F -
      fullBallCompactGradientOperator ρ σ hρ hρσ (hσθ.trans hθ) F‖ ≤ δ / 2 := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    change |fullBallSpatialSmoothGradientKernel σ θ (hρ.trans hρσ) hσθ hθ (hpos n) i x.1 F -
      spatialDeriv (fullBallSpatialPressureRepresentative F) i x.1| ≤ _
    rw [fullBallSpatialSmoothGradientKernel_apply]
    exact (hn i x).le
  simpa only [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)] using
    hb.trans_lt (half_lt_self hδ)

/-- The actual smooth gradient converges uniformly along moving compact force trajectories. -/
theorem fullBallSmoothCompactGradient_tendstoUniformly
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n)
    (hsmall : ∀ n, ε n ≤ (σ - ρ) / 6)
    {f : K → StokesEnergyForce (vec3Ball 0 1)}
    {fs : ℕ → K → StokesEnergyForce (vec3Ball 0 1)} (hf : Continuous f)
    (hfs : TendstoUniformly fs f atTop) :
    TendstoUniformly
      (fun n x ↦ fullBallSmoothCompactGradient ρ σ θ hρ hρσ hσθ hθ (hpos n) (hsmall n) (fs n x))
      (fun x ↦ fullBallCompactGradientOperator ρ σ hρ hρσ (hσθ.trans hθ) (f x)) atTop :=
  tendstoUniformly_moving_operator_on_compact_domain
    (fun n ↦ fullBallSmoothCompactGradient_opNorm_le ρ σ θ hρ hρσ hσθ hθ (hpos n) (hsmall n))
    (fullBallSmoothCompactGradient_tendsto ρ σ θ hρ hρσ hσθ hθ hε hpos hsmall) hf hfs

/-- The true compact smooth hessian operator converges on each genuine force. -/
theorem fullBallSmoothCompactHessian_tendsto
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n)
    (hsmall : ∀ n, ε n ≤ (σ - ρ) / 6) (F : StokesEnergyForce (vec3Ball 0 1)) :
    Tendsto (fun n ↦ fullBallSmoothCompactHessian ρ σ θ hρ hρσ hσθ hθ (hpos n) (hsmall n) F)
      atTop (𝓝 (fullBallCompactHessianOperator ρ σ hρ hρσ (hσθ.trans hθ) F)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have he (ij : Fin 3 × Fin 3) : ∀ᶠ n in atTop, ∀ x : fullBallCompactInterior ρ,
      |mixedSecond (fullBallSpatialSmoothPressure σ θ F (hpos n)) ij.1 ij.2 x.1 - mixedSecond
        (fullBallSpatialPressureRepresentative F) ij.1 ij.2 x.1| < δ / 6 := by
    have ht := (fullBallSpatialSmoothPressure_mixedSecond_tendstoUniformly
      (hρ.trans hρσ) hσθ hθ F ij.1 ij.2 hε hpos).comp
        (Subtype.val : fullBallCompactInterior ρ → Vec3)
    have heq : (fun x : fullBallCompactInterior ρ ↦ mixedSecond (fullBallSpatialCutoffPressure
      σ θ F) ij.1 ij.2 x.1) =
        fun x ↦ mixedSecond (fullBallSpatialPressureRepresentative F) ij.1 ij.2 x.1 := by
      funext x
      exact mixedSecond_eqOn_of_eqOn (isOpen_vec3Ball 0 σ)
        (fullBallSpatialCutoffPressure_eqOn (hρ.trans hρσ) hσθ F) ij.1 ij.2
        (fullBallSpatial_compact_inner hρ hρσ x)
    change TendstoUniformly (fun n (x : fullBallCompactInterior ρ) ↦ mixedSecond
      (fullBallSpatialSmoothPressure σ θ F (hpos n)) ij.1 ij.2 x.1)
      (fun x ↦ mixedSecond (fullBallSpatialCutoffPressure σ θ F) ij.1 ij.2 x.1) atTop at ht
    rw [heq] at ht
    have hd := Metric.tendstoUniformly_iff.mp ht (δ / 6) (by positivity)
    exact hd.mono fun n hn x ↦ by
      have hh := hn x
      rw [dist_comm] at hh
      simpa only [dist_eq_norm, Real.norm_eq_abs] using hh
  filter_upwards [Filter.eventually_all.mpr he] with n hn
  have hb : ‖fullBallSmoothCompactHessian ρ σ θ hρ hρσ hσθ hθ (hpos n) (hsmall n) F -
      fullBallCompactHessianOperator ρ σ hρ hρσ (hσθ.trans hθ) F‖ ≤ δ / 2 := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    apply (fullBallLimit_hilbert_norm_le (M := δ / 6) (by positivity)
      (fun ij ↦ ?_)).trans_eq (by ring)
    change |fullBallSpatialSmoothHessianKernel σ θ (hρ.trans hρσ) hσθ hθ (hpos n) ij.1 ij.2 x.1
      F - mixedSecond (fullBallSpatialPressureRepresentative F) ij.1 ij.2 x.1| ≤ _
    rw [fullBallSpatialSmoothHessianKernel_apply]
    exact (hn ij x).le
  simpa only [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)] using
    hb.trans_lt (half_lt_self hδ)

/-- The actual smooth hessian converges uniformly along moving compact force trajectories. -/
theorem fullBallSmoothCompactHessian_tendstoUniformly
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n)
    (hsmall : ∀ n, ε n ≤ (σ - ρ) / 6)
    {f : K → StokesEnergyForce (vec3Ball 0 1)}
    {fs : ℕ → K → StokesEnergyForce (vec3Ball 0 1)} (hf : Continuous f)
    (hfs : TendstoUniformly fs f atTop) :
    TendstoUniformly
      (fun n x ↦ fullBallSmoothCompactHessian ρ σ θ hρ hρσ hσθ hθ (hpos n) (hsmall n) (fs n x))
      (fun x ↦ fullBallCompactHessianOperator ρ σ hρ hρσ (hσθ.trans hθ) (f x)) atTop :=
  tendstoUniformly_moving_operator_on_compact_domain
    (fun n ↦ fullBallSmoothCompactHessian_opNorm_le ρ σ θ hρ hρσ hσθ hθ (hpos n) (hsmall n))
    (fullBallSmoothCompactHessian_tendsto ρ σ θ hρ hρσ hσθ hθ hε hpos hsmall) hf hfs

end FluidSingularSets
