-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallSpatialKernels
public import FluidSingularSets.HarmonicHessianSmoothApprox

/-!
# Genuine bounded smooth pressure operators on arbitrary compact interiors

The actual scalar pressure and its first two derivatives retain uniform force
bounds under genuine convolution. Their compact continuous fields therefore
form actual bounded linear operators with a boundary-margin coefficient.
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

local instance fullBallSmoothForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance fullBallSmoothForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The true componentwise second-derivative force coefficient. -/
def fullBallHarmonicForceSecondCoefficient (σ : ℝ) : ℝ :=
  fullBallHarmonicHessianConstant σ *
    (4 * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ))

/-- The literal componentwise coefficient is nonnegative inside the unit ball. -/
theorem fullBallHarmonicForceSecondCoefficient_nonneg {σ : ℝ} (hσ : σ < 1) :
    0 ≤ fullBallHarmonicForceSecondCoefficient σ :=
  mul_nonneg (fullBallHarmonicHessianConstant_nonneg hσ)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg ENNReal.toReal_nonneg _))

/-- The actual compact ball lies inside the chosen larger harmonic ball. -/
theorem fullBallSpatial_compact_inner {ρ σ : ℝ} (hρ : 0 < ρ) (hρσ : ρ < σ)
    (x : fullBallCompactInterior ρ) : x.1 ∈ vec3Ball 0 σ :=
  fullBallCompactInterior_subset hρ hρσ x.property

/-- Every genuine smoothing neighborhood remains in the larger harmonic ball. -/
theorem fullBallSpatial_compact_closedBall_inner {ρ σ ε : ℝ}
    (hρ : 0 < ρ) (hρσ : ρ < σ) (hsmall : ε ≤ (σ - ρ) / 6)
    (x : fullBallCompactInterior ρ) : Metric.closedBall x.1 ε ⊆ vec3Ball 0 σ := by
  intro y hy
  have hx := x.property
  change x.1 ∈ closure (vec3Ball 0 ρ) at hx
  rw [closure_vec3Ball hρ] at hx
  change vec3EuclideanNorm (x.1 - 0) ≤ ρ at hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hy
  have hn : vec3EuclideanNorm (y - x.1) ≤ 3 * ε :=
    (euclideanNorm_le_three_mul_space_norm (y - x.1)).trans
      (mul_le_mul_of_nonneg_left hy (by norm_num : (0 : ℝ) ≤ 3))
  have ht := vec3EuclideanNorm_add_le (y - x.1) x.1
  rw [sub_add_cancel] at ht
  rw [mem_vec3Ball]
  norm_num only [sub_zero] at hx ⊢
  linarith

variable {σ θ : ℝ}

/-- The actual cutoff pressure value has the genuine boundary-margin force bound. -/
theorem fullBallSpatialCutoffPressure_value_bound
    (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1)
    (F : StokesEnergyForce (vec3Ball 0 1)) {x : Vec3} (hx : x ∈ vec3Ball 0 σ) :
    |fullBallSpatialCutoffPressure σ θ F x| ≤ fullBallHarmonicForceValueCoefficient σ * ‖F‖ := by
  let G := unitBallGradientFreeForceProjection F
  have hσone : σ < 1 := hσθ.trans hθ
  have heq : fullBallSpatialCutoffPressure σ θ F x = fullBallSpatialPressureRepresentative F x :=
    fullBallSpatialCutoffPressure_eqOn hσ hσθ F hx
  rw [heq]
  have hb := fullBallHarmonic_representative_value_bound
    (unitBallPressureFunction_memLp_threeHalves G.1)
    (unitBallStokesPressure_weaklyHarmonic G.1 G.property)
    (unitBallFullHarmonicForcePressureRepresentative_contDiff G)
    (unitBallFullHarmonicForcePressureRepresentative_ae G) hσone hx
  have ht := mul_le_mul_of_nonneg_left (unitBallPressureFunction_lpNorm_threeHalves_le G.1)
    (fullBallHarmonicValueConstant_nonneg hσone)
  have hl : fullBallHarmonicValueConstant σ *
      lpNorm (unitBallPressureFunction G.1) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (vec3Ball 0 1)) ≤ fullBallHarmonicForceValueCoefficient σ * ‖G‖ := by
    simpa only [fullBallHarmonicForceValueCoefficient, unitBallGradientFreeForce_norm_coe,
      mul_assoc] using ht
  have hf := mul_le_mul_of_nonneg_left (unitBallGradientFreeForceProjection_norm_le F)
    (fullBallHarmonicForceValueCoefficient_nonneg hσone)
  exact hb.trans (hl.trans hf)

/-- The actual cutoff pressure spatialDeriv has the genuine boundary-margin force bound. -/
theorem fullBallSpatialCutoffPressure_spatialDeriv_bound
    (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1)
    (F : StokesEnergyForce (vec3Ball 0 1)) {x : Vec3} (hx : x ∈ vec3Ball 0 σ) (i : Fin 3) :
    |spatialDeriv (fullBallSpatialCutoffPressure σ θ F) i x| ≤
      fullBallHarmonicForceGradientCoefficient σ * ‖F‖ := by
  let G := unitBallGradientFreeForceProjection F
  have hσone : σ < 1 := hσθ.trans hθ
  have heq : spatialDeriv (fullBallSpatialCutoffPressure σ θ F) i x = spatialDeriv
    (fullBallSpatialPressureRepresentative F) i x :=
    congrArg (fun v : Vec3 ↦ v i) (classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball 0 σ)
    (fullBallSpatialCutoffPressure_eqOn hσ hσθ F) hx)
  rw [heq]
  have hb := fullBallHarmonic_representative_gradient_bound
    (unitBallPressureFunction_memLp_threeHalves G.1)
    (unitBallStokesPressure_weaklyHarmonic G.1 G.property)
    (unitBallFullHarmonicForcePressureRepresentative_contDiff G)
    (unitBallFullHarmonicForcePressureRepresentative_ae G) hσone hx
  have ht := mul_le_mul_of_nonneg_left (unitBallPressureFunction_lpNorm_threeHalves_le G.1)
    (fullBallHarmonicGradientConstant_nonneg hσone)
  have hl : fullBallHarmonicGradientConstant σ *
      lpNorm (unitBallPressureFunction G.1) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (vec3Ball 0 1)) ≤ fullBallHarmonicForceGradientCoefficient σ * ‖G‖ := by
    simpa only [fullBallHarmonicForceGradientCoefficient, unitBallGradientFreeForce_norm_coe,
      mul_assoc] using ht
  have hf := mul_le_mul_of_nonneg_left (unitBallGradientFreeForceProjection_norm_le F)
    (fullBallHarmonicForceGradientCoefficient_nonneg hσone)
  exact ((abs_apply_le_vec3EuclideanNorm
    (classicalGradient (fullBallSpatialPressureRepresentative F) x) i).trans hb).trans
      (hl.trans hf)

/-- The actual cutoff pressure mixedSecond has the genuine boundary-margin force bound. -/
theorem fullBallSpatialCutoffPressure_mixedSecond_bound
    (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1)
    (F : StokesEnergyForce (vec3Ball 0 1)) {x : Vec3} (hx : x ∈ vec3Ball 0 σ) (i j : Fin 3) :
    |mixedSecond (fullBallSpatialCutoffPressure σ θ F) i j x| ≤
      fullBallHarmonicForceSecondCoefficient σ * ‖F‖ := by
  let G := unitBallGradientFreeForceProjection F
  have hσone : σ < 1 := hσθ.trans hθ
  have heq : mixedSecond (fullBallSpatialCutoffPressure σ θ F) i j x = mixedSecond
    (fullBallSpatialPressureRepresentative F) i j x :=
    mixedSecond_eqOn_of_eqOn (isOpen_vec3Ball 0 σ)
    (fullBallSpatialCutoffPressure_eqOn hσ hσθ F) i j hx
  rw [heq]
  have hb := fullBallHarmonic_representative_hessian_bound
    (unitBallPressureFunction_memLp_threeHalves G.1)
    (unitBallStokesPressure_weaklyHarmonic G.1 G.property)
    (unitBallFullHarmonicForcePressureRepresentative_contDiff G)
    (unitBallFullHarmonicForcePressureRepresentative_ae G) hσone hx i j
  have ht := mul_le_mul_of_nonneg_left (unitBallPressureFunction_lpNorm_threeHalves_le G.1)
    (fullBallHarmonicHessianConstant_nonneg hσone)
  have hl : fullBallHarmonicHessianConstant σ *
      lpNorm (unitBallPressureFunction G.1) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (vec3Ball 0 1)) ≤ fullBallHarmonicForceSecondCoefficient σ * ‖G‖ := by
    simpa only [fullBallHarmonicForceSecondCoefficient, unitBallGradientFreeForce_norm_coe,
      mul_assoc] using ht
  have hf := mul_le_mul_of_nonneg_left (unitBallGradientFreeForceProjection_norm_le F)
    (fullBallHarmonicForceSecondCoefficient_nonneg hσone)
  exact hb.trans (hl.trans hf)

private theorem fullBall_mollify_abs_le_three {g : Vec3 → ℝ} (hg : Continuous g)
    {ε M : ℝ} (hε : 0 < ε) (x : Vec3) (hx : |g x| ≤ M)
    (hb : ∀ y ∈ Metric.ball x ε, |g y| ≤ M) : |mollify g ε hε x| ≤ 3 * M := by
  have hm := (standardMollifier (d := 3) ε hε).dist_normed_convolution_le
    (μ := volume) hg.aestronglyMeasurable (x₀ := x) (ε := 2 * M) (by
      intro y hy
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by
        simpa only [Real.norm_eq_abs] using (show |g y| + |g x| ≤ 2 * M by linarith [hb y hy])))
  have ht := norm_add_le (mollify g ε hε x - g x) (g x)
  simp only [sub_add_cancel, Real.norm_eq_abs] at ht
  have hm' : dist (mollify g ε hε x) (g x) ≤ 2 * M := by
    simpa only [mollify, mollifier, dist_comm] using hm
  rw [dist_eq_norm, Real.norm_eq_abs] at hm'
  linarith

variable {ρ : ℝ}

/-- Actual smoothing retains a uniform genuine value bound on each compact interior. -/
theorem fullBallSpatialSmoothPressure_value_bound
    (hρ : 0 < ρ) (hρσ : ρ < σ) (hσθ : σ < θ) (hθ : θ < 1)
    (F : StokesEnergyForce (vec3Ball 0 1)) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ (σ - ρ) / 6) (x : fullBallCompactInterior ρ) :
    |fullBallSpatialSmoothPressure σ θ F hε x.1| ≤ 3 * fullBallHarmonicForceValueCoefficient σ
      * ‖F‖ := by
  have hσ : 0 < σ := hρ.trans hρσ
  let g := fullBallSpatialCutoffPressure σ θ F
  have hg : Continuous g := by
    exact (fullBallSpatialCutoffPressure_contDiff hσ hσθ hθ F).continuous
  have hb : |mollify g ε hε x.1| ≤ 3 * (fullBallHarmonicForceValueCoefficient σ * ‖F‖) :=
    fullBall_mollify_abs_le_three hg hε x.1
      (fullBallSpatialCutoffPressure_value_bound hσ hσθ hθ F
        (fullBallSpatial_compact_inner hρ hρσ x))
      (fun y hy ↦ fullBallSpatialCutoffPressure_value_bound hσ hσθ hθ F
        (fullBallSpatial_compact_closedBall_inner hρ hρσ hsmall x
          (Metric.ball_subset_closedBall hy)))
  simpa only [g, mul_assoc, fullBallSpatialSmoothPressure] using hb

/-- Actual smoothing retains a uniform genuine spatialDeriv bound on each compact interior. -/
theorem fullBallSpatialSmoothPressure_spatialDeriv_bound
    (hρ : 0 < ρ) (hρσ : ρ < σ) (hσθ : σ < θ) (hθ : θ < 1)
    (F : StokesEnergyForce (vec3Ball 0 1)) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ (σ - ρ) / 6) (x : fullBallCompactInterior ρ) (i : Fin 3) :
    |spatialDeriv (fullBallSpatialSmoothPressure σ θ F hε) i x.1| ≤ 3 *
      fullBallHarmonicForceGradientCoefficient σ * ‖F‖ := by
  have hσ : 0 < σ := hρ.trans hρσ
  let g := spatialDeriv (fullBallSpatialCutoffPressure σ θ F) i
  have hg : Continuous g := by
    have hd := (fullBallSpatialCutoffPressure_contDiff hσ hσθ hθ F).continuous_fderiv
      (by norm_num)
    exact hd.clm_apply continuous_const
  rw [fullBallSpatialSmoothPressure_spatialDeriv hσ hσθ hθ]
  have hb : |mollify g ε hε x.1| ≤ 3 * (fullBallHarmonicForceGradientCoefficient σ * ‖F‖) :=
    fullBall_mollify_abs_le_three hg hε x.1
      (fullBallSpatialCutoffPressure_spatialDeriv_bound hσ hσθ hθ F
        (fullBallSpatial_compact_inner hρ hρσ x) i)
      (fun y hy ↦ fullBallSpatialCutoffPressure_spatialDeriv_bound hσ hσθ hθ F
        (fullBallSpatial_compact_closedBall_inner hρ hρσ hsmall x
          (Metric.ball_subset_closedBall hy)) i)
  simpa only [g, mul_assoc, fullBallSpatialSmoothPressure] using hb

/-- Actual smoothing retains a uniform genuine mixedSecond bound on each compact interior. -/
theorem fullBallSpatialSmoothPressure_mixedSecond_bound
    (hρ : 0 < ρ) (hρσ : ρ < σ) (hσθ : σ < θ) (hθ : θ < 1)
    (F : StokesEnergyForce (vec3Ball 0 1)) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ (σ - ρ) / 6) (x : fullBallCompactInterior ρ) (i j : Fin 3) :
    |mixedSecond (fullBallSpatialSmoothPressure σ θ F hε) i j x.1| ≤ 3 *
      fullBallHarmonicForceSecondCoefficient σ * ‖F‖ := by
  have hσ : 0 < σ := hρ.trans hρσ
  let g := mixedSecond (fullBallSpatialCutoffPressure σ θ F) i j
  have hg : Continuous g := by
    have hd := (fullBallSpatialCutoffPressure_contDiff hσ hσθ hθ F).contDiff_fderiv_apply
      (m := (1 : ℕ∞)) (n := (2 : ℕ∞)) (by norm_num)
    have hp : ContDiff ℝ (1 : ℕ∞)
        (spatialDeriv (fullBallSpatialCutoffPressure σ θ F) j) :=
      hd.comp (contDiff_id.prodMk contDiff_const)
    exact (hp.continuous_fderiv (by norm_num)).clm_apply continuous_const
  rw [fullBallSpatialSmoothPressure_mixedSecond hσ hσθ hθ]
  have hb : |mollify g ε hε x.1| ≤ 3 * (fullBallHarmonicForceSecondCoefficient σ * ‖F‖) :=
    fullBall_mollify_abs_le_three hg hε x.1
      (fullBallSpatialCutoffPressure_mixedSecond_bound hσ hσθ hθ F
        (fullBallSpatial_compact_inner hρ hρσ x) i j)
      (fun y hy ↦ fullBallSpatialCutoffPressure_mixedSecond_bound hσ hσθ hθ F
        (fullBallSpatial_compact_closedBall_inner hρ hρσ hsmall x
          (Metric.ball_subset_closedBall hy)) i j)
  simpa only [g, mul_assoc, fullBallSpatialSmoothPressure] using hb

variable (ρ σ θ : ℝ) (hρ : 0 < ρ) (hρσ : ρ < σ) (hσθ : σ < θ) (hθ : θ < 1)

/-- The actual smoothed pressure values on the genuine compact spatial carrier. -/
def fullBallSmoothCompactValueMap {ε : ℝ} (hε : 0 < ε)
    (F : StokesEnergyForce (vec3Ball 0 1)) : C(fullBallCompactInterior ρ, ℝ) where
  toFun x := fullBallSpatialSmoothPressureKernel σ θ (hρ.trans hρσ) hσθ hθ hε x.1 F
  continuous_toFun :=
    ((fullBallSpatialSmoothPressureKernel_contDiff σ θ (hρ.trans hρσ) hσθ hθ hε).continuous.comp
      continuous_subtype_val).clm_apply continuous_const

/-- The actual smoothed gradient on the genuine compact spatial carrier. -/
def fullBallSmoothCompactGradientMap {ε : ℝ} (hε : 0 < ε)
    (F : StokesEnergyForce (vec3Ball 0 1)) : C(fullBallCompactInterior ρ, Vec3) where
  toFun x i := fullBallSpatialSmoothGradientKernel σ θ (hρ.trans hρσ) hσθ hθ hε i x.1 F
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact
      ((fullBallSpatialSmoothGradientKernel_contDiff σ θ (hρ.trans hρσ) hσθ hθ hε
        i).continuous.comp continuous_subtype_val).clm_apply continuous_const

/-- The actual derivative-first smooth Hilbert Hessian on the compact spatial carrier. -/
def fullBallSmoothCompactHessianMap {ε : ℝ} (hε : 0 < ε)
    (F : StokesEnergyForce (vec3Ball 0 1)) : C(fullBallCompactInterior ρ, StokesGradientMatrix)
      where
  toFun x := WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 ↦
    fullBallSpatialSmoothHessianKernel σ θ (hρ.trans hρσ) hσθ hθ hε ij.1 ij.2 x.1 F)
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 × Fin 3 ↦ ℝ)).comp
    apply continuous_pi
    intro ij
    exact
      ((fullBallSpatialSmoothHessianKernel_contDiff σ θ (hρ.trans hρσ) hσθ hθ hε ij.1
        ij.2).continuous.comp continuous_subtype_val).clm_apply continuous_const

private theorem fullBall_hilbertHessian_norm_le {A : StokesGradientMatrix} {M : ℝ}
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

/-- One genuine force bound holds uniformly for the actual smooth value fields. -/
theorem fullBallSmoothCompactValueMap_norm_le {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ (σ - ρ) / 6) (F : StokesEnergyForce (vec3Ball 0 1)) :
    ‖fullBallSmoothCompactValueMap ρ σ θ hρ hρσ hσθ hθ hε F‖ ≤ 3 *
      fullBallHarmonicForceValueCoefficient σ * ‖F‖ := by
  have hC := fullBallHarmonicForceValueCoefficient_nonneg (hσθ.trans hθ)
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change |fullBallSpatialSmoothPressureKernel σ θ (hρ.trans hρσ) hσθ hθ hε x.1 F| ≤ _
  rw [fullBallSpatialSmoothPressureKernel_apply]
  exact fullBallSpatialSmoothPressure_value_bound hρ hρσ hσθ hθ F hε hsmall x

/-- The actual smoothed value is a genuine bounded linear force operator. -/
def fullBallSmoothCompactValue {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ (σ - ρ) / 6) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] C(fullBallCompactInterior ρ, ℝ) :=
  ({ toFun := fullBallSmoothCompactValueMap ρ σ θ hρ hρσ hσθ hθ hε
     map_add' := fun F G ↦ by
       ext x
       exact (fullBallSpatialSmoothPressureKernel σ θ (hρ.trans hρσ) hσθ hθ hε x.1).map_add F G
     map_smul' := fun c F ↦ by
       ext x
       exact (fullBallSpatialSmoothPressureKernel σ θ (hρ.trans hρσ) hσθ hθ hε x.1).map_smul c F } :
    StokesEnergyForce (vec3Ball 0 1) →ₗ[ℝ] C(fullBallCompactInterior ρ, ℝ))
    |>.mkContinuous (3 * fullBallHarmonicForceValueCoefficient σ)
      (fullBallSmoothCompactValueMap_norm_le ρ σ θ hρ hρσ hσθ hθ hε hsmall)

/-- The actual smoothed value operators have one finite uniform norm bound. -/
theorem fullBallSmoothCompactValue_opNorm_le {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ (σ - ρ) / 6) :
    ‖fullBallSmoothCompactValue ρ σ θ hρ hρσ hσθ hθ hε hsmall‖ ≤
      3 * fullBallHarmonicForceValueCoefficient σ := by
  unfold fullBallSmoothCompactValue
  exact LinearMap.mkContinuous_norm_le _
    (mul_nonneg (by norm_num) (fullBallHarmonicForceValueCoefficient_nonneg (hσθ.trans hθ))) _

/-- One genuine force bound holds uniformly for the actual smooth gradient fields. -/
theorem fullBallSmoothCompactGradientMap_norm_le {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ (σ - ρ) / 6) (F : StokesEnergyForce (vec3Ball 0 1)) :
    ‖fullBallSmoothCompactGradientMap ρ σ θ hρ hρσ hσθ hθ hε F‖ ≤ 3 *
      fullBallHarmonicForceGradientCoefficient σ * ‖F‖ := by
  have hC := fullBallHarmonicForceGradientCoefficient_nonneg (hσθ.trans hθ)
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change |fullBallSpatialSmoothGradientKernel σ θ (hρ.trans hρσ) hσθ hθ hε i x.1 F| ≤ _
  rw [fullBallSpatialSmoothGradientKernel_apply]
  exact fullBallSpatialSmoothPressure_spatialDeriv_bound hρ hρσ hσθ hθ F hε hsmall x i

/-- The actual smoothed gradient is a genuine bounded linear force operator. -/
def fullBallSmoothCompactGradient {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ (σ - ρ) / 6) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] C(fullBallCompactInterior ρ, Vec3) :=
  ({ toFun := fullBallSmoothCompactGradientMap ρ σ θ hρ hρσ hσθ hθ hε
     map_add' := fun F G ↦ by
       ext x i
       exact (fullBallSpatialSmoothGradientKernel σ θ (hρ.trans hρσ) hσθ hθ hε i x.1).map_add F G
     map_smul' := fun c F ↦ by
       ext x i
       exact (fullBallSpatialSmoothGradientKernel σ θ (hρ.trans hρσ) hσθ hθ hε i x.1).map_smul
         c F } :
    StokesEnergyForce (vec3Ball 0 1) →ₗ[ℝ] C(fullBallCompactInterior ρ, Vec3))
    |>.mkContinuous (3 * fullBallHarmonicForceGradientCoefficient σ)
      (fullBallSmoothCompactGradientMap_norm_le ρ σ θ hρ hρσ hσθ hθ hε hsmall)

/-- The actual smoothed gradient operators have one finite uniform norm bound. -/
theorem fullBallSmoothCompactGradient_opNorm_le {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ (σ - ρ) / 6) :
    ‖fullBallSmoothCompactGradient ρ σ θ hρ hρσ hσθ hθ hε hsmall‖ ≤
      3 * fullBallHarmonicForceGradientCoefficient σ := by
  unfold fullBallSmoothCompactGradient
  exact LinearMap.mkContinuous_norm_le _
    (mul_nonneg (by norm_num) (fullBallHarmonicForceGradientCoefficient_nonneg (hσθ.trans hθ))) _

/-- One genuine force bound holds uniformly for the actual smooth hessian fields. -/
theorem fullBallSmoothCompactHessianMap_norm_le {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ (σ - ρ) / 6) (F : StokesEnergyForce (vec3Ball 0 1)) :
    ‖fullBallSmoothCompactHessianMap ρ σ θ hρ hρσ hσθ hθ hε F‖ ≤ 9 *
      fullBallHarmonicForceSecondCoefficient σ * ‖F‖ := by
  have hC := fullBallHarmonicForceSecondCoefficient_nonneg (hσθ.trans hθ)
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  apply (fullBall_hilbertHessian_norm_le
    (M := 3 * fullBallHarmonicForceSecondCoefficient σ * ‖F‖) (by positivity) (fun ij ↦
      ?_)).trans_eq (by ring)
  change |fullBallSpatialSmoothHessianKernel σ θ (hρ.trans hρσ) hσθ hθ hε ij.1 ij.2 x.1 F| ≤ _
  rw [fullBallSpatialSmoothHessianKernel_apply]
  exact fullBallSpatialSmoothPressure_mixedSecond_bound hρ hρσ hσθ hθ F hε hsmall x ij.1 ij.2

/-- The actual smoothed hessian is a genuine bounded linear force operator. -/
def fullBallSmoothCompactHessian {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ (σ - ρ) / 6) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] C(fullBallCompactInterior ρ, StokesGradientMatrix) :=
  ({ toFun := fullBallSmoothCompactHessianMap ρ σ θ hρ hρσ hσθ hθ hε
     map_add' := fun F G ↦ by
       ext x ij
       exact (fullBallSpatialSmoothHessianKernel σ θ (hρ.trans hρσ) hσθ hθ hε ij.1 ij.2
         x.1).map_add F G
     map_smul' := fun c F ↦ by
       ext x ij
       exact (fullBallSpatialSmoothHessianKernel σ θ (hρ.trans hρσ) hσθ hθ hε ij.1 ij.2
         x.1).map_smul c F } :
    StokesEnergyForce (vec3Ball 0 1) →ₗ[ℝ] C(fullBallCompactInterior ρ, StokesGradientMatrix))
    |>.mkContinuous (9 * fullBallHarmonicForceSecondCoefficient σ)
      (fullBallSmoothCompactHessianMap_norm_le ρ σ θ hρ hρσ hσθ hθ hε hsmall)

/-- The actual smoothed hessian operators have one finite uniform norm bound. -/
theorem fullBallSmoothCompactHessian_opNorm_le {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ (σ - ρ) / 6) :
    ‖fullBallSmoothCompactHessian ρ σ θ hρ hρσ hσθ hθ hε hsmall‖ ≤
      9 * fullBallHarmonicForceSecondCoefficient σ := by
  unfold fullBallSmoothCompactHessian
  exact LinearMap.mkContinuous_norm_le _
    (mul_nonneg (by norm_num) (fullBallHarmonicForceSecondCoefficient_nonneg (hσθ.trans hθ))) _

end FluidSingularSets
