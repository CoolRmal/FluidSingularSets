-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallPressureC2

/-!
# Quantitative actual harmonic Stokes pressure bounds

The true L² pressure bound and finite-volume exponent comparison control the
first Weyl estimate by the genuine force norm. A second Weyl estimate on each
actual first derivative controls the actual Hessian. Equality of continuous
representatives identifies all derivatives pointwise on interior balls.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Actual derivatives agree wherever two functions agree on an open neighborhood. -/
theorem classicalGradient_eqOn_of_eqOn {U : Set Vec3} {f g : Vec3 → ℝ}
    (hU : IsOpen U) (heq : EqOn f g U) : EqOn (classicalGradient f) (classicalGradient g) U := by
  intro x hx
  have hlocal : f =ᶠ[𝓝 x] g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact heq hy
  have hd := hlocal.fderiv_eq (𝕜 := ℝ)
  ext i
  exact congrArg (fun L : Vec3 →L[ℝ] ℝ ↦ L (basisVec i)) hd

/-- A genuine C¹ harmonic function inherits the native Weyl gradient estimate itself. -/
theorem harmonic_contDiffOn_gradient_bound {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ) (hH : ContDiffOn ℝ (1 : ℕ∞) H (vec3Ball x₀ ρ))
    (hmem : MemLp H (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball x₀ ρ)))
    (hweak : WeaklyHarmonicOn (vec3Ball x₀ ρ) H) :
    ∀ x ∈ vec3Ball x₀ (ρ / 2), vec3EuclideanNorm (classicalGradient H x) ≤
      1728 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
        lpNorm H (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball x₀ ρ)) := by
  have hm := hmem
  have hw := hweak
  rw [← euclideanBall_eq_vec3Ball hρ] at hm hw
  obtain ⟨G, hG, hae, _hval, hgrad⟩ := weakly_harmonic_interior_smooth hρ hm hw
  rw [euclideanBall_eq_vec3Ball (by positivity : 0 < ρ / 2)] at hG hae hgrad
  have hsub : vec3Ball x₀ (ρ / 2) ⊆ vec3Ball x₀ ρ := vec3Ball_mono (by linarith)
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq hae (isOpen_vec3Ball x₀ (ρ / 2))
    (hH.continuousOn.mono hsub) hG.continuousOn
  have hd := classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball x₀ (ρ / 2)) heq
  intro x hx
  rw [hd hx]
  simpa only [euclideanBall_eq_vec3Ball hρ] using hgrad x hx

/-- Finite-volume L² to L^(3/2) comparison for the actual constructed pressure. -/
theorem unitBallPressureFunction_lpNorm_threeHalves_le
    (F : StokesEnergyForce (vec3Ball 0 1)) :
    lpNorm (unitBallPressureFunction F) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball 0 1)) ≤
        4 * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ) * ‖F‖ := by
  let p : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)) := unitBallStokesPressure F
  have hp := Lp.memLp p
  have hle := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := 2) (by norm_num) hp.aestronglyMeasurable
  norm_num only [ENNReal.toReal_ofReal, ENNReal.toReal_ofNat, div_div,
    Measure.restrict_apply_univ] at hle
  have hfinite : eLpNorm p 2 (volume.restrict (vec3Ball 0 1)) *
      volume (vec3Ball 0 1) ^ (1 / 6 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top hp.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) volume_vec3Ball_lt_top.ne)
  have ht := ENNReal.toReal_mono hfinite hle
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← Lp.norm_def] at ht
  change lpNorm (unitBallPressureFunction F) _ _ ≤ _ at ht
  calc
    _ ≤ ‖p‖ * (volume (vec3Ball 0 1)).toReal ^ (1 / 6 : ℝ) := ht
    _ ≤ (4 * ‖F‖) * (volume (vec3Ball 0 1)).toReal ^ (1 / 6 : ℝ) :=
      mul_le_mul_of_nonneg_right (unitBallStokesPressure_norm F)
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    _ = _ := by ring

/-- A fixed genuine force-to-interior-gradient constant. -/
def unitBallPressureGradientConstant : ℝ :=
  1728 * harmonicInteriorGradientSupConstant *
    (4 * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ))

theorem unitBallPressureGradientConstant_nonneg : 0 ≤ unitBallPressureGradientConstant := by
  unfold unitBallPressureGradientConstant
  exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1728)
    harmonicInteriorGradientSupConstant_nonneg)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.rpow_nonneg ENNReal.toReal_nonneg _))

/-- A fixed genuine force-to-interior-Hessian constant. -/
def unitBallPressureHessianConstant : ℝ :=
  1728 * harmonicInteriorGradientSupConstant * ((1 / 4 : ℝ) ^ 3)⁻¹ *
    (unitBallPressureGradientConstant *
      (volume (vec3Ball (0 : Vec3) (1 / 4))).toReal ^ (2 / 3 : ℝ))

theorem unitBallPressureHessianConstant_nonneg : 0 ≤ unitBallPressureHessianConstant := by
  unfold unitBallPressureHessianConstant
  exact mul_nonneg (mul_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1728)
      harmonicInteriorGradientSupConstant_nonneg) (by positivity))
    (mul_nonneg unitBallPressureGradientConstant_nonneg
      (Real.rpow_nonneg ENNReal.toReal_nonneg _))

/-- Any actual C² representative has the genuine force-norm gradient and Hessian bounds. -/
theorem unitBallPressure_representative_derivative_bounds
    (F : StokesEnergyForce (vec3Ball 0 1))
    (hweak : WeaklyHarmonicOn (vec3Ball 0 1) (unitBallPressureFunction F))
    (H : Vec3 → ℝ) (hH : ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 (1 / 4)))
    (hae : unitBallPressureFunction F =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))] H) :
    (∀ x ∈ vec3Ball 0 (1 / 4), vec3EuclideanNorm (classicalGradient H x) ≤
      unitBallPressureGradientConstant * ‖F‖) ∧
    (∀ x ∈ vec3Ball 0 (1 / 8), ∀ i j : Fin 3,
      |mixedSecond H i j x| ≤ unitBallPressureHessianConstant * ‖F‖) := by
  have hm := unitBallPressureFunction_memLp_threeHalves F
  have hw := hweak
  rw [← euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1)] at hm hw
  obtain ⟨G, hG, hGa, _hGval, hGgrad⟩ := weakly_harmonic_interior_smooth
    (by norm_num : (0 : ℝ) < 1) hm hw
  rw [euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] at hG hGa hGgrad
  have hsub : vec3Ball (0 : Vec3) (1 / 4) ⊆ vec3Ball 0 (1 / 2) :=
    vec3Ball_mono (by norm_num)
  have hHG : H =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))] G :=
    hae.symm.trans (ae_restrict_of_ae_restrict_of_subset hsub hGa)
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq hHG (isOpen_vec3Ball 0 (1 / 4))
    hH.continuousOn (hG.continuousOn.mono hsub)
  have hderiv := classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 4)) heq
  have hfirst : ∀ x ∈ vec3Ball 0 (1 / 4), vec3EuclideanNorm (classicalGradient H x) ≤
      unitBallPressureGradientConstant * ‖F‖ := by
    intro x hx
    rw [hderiv hx]
    have hg := hGgrad x (hsub hx)
    rw [euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1)] at hg
    norm_num only [one_pow, inv_one, mul_one] at hg
    exact hg.trans (by
      unfold unitBallPressureGradientConstant
      have ht := mul_le_mul_of_nonneg_left (unitBallPressureFunction_lpNorm_threeHalves_le F)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1728)
          harmonicInteriorGradientSupConstant_nonneg)
      convert ht using 1
      ring)
  refine ⟨hfirst, ?_⟩
  have hHweak := localWeaklyHarmonicOn_congr_ae hae
    (localWeaklyHarmonicOn_restrict (vec3Ball_mono (by norm_num : (1 / 4 : ℝ) ≤ 1)) hweak)
  have hHone : ContDiffOn ℝ (1 : ℕ∞) H (vec3Ball 0 (1 / 4)) :=
    hH.of_le (by norm_num)
  let : IsFiniteMeasure (volume.restrict (vec3Ball (0 : Vec3) (1 / 4))) :=
    isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  have hpC1 : ∀ j : Fin 3, ContDiffOn ℝ (1 : ℕ∞) (spatialDeriv H j)
      (vec3Ball 0 (1 / 4)) := by
    intro j
    exact ((contDiffOn_succ_iff_fderiv_of_isOpen (n := 1)
      (isOpen_vec3Ball 0 (1 / 4))).mp hH).2.2.clm_apply contDiffOn_const
  have hpnorm : ∀ j : Fin 3, ∀ x ∈ vec3Ball 0 (1 / 4), ‖spatialDeriv H j x‖ ≤
      unitBallPressureGradientConstant * ‖F‖ := by
    intro j x hx
    rw [Real.norm_eq_abs]
    exact (abs_apply_le_vec3EuclideanNorm (classicalGradient H x) j).trans (hfirst x hx)
  have hpMem : ∀ j : Fin 3, MemLp (spatialDeriv H j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball 0 (1 / 4))) := by
    intro j
    apply MemLp.of_bound ((hpC1 j).continuousOn.aestronglyMeasurable
      (isOpen_vec3Ball 0 (1 / 4)).measurableSet) (unitBallPressureGradientConstant * ‖F‖)
    filter_upwards [ae_restrict_mem (isOpen_vec3Ball 0 (1 / 4)).measurableSet] with x hx
    exact hpnorm j x hx
  have hpLp : ∀ j : Fin 3,
      lpNorm (spatialDeriv H j) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (vec3Ball 0 (1 / 4))) ≤
          (unitBallPressureGradientConstant * ‖F‖) *
            (volume (vec3Ball (0 : Vec3) (1 / 4))).toReal ^ (2 / 3 : ℝ) := by
    intro j
    have ht := lpNorm_bound_on (isOpen_vec3Ball 0 (1 / 4)).measurableSet
      (p := ENNReal.ofReal (3 / 2 : ℝ)) (by norm_num) (by norm_num)
      (unitBallPressureGradientConstant * ‖F‖)
      (mul_nonneg unitBallPressureGradientConstant_nonneg (norm_nonneg F)) (hpnorm j)
    norm_num at ht ⊢
    exact ht
  intro x hx i j
  have ht := harmonic_contDiffOn_gradient_bound (by norm_num : (0 : ℝ) < 1 / 4)
    (hpC1 j) (hpMem j)
    (weaklyHarmonicOn_spatialDeriv_of_contDiffOn (isOpen_vec3Ball 0 (1 / 4))
      hHone hHweak j) x (by
        simpa only [show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] using hx)
  have hb := mul_le_mul_of_nonneg_left (hpLp j)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1728)
      harmonicInteriorGradientSupConstant_nonneg)
      (by positivity : 0 ≤ ((1 / 4 : ℝ) ^ 3)⁻¹))
  have hfinal := (abs_apply_le_vec3EuclideanNorm (classicalGradient (spatialDeriv H j) x) i)
    |>.trans (ht.trans hb)
  change |mixedSecond H i j x| ≤ _ at hfinal
  convert hfinal using 1
  simp only [unitBallPressureHessianConstant]
  ring

end FluidSingularSets
