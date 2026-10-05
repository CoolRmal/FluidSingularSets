-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.LocalStokesEnergy
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-!
# Genuine zero-boundary test Poincare estimates

The global Sobolev inequality and finite-volume Hölder give a Poincare estimate
for the actual compactly supported tests defining the Stokes energy completion.
All support and derivative facts are derived from the smooth test data. The
bound is finite on every measurable finite-volume domain.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The actual values of the vector test underlying the gradient completion. -/
def stokesTestVelocity {U : Set Vec3} (φ : StokesVectorTest U) : Vec3 → Vec3 :=
  fun x i ↦ φ i x

/-- The actual values genuinely belong to `L²`. -/
theorem stokesTestVelocity_memLp {U : Set Vec3} (φ : StokesVectorTest U) :
    MemLp (stokesTestVelocity φ) 2 (volume.restrict U) := by
  apply MemLp.of_eval
  intro i
  exact ((φ i).contDiff.continuous.memLp_of_hasCompactSupport
    (φ i).hasCompactSupport).mono_measure Measure.restrict_le_self

/-- The actual test velocity as an `L²` equivalence class. -/
def stokesTestVelocityL2 {U : Set Vec3} (φ : StokesVectorTest U) :
    Lp Vec3 2 (volume.restrict U) :=
  (stokesTestVelocity_memLp φ).toLp (stokesTestVelocity φ)

/-- Compactly supported smooth test gradients vanish outside their prescribed domain. -/
theorem stokesTestGradient_eq_zero_off {U : Set Vec3} (φ : StokesVectorTest U)
    {x : Vec3} (hx : x ∉ U) : stokesTestGradient φ x = 0 := by
  ext ij
  change (fderiv ℝ (φ ij.2).toFun x) (basisVec ij.1) = 0
  have hout : x ∉ tsupport (φ ij.2).toFun :=
    fun h ↦ hx ((φ ij.2).tsupport_subset h)
  rw [fderiv_of_notMem_tsupport ℝ hout]
  rfl

/-- Consequently the global gradient norm is exactly its domain-restricted norm. -/
theorem stokesTestGradient_global_eLpNorm {U : Set Vec3} (hU : MeasurableSet U)
    (φ : StokesVectorTest U) (p : ℝ≥0∞) :
    eLpNorm (stokesTestGradient φ) p volume =
      eLpNorm (stokesTestGradient φ) p (volume.restrict U) := by
  have hind : U.indicator (stokesTestGradient φ) = stokesTestGradient φ := by
    funext x
    by_cases hx : x ∈ U
    · simp [hx]
    · simp [hx, stokesTestGradient_eq_zero_off φ hx]
  rw [← hind, eLpNorm_indicator_eq_eLpNorm_restrict hU, hind]

/-- The actual scalar Fréchet derivative is controlled by the Hilbert matrix gradient. -/
theorem fderiv_stokesTest_component_norm_le {U : Set Vec3} (φ : StokesVectorTest U)
    (j : Fin 3) (x : Vec3) :
    ‖fderiv ℝ (φ j).toFun x‖ ≤ 3 * ‖stokesTestGradient φ x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  calc
    ‖(fderiv ℝ (φ j).toFun x) z‖ =
        ‖∑ i : Fin 3, z i • (fderiv ℝ (φ j).toFun x) (basisVec i)‖ := by
      rw [← sum_smul_basisVec z, map_sum]
      simp
    _ ≤ ∑ i : Fin 3, ‖z i • (fderiv ℝ (φ j).toFun x) (basisVec i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖z‖ * ‖stokesTestGradient φ x‖ := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_smul]
      apply mul_le_mul (norm_le_pi_norm z i) ?_ (norm_nonneg _) (norm_nonneg _)
      exact PiLp.norm_apply_le (stokesTestGradient φ x) (i, j)
    _ = 3 * ‖stokesTestGradient φ x‖ * ‖z‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The finite global Sobolev constant used in the zero-boundary Poincare estimate. -/
def stokesGlobalSobolevConstant : ℝ≥0 :=
  eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Vec3) 2

/-- The genuine global Sobolev bound for each test component. -/
theorem stokesTest_component_global_sobolev {U : Set Vec3} (φ : StokesVectorTest U)
    (j : Fin 3) :
    eLpNorm (φ j).toFun 6 volume ≤
      (stokesGlobalSobolevConstant : ℝ≥0∞) * 3 *
        eLpNorm (stokesTestGradient φ) 2 volume := by
  have hs : eLpNorm (φ j).toFun 6 volume ≤
      (stokesGlobalSobolevConstant : ℝ≥0∞) *
        eLpNorm (fderiv ℝ (φ j).toFun) 2 volume := by
    simpa [stokesGlobalSobolevConstant] using
      eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure Vec3)
        ((φ j).contDiff.of_le (by simp)) (φ j).hasCompactSupport
        (by norm_num : (1 : ℝ≥0) ≤ 2)
        (by norm_num : 0 < Module.finrank ℝ Vec3)
        (by norm_num : ((6 : ℝ≥0) : ℝ)⁻¹ =
          ((2 : ℝ≥0) : ℝ)⁻¹ - (Module.finrank ℝ Vec3 : ℝ)⁻¹)
  have hd : eLpNorm (fderiv ℝ (φ j).toFun) 2 volume ≤
      (3 : ℝ≥0) • eLpNorm (stokesTestGradient φ) 2 volume := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      ((φ j).contDiff.continuous_fderiv (by simp)).aestronglyMeasurable
    exact ae_of_all _ (fun x ↦ by exact_mod_cast fderiv_stokesTest_component_norm_le φ j x)
  calc
    _ ≤ _ := hs
    _ ≤ (stokesGlobalSobolevConstant : ℝ≥0∞) *
        ((3 : ℝ≥0) • eLpNorm (stokesTestGradient φ) 2 volume) := by gcongr
    _ = _ := by simp [ENNReal.smul_def, mul_assoc]

/-- The domain-dependent Poincare constant is finite whenever the domain has finite volume. -/
def stokesTestPoincareConstant (U : Set Vec3) : ℝ≥0∞ :=
  9 * (stokesGlobalSobolevConstant : ℝ≥0∞) * volume U ^ (1 / 3 : ℝ)

theorem stokesTestPoincareConstant_ne_top {U : Set Vec3} (hU : volume U ≠ ∞) :
    stokesTestPoincareConstant U ≠ ∞ := by
  unfold stokesTestPoincareConstant
  finiteness

/-- The actual compactly supported velocity test satisfies zero-boundary Poincare. -/
theorem stokesTestVelocity_eLpNorm_le {U : Set Vec3} (hU : MeasurableSet U)
    (φ : StokesVectorTest U) :
    eLpNorm (stokesTestVelocity φ) 2 (volume.restrict U) ≤
      stokesTestPoincareConstant U * eLpNorm (stokesTestGradient φ) 2 (volume.restrict U) := by
  have hc (j : Fin 3) : eLpNorm (φ j).toFun 2 (volume.restrict U) ≤
      (stokesGlobalSobolevConstant : ℝ≥0∞) * 3 * volume U ^ (1 / 3 : ℝ) *
        eLpNorm (stokesTestGradient φ) 2 (volume.restrict U) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict U)
      (by norm_num : (2 : ℝ≥0∞) ≤ 6) (φ j).contDiff.continuous.aestronglyMeasurable
    norm_num at h
    calc
      _ ≤ eLpNorm (φ j).toFun 6 (volume.restrict U) * volume U ^ (1 / 3 : ℝ) := by
        simpa using h
      _ ≤ eLpNorm (φ j).toFun 6 volume * volume U ^ (1 / 3 : ℝ) := by
        gcongr
        exact Measure.restrict_le_self
      _ ≤ ((stokesGlobalSobolevConstant : ℝ≥0∞) * 3 *
          eLpNorm (stokesTestGradient φ) 2 volume) * volume U ^ (1 / 3 : ℝ) := by
        gcongr
        exact stokesTest_component_global_sobolev φ j
      _ = _ := by rw [stokesTestGradient_global_eLpNorm hU]; ring
  have hm : eLpNorm (stokesTestVelocity φ) 2 (volume.restrict U) ≤
      eLpNorm (fun x ↦ ∑ j : Fin 3, ‖φ j x‖) 2 (volume.restrict U) := by
    apply eLpNorm_mono_enorm
    · exact (stokesTestVelocity_memLp φ).aestronglyMeasurable
    · intro x
      have hnorm : ‖stokesTestVelocity φ x‖ ≤ ‖∑ j : Fin 3, ‖φ j x‖‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))]
        apply (pi_norm_le_iff_of_nonneg
          (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))).mpr
        intro j
        exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j)
      simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hnorm
  calc
    _ ≤ _ := hm
    _ = eLpNorm (∑ j : Fin 3, fun x ↦ ‖φ j x‖) 2 (volume.restrict U) := rfl
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x ↦ ‖φ j x‖) 2 (volume.restrict U) :=
      eLpNorm_sum_le (by norm_num)
    _ = ∑ j : Fin 3, eLpNorm (φ j).toFun 2 (volume.restrict U) := by
      apply Finset.sum_congr rfl
      intro j _
      exact eLpNorm_norm (φ j).toFun (φ j).contDiff.continuous.aestronglyMeasurable
    _ ≤ ∑ _j : Fin 3, (stokesGlobalSobolevConstant : ℝ≥0∞) * 3 *
        volume U ^ (1 / 3 : ℝ) *
          eLpNorm (stokesTestGradient φ) 2 (volume.restrict U) :=
      Finset.sum_le_sum (fun j _ ↦ hc j)
    _ = _ := by simp [stokesTestPoincareConstant, Finset.sum_const]; ring

/-- The finite real norm bound is suitable for a continuous extension from test gradients. -/
theorem stokesTestVelocityL2_norm_le {U : Set Vec3} (hU : MeasurableSet U)
    (hvol : volume U ≠ ∞) (φ : StokesVectorTest U) :
    ‖stokesTestVelocityL2 φ‖ ≤ (stokesTestPoincareConstant U).toReal *
      ‖stokesTestGradientL2 φ‖ := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (stokesTestPoincareConstant_ne_top hvol)
      (stokesTestGradient_memLp φ).eLpNorm_ne_top)
    (stokesTestVelocity_eLpNorm_le hU φ)
  rw [ENNReal.toReal_mul] at h
  simpa only [stokesTestVelocityL2, stokesTestGradientL2, Lp.norm_toLp] using h

/-- Zero gradient energy forces the actual zero-boundary velocity class to vanish. -/
theorem stokesTestVelocityL2_eq_zero_of_gradient_eq_zero {U : Set Vec3}
    (hU : MeasurableSet U) (hvol : volume U ≠ ∞) (φ : StokesVectorTest U)
    (hgrad : stokesTestGradientL2 φ = 0) : stokesTestVelocityL2 φ = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa [hgrad] using stokesTestVelocityL2_norm_le hU hvol φ

end FluidSingularSets
