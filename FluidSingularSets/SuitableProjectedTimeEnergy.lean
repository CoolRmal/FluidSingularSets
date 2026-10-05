-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SuitableProjectedLocalEnergy
public import FluidSingularSets.TestedTimeEnergy

/-!
# Actual projected energy at almost every time

The genuine nonsmooth projected local energy inequality is tested with the
actual smooth backward time ramps. True spatial integrals are extended by zero
outside the original test interval, and Lebesgue differentiation extracts the
almost-every-time energy and dissipation inequality.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology BigOperators ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The literal tested corrected velocity energy. -/
def suitableProjectedEnergyDensity
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) (ψ : Vec3 × ℝ → ℝ)
    (z : unitBallPressureCompactInterior × ℝ) : ℝ :=
  vec3EuclideanNorm (u (z.1.1, z.2) +
    suitableProjectedHarmonicGradient u D p t₀ z) ^ 2 * ψ (z.1.1, z.2)

/-- The literal tested corrected gradient dissipation, with its true coefficient two. -/
def suitableProjectedDissipationDensity
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) (ψ : Vec3 × ℝ → ℝ)
    (z : unitBallPressureCompactInterior × ℝ) : ℝ :=
  2 * projectedGradientSquare
    (D (z.1.1, z.2) + suitableProjectedHarmonicDerivative u D p t₀ z) * ψ (z.1.1, z.2)

/-- The actual projected right hand side, obtained from the literal deficit. -/
def suitableProjectedRhsDensity
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) (ψ : Vec3 × ℝ → ℝ)
    (z : unitBallPressureCompactInterior × ℝ) : ℝ :=
  suitableProjectedDissipationDensity u D p t₀ ψ z -
    suitableProjectedLocalEnergyDensity u D p t₀ ψ z

/-- The actual scalar smooth time multiplier has precisely the energy derivative term. -/
theorem suitableProjectedLocalEnergyDensity_mul_time
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) {ψ : Vec3 × ℝ → ℝ} {χ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (z : unitBallPressureCompactInterior × ℝ) :
    suitableProjectedLocalEnergyDensity u D p t₀ (fun w ↦ ψ w * χ w.2) z =
      suitableProjectedLocalEnergyDensity u D p t₀ ψ z * χ z.2 -
        suitableProjectedEnergyDensity u D p t₀ ψ z * deriv χ z.2 := by
  let U : Vec3 := u ((z.1.1, z.2) : ParabolicPoint)
  let H := suitableProjectedHarmonicGradient u D p t₀ z
  let W := D ((z.1.1, z.2) : ParabolicPoint)
  let B := suitableProjectedHarmonicDerivative u D p t₀ z
  let P := p ((z.1.1, z.2) : ParabolicPoint) -
    harmonicCompactPressureValues (-unitBallMomentumForceCurve u D p z.2) z.1
  let w : Vec3 × ℝ := (z.1.1, z.2)
  have hτ := timePartial_mul_time hψ hχ w
  have hG : (fun j ↦ spatialPartial (fun v ↦ ψ v * χ v.2) j w) =
      (fun j ↦ spatialPartial ψ j w * χ z.2) := by
    funext j
    exact spatialPartial_mul_time hψ j w
  have hΛ : (∑ j, spatialSecondPartial (fun v ↦ ψ v * χ v.2) j j w) =
      (∑ j, spatialSecondPartial ψ j j w) * χ z.2 := by
    simp_rw [spatialSecondPartial_mul_time hψ]
    exact (Finset.sum_mul _ _ _).symm
  change projectedEnergyDeficitPolynomial U H
    (fun j ↦ spatialPartial (fun v ↦ ψ v * χ v.2) j w) W B P
    (ψ w * χ z.2) (timePartial (fun v ↦ ψ v * χ v.2) w)
    (∑ j, spatialSecondPartial (fun v ↦ ψ v * χ v.2) j j w) =
      projectedEnergyDeficitPolynomial U H (fun j ↦ spatialPartial ψ j w) W B P
        (ψ w) (timePartial ψ w) (∑ j, spatialSecondPartial ψ j j w) * χ z.2 -
          vec3EuclideanNorm (U + H) ^ 2 * ψ w * deriv χ z.2
  rw [hτ, hG, hΛ]
  simp only [projectedEnergyDeficitPolynomial, Fin.sum_univ_three]
  ring

/-- The actual nonnegative test gives nonnegative corrected energy at every point. -/
theorem suitableProjectedEnergyDensity_nonneg
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) {ψ : Vec3 × ℝ → ℝ}
    (hψ : ∀ z, 0 ≤ ψ z) (z : unitBallPressureCompactInterior × ℝ) :
    0 ≤ suitableProjectedEnergyDensity u D p t₀ ψ z :=
  mul_nonneg (sq_nonneg _) (hψ (z.1.1, z.2))

/-- The literal corrected gradient dissipation is nonnegative at every point. -/
theorem suitableProjectedDissipationDensity_nonneg
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) {ψ : Vec3 × ℝ → ℝ}
    (hψ : ∀ z, 0 ≤ ψ z) (z : unitBallPressureCompactInterior × ℝ) :
    0 ≤ suitableProjectedDissipationDensity u D p t₀ ψ z :=
  mul_nonneg (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
      (hψ (z.1.1, z.2))

variable {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

set_option maxHeartbeats 1000000 in
/-- Every literal density used in time extraction is integrable directly from suitability. -/
theorem suitable_projected_time_energy_integrable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z)
    (hsupp : tsupport ψ ⊆
      unitBallPressureCompactInterior ×ˢ Ioo (t₀ - 4) (t₀ + 4)) :
    Integrable (suitableProjectedEnergyDensity u D p t₀ ψ)
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) ∧
      Integrable (suitableProjectedDissipationDensity u D p t₀ ψ)
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) ∧
      Integrable (suitableProjectedRhsDensity u D p t₀ ψ)
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) := by
  let J := Ioo (t₀ - 4) (t₀ + 4)
  let μ := harmonicInteriorMeasure
  let ν := volume.restrict J
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
    ((measure_mono Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne
  let : ENNReal.HolderTriple 2 2 1 := by
    have h : Real.HolderTriple 2 2 1 := by constructor <;> norm_num
    simpa using h.ennrealOfReal
  obtain ⟨hU, hD, _hp⟩ := suitable_harmonicInterior_memLp hsol hdom
  obtain ⟨hH, hB⟩ := suitable_harmonicInterior_correction_memLp_top hsol hdom
  have hΨ : MemLp (fun z : unitBallPressureCompactInterior × ℝ ↦ ψ (z.1.1, z.2)) ⊤
      (μ.prod ν) := by
    obtain ⟨C, hC⟩ := exists_bound_of_mem_spaceTimeTestFunction hψ
    exact MemLp.of_bound
      (hψ.1.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        continuous_snd)).aestronglyMeasurable C (ae_of_all _ fun z ↦ hC (z.1.1, z.2))
  have hV (i : Fin 3) : MemLp (fun z : unitBallPressureCompactInterior × ℝ ↦
      u (z.1.1, z.2) i + suitableProjectedHarmonicGradient u D p t₀ z i) 2 (μ.prod ν) :=
    ((memLp_pi_iff.mp hU i).mono_exponent (by norm_num)).add
      ((memLp_pi_iff.mp hH i).mono_exponent le_top)
  have hW (i j : Fin 3) : MemLp (fun z : unitBallPressureCompactInterior × ℝ ↦
      D (z.1.1, z.2) i j + suitableProjectedHarmonicDerivative u D p t₀ z i j)
      2 (μ.prod ν) :=
    (memLp_pi_iff.mp (memLp_pi_iff.mp hD i) j).add ((hB i j).mono_exponent le_top)
  have hEi (i : Fin 3) : Integrable (fun z : unitBallPressureCompactInterior × ℝ ↦
      (u (z.1.1, z.2) i + suitableProjectedHarmonicGradient u D p t₀ z i) ^ 2 *
        ψ (z.1.1, z.2)) (μ.prod ν) := by
    have hi := (((hV i).mul (r := 1) (hV i)).mul (r := 1) hΨ).integrable (by norm_num)
    exact hi.congr (ae_of_all _ fun z ↦
      congrArg (fun a ↦ a * ψ (z.1.1, z.2)) (pow_two
        (u (z.1.1, z.2) i + suitableProjectedHarmonicGradient u D p t₀ z i)).symm)
  have hDi (i j : Fin 3) : Integrable (fun z : unitBallPressureCompactInterior × ℝ ↦
      (D (z.1.1, z.2) i j + suitableProjectedHarmonicDerivative u D p t₀ z i j) ^ 2 *
        ψ (z.1.1, z.2)) (μ.prod ν) := by
    have hi := (((hW i j).mul (r := 1) (hW i j)).mul (r := 1) hΨ).integrable (by norm_num)
    exact hi.congr (ae_of_all _ fun z ↦
      congrArg (fun a ↦ a * ψ (z.1.1, z.2)) (pow_two
        (D (z.1.1, z.2) i j + suitableProjectedHarmonicDerivative u D p t₀ z i j)).symm)
  have hE : Integrable (suitableProjectedEnergyDensity u D p t₀ ψ) (μ.prod ν) := by
    have hs := integrable_finsetSum Finset.univ (fun i _ ↦ hEi i)
    convert hs using 1
    ext z
    simp only [suitableProjectedEnergyDensity, vec3EuclideanNorm,
      Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg _), Pi.add_apply,
      Finset.sum_mul]
  have hDD : Integrable (suitableProjectedDissipationDensity u D p t₀ ψ) (μ.prod ν) := by
    have hs := (integrable_finsetSum Finset.univ fun i _ ↦
      integrable_finsetSum Finset.univ fun j _ ↦ hDi i j).const_mul 2
    convert hs using 1
    ext z
    simp only [suitableProjectedDissipationDensity, projectedGradientSquare,
      Pi.add_apply, Fin.sum_univ_three]
    ring
  exact ⟨hE, hDD, hDD.sub (suitable_projected_local_energy hsol hdom hψ hnψ hsupp).1⟩

set_option maxHeartbeats 1000000 in
/-- The genuine projected inequality with every actual smooth backward ramp. -/
theorem suitable_projected_backward_cutoff_energy
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z)
    (hsupp : tsupport ψ ⊆
      unitBallPressureCompactInterior ×ˢ Ioo (t₀ - 4) (t₀ + 4))
    (t h : ℝ) (hh : 0 < h) :
    (∫ z, suitableProjectedDissipationDensity u D p t₀ ψ z * backwardTimeCutoff t h z.2
      ∂harmonicInteriorMeasure.prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) ≤
      (∫ z, suitableProjectedRhsDensity u D p t₀ ψ z * backwardTimeCutoff t h z.2
        ∂harmonicInteriorMeasure.prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) +
        ∫ z, suitableProjectedEnergyDensity u D p t₀ ψ z * deriv (backwardTimeCutoff t h) z.2
          ∂harmonicInteriorMeasure.prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) := by
  let J := Ioo (t₀ - 4) (t₀ + 4)
  let μ := harmonicInteriorMeasure
  let ν := volume.restrict J
  let χ := backwardTimeCutoff t h
  let Ψ : Vec3 × ℝ → ℝ := fun w ↦ ψ w * χ w.2
  have hχ : ContDiff ℝ ∞ χ := backwardTimeCutoff_smooth
  have hΨ := spaceTimeTestFunction_mul_smooth hψ (hχ.comp contDiff_snd)
  have hnΨ : ∀ z, 0 ≤ Ψ z := fun z ↦ mul_nonneg (hnψ z) backwardTimeCutoff_nonneg
  have hsΨ : tsupport Ψ ⊆ unitBallPressureCompactInterior ×ˢ J :=
    tsupport_mul_subset_left.trans hsupp
  have hLEI := (suitable_projected_local_energy hsol hdom hΨ hnΨ hsΨ).2
  obtain ⟨hE, hD, hR⟩ := suitable_projected_time_energy_integrable hsol hdom hψ hnψ hsupp
  have hmχ : AEStronglyMeasurable (fun z : unitBallPressureCompactInterior × ℝ ↦ χ z.2)
      (μ.prod ν) := (hχ.continuous.comp continuous_snd).aestronglyMeasurable
  have hbχ : ∀ᵐ z : unitBallPressureCompactInterior × ℝ ∂μ.prod ν, ‖χ z.2‖ ≤ 1 :=
    ae_of_all _ fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg backwardTimeCutoff_nonneg]
      exact backwardTimeCutoff_le_one
  have hmχ' : AEStronglyMeasurable
      (fun z : unitBallPressureCompactInterior × ℝ ↦ deriv χ z.2) (μ.prod ν) :=
    ((hχ.continuous_deriv (by simp)).comp continuous_snd).aestronglyMeasurable
  have hbχ' : ∀ᵐ z : unitBallPressureCompactInterior × ℝ ∂μ.prod ν,
      ‖deriv χ z.2‖ ≤ 16 / h := ae_of_all _ fun z ↦ by
    simpa only [Real.norm_eq_abs] using backwardTimeCutoff_abs_deriv_le hh
  have hDc := hD.mul_bdd hmχ hbχ
  have hRc := hR.mul_bdd hmχ hbχ
  have hEc := hE.mul_bdd hmχ' hbχ'
  have heq : (∫ z, suitableProjectedLocalEnergyDensity u D p t₀ Ψ z ∂μ.prod ν) =
      (∫ z, suitableProjectedDissipationDensity u D p t₀ ψ z * χ z.2 ∂μ.prod ν) -
        (∫ z, suitableProjectedRhsDensity u D p t₀ ψ z * χ z.2 ∂μ.prod ν) -
          ∫ z, suitableProjectedEnergyDensity u D p t₀ ψ z * deriv χ z.2 ∂μ.prod ν := by
    calc
      _ = ∫ z, ((fun z ↦ suitableProjectedDissipationDensity u D p t₀ ψ z * χ z.2) -
          (fun z ↦ suitableProjectedRhsDensity u D p t₀ ψ z * χ z.2) -
          (fun z ↦ suitableProjectedEnergyDensity u D p t₀ ψ z * deriv χ z.2)) z
            ∂μ.prod ν := by
        apply integral_congr_ae
        exact ae_of_all _ fun z ↦ by
          rw [suitableProjectedLocalEnergyDensity_mul_time u D p t₀ hψ.1 hχ]
          simp only [Pi.sub_apply, suitableProjectedRhsDensity]
          ring
      _ = _ := by rw [integral_sub' (hDc.sub hRc) hEc, integral_sub' hDc hRc]
  change (∫ z, suitableProjectedLocalEnergyDensity u D p t₀ Ψ z ∂μ.prod ν) ≤ 0 at hLEI
  rw [heq] at hLEI
  linarith

/-- The genuine projected energy and past dissipation inequality holds for almost every time. -/
theorem suitable_projected_time_energy_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z)
    (hsupp : tsupport ψ ⊆
      unitBallPressureCompactInterior ×ˢ Ioo (t₀ - 4) (t₀ + 4)) :
    ∀ᵐ t ∂volume,
      (Ioo (t₀ - 4) (t₀ + 4)).indicator
        (fun s ↦ ∫ x, suitableProjectedEnergyDensity u D p t₀ ψ (x, s)
          ∂harmonicInteriorMeasure) t +
        (∫ s in Iio t, (Ioo (t₀ - 4) (t₀ + 4)).indicator
          (fun s ↦ ∫ x, suitableProjectedDissipationDensity u D p t₀ ψ (x, s)
            ∂harmonicInteriorMeasure) s) ≤
          ∫ s in Iio t, (Ioo (t₀ - 4) (t₀ + 4)).indicator
            (fun s ↦ ∫ x, suitableProjectedRhsDensity u D p t₀ ψ (x, s)
              ∂harmonicInteriorMeasure) s := by
  obtain ⟨hE, hD, hR⟩ := suitable_projected_time_energy_integrable hsol hdom hψ hnψ hsupp
  exact tested_backwardTimeCutoff_product_energy_ae measurableSet_Ioo hE hD hR
    (suitable_projected_backward_cutoff_energy hsol hdom hψ hnψ hsupp)

end FluidSingularSets
