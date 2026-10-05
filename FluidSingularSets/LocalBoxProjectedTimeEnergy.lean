-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.LocalBoxProjectedLocalEnergy
public import FluidSingularSets.TestedTimeEnergy

/-!
# Original-interval projected energy at almost every time

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
def localBoxProjectedEnergyDensity
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ)
    (z : unitBallPressureCompactInterior × ℝ) : ℝ :=
  vec3EuclideanNorm (u (z.1.1, z.2) +
    localBoxProjectedHarmonicGradient u D p a b c z) ^ 2 * ψ (z.1.1, z.2)

/-- The literal tested corrected gradient dissipation, with its true coefficient two. -/
def localBoxProjectedDissipationDensity
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ)
    (z : unitBallPressureCompactInterior × ℝ) : ℝ :=
  2 * projectedGradientSquare
    (D (z.1.1, z.2) + localBoxProjectedHarmonicDerivative u D p a b c z) * ψ (z.1.1, z.2)

/-- The actual projected right hand side, obtained from the literal deficit. -/
def localBoxProjectedRhsDensity
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ)
    (z : unitBallPressureCompactInterior × ℝ) : ℝ :=
  localBoxProjectedDissipationDensity u D p a b c ψ z -
    localBoxProjectedLocalEnergyDensity u D p a b c ψ z

/-- The actual scalar smooth time multiplier has precisely the energy derivative term. -/
theorem localBoxProjectedLocalEnergyDensity_mul_time
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {ψ : Vec3 × ℝ → ℝ} {χ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (z : unitBallPressureCompactInterior × ℝ) :
    localBoxProjectedLocalEnergyDensity u D p a b c (fun w ↦ ψ w * χ w.2) z =
      localBoxProjectedLocalEnergyDensity u D p a b c ψ z * χ z.2 -
        localBoxProjectedEnergyDensity u D p a b c ψ z * deriv χ z.2 := by
  let U : Vec3 := u ((z.1.1, z.2) : ParabolicPoint)
  let H := localBoxProjectedHarmonicGradient u D p a b c z
  let W := D ((z.1.1, z.2) : ParabolicPoint)
  let B := localBoxProjectedHarmonicDerivative u D p a b c z
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
theorem localBoxProjectedEnergyDensity_nonneg
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {ψ : Vec3 × ℝ → ℝ}
    (hψ : ∀ z, 0 ≤ ψ z) (z : unitBallPressureCompactInterior × ℝ) :
    0 ≤ localBoxProjectedEnergyDensity u D p a b c ψ z :=
  mul_nonneg (sq_nonneg _) (hψ (z.1.1, z.2))

/-- The literal corrected gradient dissipation is nonnegative at every point. -/
theorem localBoxProjectedDissipationDensity_nonneg
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {ψ : Vec3 × ℝ → ℝ}
    (hψ : ∀ z, 0 ≤ ψ z) (z : unitBallPressureCompactInterior × ℝ) :
    0 ≤ localBoxProjectedDissipationDensity u D p a b c ψ z :=
  mul_nonneg (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
      (hψ (z.1.1, z.2))

variable {Ω : Set Vec3} {I : Set ℝ} {q a b c : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

set_option maxHeartbeats 1000000 in
/-- Every literal density used in time extraction is integrable directly from suitability. -/
theorem suitable_projected_time_energy_integrable_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z)
    (hsupp : tsupport ψ ⊆
      unitBallPressureCompactInterior ×ˢ Ioo a b) :
    Integrable (localBoxProjectedEnergyDensity u D p a b c ψ)
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo a b))) ∧
      Integrable (localBoxProjectedDissipationDensity u D p a b c ψ)
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo a b))) ∧
      Integrable (localBoxProjectedRhsDensity u D p a b c ψ)
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo a b))) := by
  let J := Ioo a b
  let μ := harmonicInteriorMeasure
  let ν := volume.restrict J
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
    ((measure_mono Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne
  let : ENNReal.HolderTriple 2 2 1 := by
    have h : Real.HolderTriple 2 2 1 := by constructor <;> norm_num
    simpa using h.ennrealOfReal
  obtain ⟨hU, hD, _hp⟩ := localBox_harmonicInterior_memLp hsol hbox hab
  obtain ⟨hH, hB⟩ := localBox_harmonicInterior_correction_memLp_top hsol hbox hab hc
  have hΨ : MemLp (fun z : unitBallPressureCompactInterior × ℝ ↦ ψ (z.1.1, z.2)) ⊤
      (μ.prod ν) := by
    obtain ⟨C, hC⟩ := exists_bound_of_mem_spaceTimeTestFunction hψ
    exact MemLp.of_bound
      (hψ.1.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        continuous_snd)).aestronglyMeasurable C (ae_of_all _ fun z ↦ hC (z.1.1, z.2))
  have hV (i : Fin 3) : MemLp (fun z : unitBallPressureCompactInterior × ℝ ↦
      u (z.1.1, z.2) i + localBoxProjectedHarmonicGradient u D p a b c z i) 2 (μ.prod ν) :=
    ((memLp_pi_iff.mp hU i).mono_exponent (by norm_num)).add
      ((memLp_pi_iff.mp hH i).mono_exponent le_top)
  have hW (i j : Fin 3) : MemLp (fun z : unitBallPressureCompactInterior × ℝ ↦
      D (z.1.1, z.2) i j + localBoxProjectedHarmonicDerivative u D p a b c z i j)
      2 (μ.prod ν) :=
    (memLp_pi_iff.mp (memLp_pi_iff.mp hD i) j).add ((hB i j).mono_exponent le_top)
  have hEi (i : Fin 3) : Integrable (fun z : unitBallPressureCompactInterior × ℝ ↦
      (u (z.1.1, z.2) i + localBoxProjectedHarmonicGradient u D p a b c z i) ^ 2 *
        ψ (z.1.1, z.2)) (μ.prod ν) := by
    have hi := (((hV i).mul (r := 1) (hV i)).mul (r := 1) hΨ).integrable (by norm_num)
    exact hi.congr (ae_of_all _ fun z ↦
      congrArg (fun a ↦ a * ψ (z.1.1, z.2)) (pow_two
        (u (z.1.1, z.2) i + localBoxProjectedHarmonicGradient u D p a b c z i)).symm)
  have hDi (i j : Fin 3) : Integrable (fun z : unitBallPressureCompactInterior × ℝ ↦
      (D (z.1.1, z.2) i j + localBoxProjectedHarmonicDerivative u D p a b c z i j) ^ 2 *
        ψ (z.1.1, z.2)) (μ.prod ν) := by
    have hi := (((hW i j).mul (r := 1) (hW i j)).mul (r := 1) hΨ).integrable (by norm_num)
    exact hi.congr (ae_of_all _ fun z ↦
      congrArg (fun a ↦ a * ψ (z.1.1, z.2)) (pow_two
        (D (z.1.1, z.2) i j + localBoxProjectedHarmonicDerivative u D p a b c z i j)).symm)
  have hE : Integrable (localBoxProjectedEnergyDensity u D p a b c ψ) (μ.prod ν) := by
    have hs := integrable_finsetSum Finset.univ (fun i _ ↦ hEi i)
    convert hs using 1
    ext z
    simp only [localBoxProjectedEnergyDensity, vec3EuclideanNorm,
      Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg _), Pi.add_apply,
      Finset.sum_mul]
  have hDD : Integrable (localBoxProjectedDissipationDensity u D p a b c ψ) (μ.prod ν) := by
    have hs := (integrable_finsetSum Finset.univ fun i _ ↦
      integrable_finsetSum Finset.univ fun j _ ↦ hDi i j).const_mul 2
    convert hs using 1
    ext z
    simp only [localBoxProjectedDissipationDensity, projectedGradientSquare,
      Pi.add_apply, Fin.sum_univ_three]
    ring
  exact ⟨hE, hDD, hDD.sub
    (suitable_projected_local_energy_localBox hsol hbox hab hc hψ hnψ hsupp).1⟩

set_option maxHeartbeats 1000000 in
/-- The genuine projected inequality with every actual smooth backward ramp. -/
theorem suitable_projected_backward_cutoff_energy_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z)
    (hsupp : tsupport ψ ⊆
      unitBallPressureCompactInterior ×ˢ Ioo a b)
    (t h : ℝ) (hh : 0 < h) :
    (∫ z, localBoxProjectedDissipationDensity u D p a b c ψ z * backwardTimeCutoff t h z.2
      ∂harmonicInteriorMeasure.prod (volume.restrict (Ioo a b))) ≤
      (∫ z, localBoxProjectedRhsDensity u D p a b c ψ z * backwardTimeCutoff t h z.2
        ∂harmonicInteriorMeasure.prod (volume.restrict (Ioo a b))) +
        ∫ z, localBoxProjectedEnergyDensity u D p a b c ψ z *
          deriv (backwardTimeCutoff t h) z.2
          ∂harmonicInteriorMeasure.prod (volume.restrict (Ioo a b)) := by
  let J := Ioo a b
  let μ := harmonicInteriorMeasure
  let ν := volume.restrict J
  let χ := backwardTimeCutoff t h
  let Ψ : Vec3 × ℝ → ℝ := fun w ↦ ψ w * χ w.2
  have hχ : ContDiff ℝ ∞ χ := backwardTimeCutoff_smooth
  have hΨ := spaceTimeTestFunction_mul_smooth hψ (hχ.comp contDiff_snd)
  have hnΨ : ∀ z, 0 ≤ Ψ z := fun z ↦ mul_nonneg (hnψ z) backwardTimeCutoff_nonneg
  have hsΨ : tsupport Ψ ⊆ unitBallPressureCompactInterior ×ˢ J :=
    tsupport_mul_subset_left.trans hsupp
  have hLEI := (suitable_projected_local_energy_localBox hsol hbox hab hc hΨ hnΨ hsΨ).2
  obtain ⟨hE, hD, hR⟩ :=
    suitable_projected_time_energy_integrable_localBox hsol hbox hab hc hψ hnψ hsupp
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
  have heq : (∫ z, localBoxProjectedLocalEnergyDensity u D p a b c Ψ z ∂μ.prod ν) =
      (∫ z, localBoxProjectedDissipationDensity u D p a b c ψ z * χ z.2 ∂μ.prod ν) -
        (∫ z, localBoxProjectedRhsDensity u D p a b c ψ z * χ z.2 ∂μ.prod ν) -
          ∫ z, localBoxProjectedEnergyDensity u D p a b c ψ z * deriv χ z.2 ∂μ.prod ν := by
    calc
      _ = ∫ z, ((fun z ↦ localBoxProjectedDissipationDensity u D p a b c ψ z * χ z.2) -
          (fun z ↦ localBoxProjectedRhsDensity u D p a b c ψ z * χ z.2) -
          (fun z ↦ localBoxProjectedEnergyDensity u D p a b c ψ z * deriv χ z.2)) z
            ∂μ.prod ν := by
        apply integral_congr_ae
        exact ae_of_all _ fun z ↦ by
          rw [localBoxProjectedLocalEnergyDensity_mul_time u D p a b c hψ.1 hχ]
          simp only [Pi.sub_apply, localBoxProjectedRhsDensity]
          ring
      _ = _ := by rw [integral_sub' (hDc.sub hRc) hEc, integral_sub' hDc hRc]
  change (∫ z, localBoxProjectedLocalEnergyDensity u D p a b c Ψ z ∂μ.prod ν) ≤ 0 at hLEI
  rw [heq] at hLEI
  linarith

/-- The genuine projected energy and past dissipation inequality holds for almost every time. -/
theorem suitable_projected_time_energy_ae_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z)
    (hsupp : tsupport ψ ⊆
      unitBallPressureCompactInterior ×ˢ Ioo a b) :
    ∀ᵐ t ∂volume,
      (Ioo a b).indicator
        (fun s ↦ ∫ x, localBoxProjectedEnergyDensity u D p a b c ψ (x, s)
          ∂harmonicInteriorMeasure) t +
        (∫ s in Iio t, (Ioo a b).indicator
          (fun s ↦ ∫ x, localBoxProjectedDissipationDensity u D p a b c ψ (x, s)
            ∂harmonicInteriorMeasure) s) ≤
          ∫ s in Iio t, (Ioo a b).indicator
            (fun s ↦ ∫ x, localBoxProjectedRhsDensity u D p a b c ψ (x, s)
              ∂harmonicInteriorMeasure) s := by
  obtain ⟨hE, hD, hR⟩ :=
    suitable_projected_time_energy_integrable_localBox hsol hbox hab hc hψ hnψ hsupp
  exact tested_backwardTimeCutoff_product_energy_ae measurableSet_Ioo hE hD hR
    (suitable_projected_backward_cutoff_energy_localBox hsol hbox hab hc hψ hnψ hsupp)

end FluidSingularSets
