-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.PressureEnergyForces
public import FluidSingularSets.SliceLpMeasurable

/-!
# Genuine time integrability of suitable pressure energy forces

Joint measurable pressure supplies an actual strongly measurable spatial L²
curve after subtracting its spatial mean. The actual Stokes pressure-gradient
operator transports that curve into the energy dual. The finite 5/4 time
moment proved from suitability therefore gives the genuine Bochner L^(5/4)
class needed for the projected momentum equation.
-/

@[expose] public section

open MeasureTheory Set CKN Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance pressureForceTimeNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The genuine pressure-gradient operator as a typed real continuous linear map. -/
def stokesPressureGradientL (U : Set Vec3) :
    Lp ℝ 2 (volume.restrict U) →L[ℝ] StokesEnergyForce U :=
  -((realDualPrecompose (E := Lp ℝ 2 (volume.restrict U))
      (K := stokesGradientEnergySpace U) (stokesEnergyDivergence U)).comp
    (realHilbertRiesz (Lp ℝ 2 (volume.restrict U))))

/-- The operator acts by the actual spatial pressure gradient. -/
theorem stokesPressureGradientL_apply {U : Set Vec3}
    (p : Lp ℝ 2 (volume.restrict U)) :
    stokesPressureGradientL U p = stokesL2PressureGradient p := by
  ext v
  rfl

/-- The canonical pressure energy force is the operator applied to the actual
conditional spatial L² class, including at the exceptional slices. -/
theorem pressureEnergyForce_eq_actualSliceLp
    (p : ParabolicPoint → ℝ) (x₀ : Vec3) (r t : ℝ) :
    pressureEnergyForce p x₀ r t = stokesPressureGradientL (vec3Ball x₀ r)
      (actualSliceLp (μ := volume.restrict (vec3Ball x₀ r)) (p := 2)
        (fun w : Vec3 × ℝ ↦ centeredPressureSlice p x₀ r w.2 w.1) t) := by
  classical
  unfold pressureEnergyForce actualSliceLp
  split_ifs with h
  · exact (stokesPressureGradientL_apply _).symm
  · exact (stokesPressureGradientL _).map_zero.symm

/-- Subtracting the actual spatial mean preserves joint AE strong measurability. -/
theorem aestronglyMeasurable_centeredPressure
    {p : ParabolicPoint → ℝ} {x₀ : Vec3} {r : ℝ} {J : Set ℝ}
    (hp : AEStronglyMeasurable p (volume.restrict (vec3Ball x₀ r ×ˢ J))) :
    AEStronglyMeasurable (fun w : ParabolicPoint ↦ centeredPressureSlice p x₀ r w.2 w.1)
      (volume.restrict (vec3Ball x₀ r ×ˢ J)) := by
  let μ := (volume : Measure Vec3).restrict (vec3Ball x₀ r)
  let ν := (volume : Measure ℝ).restrict J
  have hp' : AEStronglyMeasurable (fun w : Vec3 × ℝ ↦ p w) (μ.prod ν) := by
    dsimp [μ, ν]
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hp
  have hi : AEStronglyMeasurable (fun t ↦ ∫ x, p (x, t) ∂μ) ν :=
    hp'.prod_swap.integral_prod_right'
  have hm : AEStronglyMeasurable (fun t ↦ average μ (fun x ↦ p (x, t))) ν := by
    have hh := hi.const_smul ((μ.real univ)⁻¹)
    change AEStronglyMeasurable (fun t ↦ (μ.real univ)⁻¹ • ∫ x, p (x, t) ∂μ) ν at hh
    simpa only [average_eq] using hh
  have hc := hp'.sub hm.comp_snd
  change AEStronglyMeasurable (fun w : Vec3 × ℝ ↦ centeredPressureSlice p x₀ r w.2 w.1)
    ((volume : Measure ParabolicPoint).restrict (vec3Ball x₀ r ×ˢ J))
  rw [volume_parabolicPoint_eq_prod, ← Measure.prod_restrict]
  exact hc

/-- The actual time-dependent pressure energy force is strongly measurable. -/
theorem aestronglyMeasurable_pressureEnergyForce
    {p : ParabolicPoint → ℝ} {x₀ : Vec3} {r : ℝ} {J : Set ℝ}
    (hp : AEStronglyMeasurable p (volume.restrict (vec3Ball x₀ r ×ˢ J))) :
    AEStronglyMeasurable (pressureEnergyForce p x₀ r) (volume.restrict J) := by
  have hc := aestronglyMeasurable_centeredPressure hp
  have hc' : AEStronglyMeasurable
      (fun w : Vec3 × ℝ ↦ centeredPressureSlice p x₀ r w.2 w.1)
      ((volume.restrict (vec3Ball x₀ r)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hc
  have hs := aestronglyMeasurable_actualSliceLp (p := 2) hc' (by norm_num)
  have hf := (stokesPressureGradientL (vec3Ball x₀ r)).continuous.comp_aestronglyMeasurable hs
  exact hf.congr (Eventually.of_forall (fun t ↦
    (pressureEnergyForce_eq_actualSliceLp p x₀ r t).symm))

/-- The canonical force norm is bounded by the actual centered-pressure L² norm. -/
theorem pressureEnergyForce_enorm_le
    (p : ParabolicPoint → ℝ) (x₀ : Vec3) (r t : ℝ) :
    ‖pressureEnergyForce p x₀ r t‖ₑ ≤
      ENNReal.ofReal ‖stokesEnergyDivergence (vec3Ball x₀ r)‖ *
        eLpNorm (centeredPressureSlice p x₀ r t) 2 (volume.restrict (vec3Ball x₀ r)) := by
  classical
  unfold pressureEnergyForce
  split_ifs with h
  · have hn := stokesL2PressureGradient_norm_le (h.toLp (centeredPressureSlice p x₀ r t))
    rw [Lp.norm_toLp] at hn
    have he := ENNReal.ofReal_le_ofReal hn
    rw [ENNReal.ofReal_mul (norm_nonneg (stokesEnergyDivergence (vec3Ball x₀ r))),
      ENNReal.ofReal_toReal h.eLpNorm_ne_top] at he
    rw [ofReal_norm (stokesL2PressureGradient (h.toLp (centeredPressureSlice p x₀ r t)))] at he
    exact he
  · simp

/-- A genuine finite centered-pressure time moment gives the actual Bochner
L^(5/4) class of its energy force. -/
theorem memLp_pressureEnergyForce_of_time_moment
    {p : ParabolicPoint → ℝ} {x₀ : Vec3} {r : ℝ} {J : Set ℝ}
    (hp : AEStronglyMeasurable p (volume.restrict (vec3Ball x₀ r ×ˢ J)))
    (hfin : (∫⁻ t in J, eLpNorm (centeredPressureSlice p x₀ r t) 2
      (volume.restrict (vec3Ball x₀ r)) ^ (5 / 4 : ℝ)) < ∞) :
    MemLp (pressureEnergyForce p x₀ r) (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict J) := by
  have hm := aestronglyMeasurable_pressureEnergyForce hp
  apply memLp_iff.mpr
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num)
    ENNReal.ofReal_ne_top hm, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 5 / 4)]
  let C : ℝ≥0∞ := ENNReal.ofReal ‖stokesEnergyDivergence (vec3Ball x₀ r)‖ ^ (5 / 4 : ℝ)
  have hC : C ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top).ne
  calc
    _ ≤ ∫⁻ t in J, C * (eLpNorm (centeredPressureSlice p x₀ r t) 2
        (volume.restrict (vec3Ball x₀ r)) ^ (5 / 4 : ℝ)) := by
      apply lintegral_mono
      intro t
      exact (ENNReal.rpow_le_rpow (pressureEnergyForce_enorm_le p x₀ r t)
        (by norm_num)).trans_eq (ENNReal.mul_rpow_of_nonneg _ _ (by norm_num))
    _ = C * (∫⁻ t in J, eLpNorm (centeredPressureSlice p x₀ r t) 2
        (volume.restrict (vec3Ball x₀ r)) ^ (5 / 4 : ℝ)) := lintegral_const_mul' C _ hC
    _ < ∞ := ENNReal.mul_lt_top hC.lt_top hfin

/-- Suitable weak solutions supply genuine time-integrable energy-dual pressure
gradients, with their literal test pairing and actual projection fixation. -/
theorem exists_suitable_memLp_pressure_energy_force
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r)
    (hdom : Metric.ball z (8 * r) ⊆ spaceTimeSet Ω I) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ))
        (volume.restrict (vec3Ball z.1 (2 * r) ×ˢ Ioo (z.2 - (2 * r) ^ 2) (z.2 + (2 * r) ^ 2))) ∧
      MemLp (pressureEnergyForce p z.1 r) (ENNReal.ofReal (5 / 4 : ℝ))
        (volume.restrict (Ioo (z.2 - (2 * r) ^ 2) (z.2 + (2 * r) ^ 2))) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (z.2 - (2 * r) ^ 2) (z.2 + (2 * r) ^ 2)),
        ∀ φ : StokesVectorTest (vec3Ball z.1 r),
          pressureEnergyForce p z.1 r t (stokesEnergyTest φ) =
            ∫ x in vec3Ball z.1 r, ∑ i : Fin 3, Dp (x, t) i * φ i x) ∧
      (∀ t, stokesPressureProjection (vec3Ball z.1 r) (pressureEnergyForce p z.1 r t) =
        pressureEnergyForce p z.1 r t) := by
  obtain ⟨Dp, hm, hD, hpairs, hfix, hfin⟩ := exists_suitable_pressure_energy_force hsol z hr hdom
  have hbox := CKN.Core.Endgame.localBox_of_parabolic_ball (by positivity : 0 < 2 * r)
    ((Metric.ball_subset_ball (by linarith : 2 * (2 * r) ≤ 8 * r)).trans hdom)
  have hp := hsol.toData.memLp_pressure hbox
  have hsub : vec3Ball z.1 r ⊆ vec3Ball z.1 (2 * r) := by
    intro x hx
    change vec3EuclideanNorm (x - z.1) < r at hx
    change vec3EuclideanNorm (x - z.1) < 2 * r
    exact lt_of_lt_of_le hx (by linarith)
  have hpr : AEStronglyMeasurable p (volume.restrict
      (vec3Ball z.1 r ×ˢ Ioo (z.2 - (2 * r) ^ 2) (z.2 + (2 * r) ^ 2))) :=
    hp.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume
      (Set.prod_mono hsub Subset.rfl))
  exact ⟨Dp, hm, hD, memLp_pressureEnergyForce_of_time_moment hpr hfin, hpairs, hfix⟩

end FluidSingularSets
