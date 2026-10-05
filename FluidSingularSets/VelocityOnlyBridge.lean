-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.MixedVelocityDecay

/-!
# Pressure decay with a short velocity time window

The genuine pressure decay of the CKN library holds at almost every time.
Keeping its velocity source on a short time interval is stronger than enlarging
both source terms to the outer cylinder. For bounded velocity this distinction
allows the normalized pressure charge to vanish at small scales.

The pressure estimate reuses the results of Scott Armstrong and Vlad Vicol in
the CKN library, distributed under the Apache 2.0 license.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- An essential Euclidean bound also bounds the actual spatial mean. -/
theorem euclideanMean_le_of_ae_bound {x₀ : Vec3} {ρ B : ℝ} (hρ : 0 < ρ)
    {u : Vec3 → Vec3} (hu : IntegrableOn u (vec3Ball x₀ ρ) volume)
    (hbound : ∀ᵐ x ∂volume.restrict (vec3Ball x₀ ρ), vec3EuclideanNorm (u x) ≤ B) :
    vec3EuclideanNorm (average (volume.restrict (vec3Ball x₀ ρ)) u) ≤ B := by
  let L := (PiLp.continuousLinearEquiv (2 : ℝ≥0∞) ℝ
    (fun _ : Fin 3 ↦ ℝ)).symm
  have hLint : IntegrableOn (fun x ↦ L (u x)) (vec3Ball x₀ ρ) volume :=
    L.toContinuousLinearMap.integrable_comp hu
  have hmap : L (average (volume.restrict (vec3Ball x₀ ρ)) u) =
      average (volume.restrict (vec3Ball x₀ ρ)) (fun x ↦ L (u x)) := by
    rw [average_eq, average_eq, map_smul, L.integral_comp_comm]
  have hnorm : ‖average (volume.restrict (vec3Ball x₀ ρ)) (fun x ↦ L (u x))‖ ≤ B := by
    apply (setAverage_norm_le volume (vec3Ball x₀ ρ) (fun x ↦ L (u x))).trans
    have h := setAverage_mono_of_ae (g := fun _ ↦ B) hLint.norm
      (integrableOn_const (C := B) (volume_vec3Ball_lt_top.ne)) (by
        change ∀ᵐ x ∂volume.restrict (vec3Ball x₀ ρ), ‖L (u x)‖ ≤ B
        simpa only [vec3EuclideanNorm_eq_l2,
          show (L : Vec3 → L2Vec3) = WithLp.toLp 2 by rfl] using hbound)
    simpa only [setAverage_const (volume_vec3Ball_pos hρ).ne'
      volume_vec3Ball_lt_top.ne] using h
  rw [← hmap] at hnorm
  simpa only [vec3EuclideanNorm_eq_l2,
    show (L : Vec3 → L2Vec3) = WithLp.toLp 2 by rfl] using hnorm

/-- The mean-free cubic source of pressure is bounded by eight times the cube
of an essential velocity bound, with the exact spatial volume factor. -/
theorem lin34VelocitySlice_le_of_ae_bound {u : ParabolicPoint → Vec3}
    {z : ParabolicPoint} {ρ s B : ℝ} (hρ : 0 < ρ) (hB : 0 ≤ B)
    (hu : IntegrableOn (fun x ↦ u (x, s)) (vec3Ball z.1 ρ) volume)
    (hbound : ∀ᵐ x ∂volume.restrict (vec3Ball z.1 ρ),
      vec3EuclideanNorm (u (x, s)) ≤ B) :
    lin34VelocitySlice u z ρ s ≤ (2 * B) ^ 3 * (volume (vec3Ball z.1 ρ)).toReal := by
  let : IsFiniteMeasure (volume.restrict (vec3Ball z.1 ρ)) :=
    isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  have hmean := euclideanMean_le_of_ae_bound hρ hu hbound
  have heq := meanFreeVec_eq_sub_spatialAverage hu
  have hpoint : ∀ᵐ x ∂volume.restrict (vec3Ball z.1 ρ),
      vec3EuclideanNorm (meanFreeVec u z.1 ρ s x) ≤ 2 * B := by
    filter_upwards [hbound] with x hx
    change vec3EuclideanNorm ((fun y ↦ meanFreeVec u z.1 ρ s y) x) ≤ 2 * B
    rw [heq]
    exact (vec3EuclideanNorm_sub_le _ _).trans (by linarith only [hx, hmean])
  have hmeas : AEStronglyMeasurable (fun x ↦
      vec3EuclideanNorm (meanFreeVec u z.1 ρ s x) ^ (3 : ℕ))
      (volume.restrict (vec3Ball z.1 ρ)) := by
    have hbase := (CKN.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      (hu.aestronglyMeasurable.sub (aestronglyMeasurable_const
        (b := average (volume.restrict (vec3Ball z.1 ρ)) (fun y ↦ u (y, s)))))).pow 3
    exact (aestronglyMeasurable_congr (Eventually.of_forall fun x ↦
      congrArg (fun a ↦ vec3EuclideanNorm a ^ (3 : ℕ)) (congrFun heq x))).2 hbase
  have hconst : Integrable (fun _ : Vec3 ↦ (2 * B) ^ 3)
      (volume.restrict (vec3Ball z.1 ρ)) := integrable_const _
  have hint : Integrable (fun x ↦
      vec3EuclideanNorm (meanFreeVec u z.1 ρ s x) ^ (3 : ℕ))
      (volume.restrict (vec3Ball z.1 ρ)) := by
    apply hconst.mono hmeas
    filter_upwards [hpoint] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (vec3EuclideanNorm_nonneg _) _),
      abs_of_nonneg (pow_nonneg (mul_nonneg (by norm_num) hB) _)]
    exact pow_le_pow_left₀ (vec3EuclideanNorm_nonneg _) hx 3
  have hle := integral_mono_ae hint hconst (by
    filter_upwards [hpoint] with x hx
    exact pow_le_pow_left₀ (vec3EuclideanNorm_nonneg _) hx 3)
  simpa only [lin34VelocitySlice, integral_const, smul_eq_mul,
    measureReal_def, Measure.restrict_apply_univ, mul_comm] using hle

/-- Only the harmonic pressure source needs the full outer time interval.
The velocity source stays on the requested inner interval. -/
theorem suitablePressureTimeWindowDecay_keep_velocity
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    {J : Set ℝ} (hJ : J ⊆ Ioc (z.2 - ρ ^ 2) z.2) :
    (∫ s in J, r⁻¹ ^ 2 * ∫ x in vec3Ball z.1 r,
        |p (x, s)| ^ (3 / 2 : ℝ)) ≤
      lin34AbsoluteConstant * ((ρ / r) ^ 2 * (∫ s in J, lin34G u z ρ s) +
        (r / ρ) * pressureD p z ρ) := by
  let T := Ioc (z.2 - ρ ^ 2) z.2
  let F := fun s ↦ r⁻¹ ^ 2 * ∫ x in vec3Ball z.1 r, |p (x, s)| ^ (3 / 2 : ℝ)
  let H := fun s ↦ lin34AbsoluteConstant *
    ((ρ / r) ^ 2 * lin34G u z ρ s + (r / ρ) * lin34H p z ρ s)
  have hrρ : r ≤ ρ := by linarith only [hhalf, hρ]
  have hp := lin34_integrableOn_pressure_pow_cylinder hsol hρ hsub
  have hprod : Integrable (fun w ↦ |p w| ^ (3 / 2 : ℝ))
      ((volume.restrict (vec3Ball z.1 ρ)).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict]
    exact hp
  have hsmallprod : Integrable (fun w ↦ |p w| ^ (3 / 2 : ℝ))
      ((volume.restrict (vec3Ball z.1 r)).prod (volume.restrict T)) := by
    apply hprod.mono_measure
    exact Measure.prod_mono
      (Measure.restrict_mono (vec3Ball_mono hrρ) le_rfl) le_rfl
  have hF : Integrable F (volume.restrict T) := hsmallprod.integral_prod_right.const_mul _
  have hG := lin34G_integrable hsol hρ hsub
  have hHp := lin34H_integrable hsol hρ hsub
  have hH : Integrable H (volume.restrict T) :=
    ((hG.const_mul _).add (hHp.const_mul _)).const_mul _
  have hforce : ∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun w ↦ ∑ i : Fin 3, (0 : Vec3) i * spatialPartial ψ i w)
          (tsupport ψ) volume ∧
        (∫ w in spaceTimeSet Ω I, ∑ i : Fin 3, (0 : Vec3) i * spatialPartial ψ i w) = 0 :=
    by intro ψ hψ; simp
  have hpoint := ((CKN.pressure_lin34_of_sws q hsol hρ hr hhalf hsub).1 hforce).1
  have hC : 0 ≤ lin34AbsoluteConstant :=
    (lin34PointwiseConstant_nonneg lin34CZConstant_nonneg).trans (le_max_left _ _)
  have hpressure : ∫ s in J, lin34H p z ρ s ≤ pressureD p z ρ := by
    rw [lin34_pressureD_eq_integral hsol hρ hsub]
    apply setIntegral_mono_set hHp
    · exact Eventually.of_forall fun s ↦ mul_nonneg (sq_nonneg _)
        (integral_nonneg fun _ ↦ by positivity)
    · exact Eventually.of_forall fun s hs ↦ hJ hs
  calc
    _ ≤ ∫ s in J, H s := integral_mono_ae (hF.mono_measure
        (Measure.restrict_mono hJ le_rfl))
      (hH.mono_measure (Measure.restrict_mono hJ le_rfl))
      (ae_restrict_of_ae_restrict_of_subset hJ hpoint)
    _ = lin34AbsoluteConstant * ((ρ / r) ^ 2 * (∫ s in J, lin34G u z ρ s) +
        (r / ρ) * (∫ s in J, lin34H p z ρ s)) := by
      dsimp [H]
      rw [integral_const_mul, integral_add
        ((hG.mono_measure (Measure.restrict_mono hJ le_rfl)).const_mul _)
        ((hHp.mono_measure (Measure.restrict_mono hJ le_rfl)).const_mul _),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_left hpressure
        (div_nonneg hr.le hρ.le)) _) hC

/-- Essential boundedness of an actual suitable solution gives a pressure
bound whose velocity term is independent of the inner radius. -/
theorem suitablePressureDecay_of_ae_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {ρ r B : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2) (hB : 0 ≤ B)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hbound : ∀ᵐ w ∂volume.restrict (parabolicCylinder z.1 z.2 ρ),
      vec3EuclideanNorm (u w) ≤ B) :
    pressureD p z r ≤ lin34AbsoluteConstant *
      ((2 * B) ^ 3 * (volume (vec3Ball z.1 ρ)).toReal + (r / ρ) * pressureD p z ρ) := by
  let T := Ioc (z.2 - ρ ^ 2) z.2
  let J := Ioc (z.2 - r ^ 2) z.2
  let μ := volume.restrict (vec3Ball z.1 ρ)
  let ν := volume.restrict T
  have hrρ : r ≤ ρ := by linarith only [hhalf, hρ]
  have hJ : J ⊆ T := Ioc_subset_Ioc_left (lin34_time_subset hr hrρ)
  have hu : Integrable u (μ.prod ν) := by
    rw [Measure.prod_restrict]
    exact tsai_integrable_velocity_on_cylinder hsol hρ hsub
  have hboundprod : ∀ᵐ w ∂μ.prod ν, vec3EuclideanNorm (u w) ≤ B := by
    rw [Measure.prod_restrict]
    exact hbound
  have hslices : ∀ᵐ s ∂ν, ∀ᵐ x ∂μ, vec3EuclideanNorm (u (x, s)) ≤ B :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae
        hboundprod)
  have hGbound : ∀ᵐ s ∂ν, lin34G u z ρ s ≤
      ρ⁻¹ ^ 2 * ((2 * B) ^ 3 * (volume (vec3Ball z.1 ρ)).toReal) := by
    filter_upwards [hu.prod_left_ae, hslices] with s hus hbs
    exact mul_le_mul_of_nonneg_left
      (lin34VelocitySlice_le_of_ae_bound hρ hB hus hbs) (sq_nonneg _)
  have hG := lin34G_integrable hsol hρ hsub
  have htime : (volume J).toReal = r ^ 2 := by
    dsimp [J]
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by nlinarith [sq_nonneg r])]
    ring
  have hGint : ∫ s in J, lin34G u z ρ s ≤
      r ^ 2 * (ρ⁻¹ ^ 2 * ((2 * B) ^ 3 * (volume (vec3Ball z.1 ρ)).toReal)) := by
    have hle := integral_mono_ae (hG.mono_measure (Measure.restrict_mono hJ le_rfl))
      (integrable_const _) (ae_restrict_of_ae_restrict_of_subset hJ hGbound)
    simpa only [integral_const, smul_eq_mul, measureReal_def,
      Measure.restrict_apply_univ, htime] using hle
  have hsubr := (closure_parabolicCylinder_mono hr.le hrρ).trans hsub
  have hD := pressureD_eq_time_slice_integral
    (lin34_integrableOn_pressure_pow_cylinder hsol hr hsubr)
  have hdecay := suitablePressureTimeWindowDecay_keep_velocity hsol hρ hr hhalf hsub hJ
  have hC : 0 ≤ lin34AbsoluteConstant :=
    (lin34PointwiseConstant_nonneg lin34CZConstant_nonneg).trans (le_max_left _ _)
  calc
    pressureD p z r = ∫ s in J, r⁻¹ ^ 2 * ∫ x in vec3Ball z.1 r,
        |p (x, s)| ^ (3 / 2 : ℝ) := hD
    _ ≤ _ := hdecay
    _ ≤ lin34AbsoluteConstant *
        ((ρ / r) ^ 2 * (r ^ 2 * (ρ⁻¹ ^ 2 *
          ((2 * B) ^ 3 * (volume (vec3Ball z.1 ρ)).toReal))) +
            (r / ρ) * pressureD p z ρ) := mul_le_mul_of_nonneg_left
      (add_le_add_left (mul_le_mul_of_nonneg_left hGint (sq_nonneg _)) _) hC
    _ = _ := by
      congr 1
      congr 1
      field_simp [hρ.ne', hr.ne']

/-- The real spatial volume tends to zero with the third power of the radius. -/
theorem tendsto_real_volume_vec3Ball (x : Vec3) :
    Tendsto (fun r : ℝ ↦ (volume (vec3Ball x r)).toReal)
      (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun r : ℝ ↦ r) (𝓝[>] 0) (𝓝 0) :=
    (continuous_id.tendsto 0).mono_left inf_le_left
  have h := (hid.pow 3).mul_const (Real.pi * 4 / 3)
  simp only [zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [volume_vec3Ball_eq, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal (by positivity)]

/-- For an actually suitable unforced solution, local essential boundedness
forces the normalized pressure charge to vanish. No pressure smallness or
regularity estimate is a hypothesis. -/
theorem tendsto_pressureD_of_ae_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hsub : closure (parabolicCylinder z.1 z.2 R) ⊆ spaceTimeSet Ω I)
    (hbound : ∀ᵐ w ∂volume.restrict (parabolicCylinder z.1 z.2 R),
      vec3EuclideanNorm (u w) ≤ B) :
    Tendsto (pressureD p z) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hlimit : Tendsto (fun ρ : ℝ ↦ lin34AbsoluteConstant *
      ((2 * B) ^ 3 * (volume (vec3Ball z.1 ρ)).toReal)) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_real_volume_vec3Ball z.1).const_mul
      (lin34AbsoluteConstant * (2 * B) ^ 3)
    simp only [mul_zero] at h
    convert h using 1
    funext ρ
    ring
  have hsmall : ∀ᶠ ρ : ℝ in 𝓝[>] 0,
      lin34AbsoluteConstant * ((2 * B) ^ 3 *
        (volume (vec3Ball z.1 ρ)).toReal) < ε / 2 :=
    (tendsto_order.1 hlimit).2 _ (by positivity)
  have houter : ∀ᶠ ρ : ℝ in 𝓝[>] 0, ρ < R :=
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds
  have hpositive : ∀ᶠ ρ : ℝ in 𝓝[>] 0, 0 < ρ := self_mem_nhdsWithin
  obtain ⟨ρ, hρ, hρR, hsmallρ⟩ := (hpositive.and (houter.and hsmall)).exists
  have hsubρ := (closure_parabolicCylinder_mono hρ.le hρR.le).trans hsub
  have hboundρ := ae_restrict_of_ae_restrict_of_subset
    (parabolicCylinder_mono hρ.le hρR.le) hbound
  have herror : Tendsto (fun r : ℝ ↦
      lin34AbsoluteConstant * ((r / ρ) * pressureD p z ρ)) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun r : ℝ ↦ r) (𝓝[>] 0) (𝓝 0) :=
      (continuous_id.tendsto 0).mono_left inf_le_left
    simpa only [zero_div, zero_mul, mul_zero] using
      ((hid.div_const ρ).mul_const (pressureD p z ρ)).const_mul lin34AbsoluteConstant
  have herrorSmall : ∀ᶠ r : ℝ in 𝓝[>] 0,
      lin34AbsoluteConstant * ((r / ρ) * pressureD p z ρ) < ε / 2 :=
    (tendsto_order.1 herror).2 _ (by positivity)
  have hinner : ∀ᶠ r : ℝ in 𝓝[>] 0, r < ρ / 2 :=
    (eventually_lt_nhds (by positivity : (0 : ℝ) < ρ / 2)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hinner, herrorSmall] with r hr hrρ herr
  have hdecay := suitablePressureDecay_of_ae_bound hsol hρ hr hrρ.le hB hsubρ hboundρ
  have hnonneg : 0 ≤ pressureD p z r := by
    exact mul_nonneg (sq_nonneg _) (integral_nonneg fun _ ↦ by positivity)
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [mul_add] at hdecay
  linarith only [hdecay, hsmallρ, herr]

end FluidSingularSets
