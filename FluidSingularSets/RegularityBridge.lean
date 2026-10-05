-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import FluidSingularSets.CKNBridge
public import CKN.Foundation.Parabolic.Doubling

/-!
# Supporting estimates for comparing regularity conventions

An essential velocity bound makes the scale-invariant cubic velocity charge
vanish. The unit-cylinder smallness criterion below transfers the actual CKN
regular-point conclusion to the local Hölder convention in the specification.
Completing the converse from essential boundedness also requires local pressure
decay and transport of the criterion to cylinders about an arbitrary point.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKNChallenge

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- A finite almost-everywhere Hölder norm supplies an actual local essential
bound, by selecting one finite-norm representative in the defining infimum. -/
theorem holder_regular_has_local_ae_bound
    {u : SpaceTime → Space} {z : SpaceTime} (hreg : IsHolderRegularPoint u z) :
    ∃ U : Set SpaceTime, IsOpen U ∧ z ∈ U ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ w ∂volume.restrict U, ‖u w‖ ≤ B := by
  obtain ⟨U, hU, hz, γ, _, _, hnorm⟩ := hreg
  unfold aeHolderNormOn at hnorm
  obtain ⟨w, hw⟩ := iInf_lt_iff.mp hnorm
  obtain ⟨hae, hwNorm⟩ := iInf_lt_iff.mp hw
  let S : ℝ≥0∞ := ⨆ x : U, ‖w x‖ₑ
  have hS : S < ∞ := lt_of_le_of_lt le_self_add hwNorm
  refine ⟨U, hU, hz, S.toReal, ENNReal.toReal_nonneg, ?_⟩
  filter_upwards [hae, ae_restrict_mem hU.measurableSet] with x hx hxU
  have hvalue : ‖w x‖ₑ ≤ S := le_iSup (fun y : U => ‖w y‖ₑ) ⟨x, hxU⟩
  have hreal := ENNReal.toReal_mono hS.ne hvalue
  rw [← hx]
  simpa only [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] using hreal

/-- Ordinary-coordinate cylinders have the same volume as raw CKN cylinders. -/
theorem volume_Q_eq_raw (r : ℝ) (z : SpaceTime) :
    volume (Q r z) = volume (CKN.Foundation.Parabolic.parabolicCylinder
      (rawToEuclidean.symm z.1) z.2 r) := by
  have h := rawSpaceTimeToEuclidean_measurePreserving.measure_preimage
    (Metric.isOpen_ball.measurableSet.prod measurableSet_Ioc).nullMeasurableSet
      (s := Q r z)
  rw [rawSpaceTime_preimage_Q] at h
  rw [volume_rawPoint_eq_product]
  exact h.symm

/-- The homogeneous dimension of three-dimensional parabolic cylinders is five. -/
theorem volume_Q_eq_unit {r : ℝ} (hr : 0 < r) (z : SpaceTime) :
    volume (Q r z) = ENNReal.ofReal (r ^ 5) * volume (Q 1) := by
  rw [volume_Q_eq_raw, volume_Q_eq_raw]
  have hs := CKN.Foundation.Parabolic.volume_parabolicCylinder_radius_scale
    (x := rawToEuclidean.symm z.1) (t := z.2) (r := 1) hr
  have ht := CKN.Foundation.Parabolic.Integration.volume_parabolicCylinder_translate
    (rawToEuclidean.symm z.1) 0 z.2 0 1
  simpa only [mul_one, add_zero, map_zero, Prod.fst_zero, Prod.snd_zero] using
    hs.trans (congrArg (ENNReal.ofReal (r ^ 5) * ·) (by simpa only [add_zero] using ht))

/-- The unit cylinder has finite ambient volume. -/
theorem volume_Q_one_lt_top : volume (Q 1) < (∞ : ℝ≥0∞) := by
  rw [volume_Q_eq_raw]
  exact CKN.Foundation.Parabolic.Integration.volume_parabolicCylinder_lt_top

/-- An almost-everywhere velocity bound controls its cubic cylinder charge. -/
theorem cubic_charge_le_of_ae_bound
    {u : SpaceTime → Space} {z : SpaceTime} {r B : ℝ}
    (hbound : ∀ᵐ w ∂volume.restrict (Q r z), ‖u w‖ ≤ B) :
    (∫⁻ w in Q r z, ‖u w‖ₑ ^ (3 : ℝ)) ≤
      ENNReal.ofReal (B ^ 3) * volume (Q r z) := by
  calc
    _ ≤ ∫⁻ _w in Q r z, ENNReal.ofReal (B ^ 3) := by
      apply lintegral_mono_ae
      filter_upwards [hbound] with w hw
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by rfl, Real.rpow_natCast]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hw 3)
    _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ]

/-- The scale-invariant cubic charge of a bounded velocity is at most a cubic
power of the radius times its bound and the fixed unit-cylinder volume. -/
theorem normalized_cubic_charge_le_of_ae_bound
    {u : SpaceTime → Space} {z : SpaceTime} {r B : ℝ}
    (hr : 0 < r) (hB : 0 ≤ B)
    (hbound : ∀ᵐ w ∂volume.restrict (Q r z), ‖u w‖ ≤ B) :
    ENNReal.ofReal (r⁻¹ ^ 2) * (∫⁻ w in Q r z, ‖u w‖ₑ ^ (3 : ℝ)) ≤
      ENNReal.ofReal (B ^ 3 * r ^ 3) * volume (Q 1) := by
  calc
    _ ≤ ENNReal.ofReal (r⁻¹ ^ 2) *
        (ENNReal.ofReal (B ^ 3) * volume (Q r z)) :=
      mul_le_mul le_rfl (cubic_charge_le_of_ae_bound hbound) (by positivity) (by positivity)
    _ = ENNReal.ofReal (r⁻¹ ^ 2 * (B ^ 3 * r ^ 5)) * volume (Q 1) := by
      rw [volume_Q_eq_unit hr, ← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul (sq_nonneg _),
        ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (pow_nonneg hB 3))]
      congr 2
      ring
    _ = _ := by
      congr 2
      field_simp

/-- A fixed essential bound on all sufficiently small cylinders forces the
normalized cubic velocity charge to vanish at their center. -/
theorem tendsto_normalized_cubic_charge_of_ae_bound
    {u : SpaceTime → Space} {z : SpaceTime} {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ᵐ w ∂volume.restrict (Q r z), ‖u w‖ ≤ B) :
    Tendsto (fun r : ℝ => ENNReal.ofReal (r⁻¹ ^ 2) *
      (∫⁻ w in Q r z, ‖u w‖ₑ ^ (3 : ℝ))) (𝓝[>] 0) (𝓝 0) := by
  have hmajor : Tendsto (fun r : ℝ => ENNReal.ofReal (B ^ 3 * r ^ 3) *
      volume (Q 1)) (𝓝[>] 0) (𝓝 0) := by
    have hreal : Tendsto (fun r : ℝ => B ^ 3 * r ^ 3) (𝓝[>] 0) (𝓝 0) := by
      have hid : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
        (continuous_id.tendsto 0).mono_left inf_le_left
      simpa using tendsto_const_nhds.mul (hid.pow 3)
    simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hreal)
      (Or.inr volume_Q_one_lt_top.ne)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [self_mem_nhdsWithin, hbound] with r hr hbr
  exact normalized_cubic_charge_le_of_ae_bound hr hB hbr

/-- Actual suitability and the CKN small-data criterion imply Hölder regularity
at every point in the open half cylinder, in ordinary coordinates. -/
theorem epsilon_cubic_charge_implies_holder_regular
    (q : ℝ≥0) (hq : 5 / 2 < (q : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (Ω : Set Space) (I : Set ℝ) (sol : LocalWeakNSESolution Ω I q),
        closure (Q 1) ⊆ Ω ×ˢ I →
        (∫⁻ w in Q 1, ‖sol.u w‖ₑ ^ (3 : ℝ) +
          ‖sol.p w‖ₑ ^ (3 / 2 : ℝ) + ‖sol.f w‖ₑ ^ (q : ℝ)) ≤
            ENNReal.ofReal ε →
        ∀ z ∈ Metric.ball (0 : Space) (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
          IsHolderRegularPoint sol.u z := by
  obtain ⟨ε, γ, C, hε, _, _, _, hreg⟩ := CKN.epsilonRegularityL3 (q : ℝ) hq
  refine ⟨ε, hε, ?_⟩
  intro Ω I sol hdomain hsmall z hz
  have hdomainRaw : closure (CKN.Foundation.Parabolic.parabolicCylinder 0 0 1) ⊆
      CKN.spaceTimeSet (rawSpace Ω) I := by
    intro w hw
    have he := (mem_closure_cylinder_iff_mem_closure_Q one_pos
      ((0 : RawSpace), 0) w).mp hw
    have hd := hdomain (by simpa only [map_zero, Prod.zero_eq_mk] using he)
    exact hd
  have hsmallRaw := (smallness_integral_transport sol).trans_le hsmall
  obtain ⟨w, _, _, hpoints⟩ := hreg (rawSpace Ω) I (pullVelocity sol.u)
    (pullGradient sol.Dxu) (pullScalar sol.p) (pullVelocity sol.f)
    (rawSuitableWeakSolution hq sol) hdomainRaw hsmallRaw
  let zr : RawPoint := rawSpaceTimeToEuclidean.symm z
  have hzRaw : zr ∈ CKN.Foundation.Parabolic.vec3Ball 0 (1 / 2) ×ˢ
      Ioo (-(1 / 4 : ℝ)) 0 := by
    constructor
    · change CKN.Foundation.Parabolic.vec3EuclideanNorm (zr.1 - 0) < 1 / 2
      change CKN.Foundation.Parabolic.vec3EuclideanNorm
        (rawToEuclidean.symm z.1 - 0) < 1 / 2
      simpa only [sub_zero, vec3EuclideanNorm_rawToEuclidean_symm,
        Metric.mem_ball, dist_zero_right] using hz.1
    · exact hz.2
  have hout := isHolderRegularPoint_of_rawRegular (hpoints zr hzRaw)
  have he : parabolicToEuclideanHomeomorph zr = z := by
    exact rawSpaceTimeToEuclidean.apply_symm_apply z
  exact he ▸ hout

end FluidSingularSets
