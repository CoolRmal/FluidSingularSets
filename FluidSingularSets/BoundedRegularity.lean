-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.VelocityOnlyBridge
public import FluidSingularSets.CKNBridge
public import FluidSingularSets.RegularityBridge
public import CKN.Core.Endgame.StartCaccioppoli
public import CKN.Setting.ScalingQuantityNonneg

/-!
# Essential boundedness implies the specified regularity

An essential bound makes the cubic velocity charge vanish. Actual suitable
solutions also have vanishing normalized pressure by the time-window estimate.
The solution-level Caccioppoli inequality then makes the normalized gradient
charge vanish, so CKN epsilon regularity supplies a Hölder representative.

The solution-level analytic inputs are the proved CKN results of Scott Armstrong
and Vlad Vicol, distributed under the Apache 2.0 license.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The cubic velocity quantity has the exact small spatial-volume bound. -/
theorem gamma_cube_le_of_ae_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r B : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I)
    (hbound : ∀ᵐ w ∂volume.restrict (parabolicCylinder z.1 z.2 r),
      vec3EuclideanNorm (u w) ≤ B) :
    gamma u z r ^ 3 ≤ B ^ 3 * (volume (vec3Ball z.1 r)).toReal := by
  let : IsFiniteMeasure (volume.restrict (parabolicCylinder z.1 z.2 r)) :=
    isFiniteMeasure_restrict.mpr volume_parabolicCylinder_lt_top.ne
  have hint := tsai_integrable_velocity_cube_on_cylinder hsol hr hsub
  have hmass : ∫ w in parabolicCylinder z.1 z.2 r,
      vec3EuclideanNorm (u w) ^ (3 : ℕ) ≤
        (volume (parabolicCylinder z.1 z.2 r)).toReal * B ^ 3 := by
    have h := integral_mono_ae hint (integrable_const (B ^ 3)) (by
      filter_upwards [hbound] with w hw
      exact pow_le_pow_left₀ (vec3EuclideanNorm_nonneg _) hw 3)
    simpa only [integral_const, smul_eq_mul, measureReal_def,
      Measure.restrict_apply_univ] using h
  have hreal : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal =
        ∫ w in parabolicCylinder z.1 z.2 r,
          vec3EuclideanNorm (u w) ^ (3 : ℕ) := by
    rw [setIntegral_eq_toReal_setLIntegral_of_nonneg hint
      (Eventually.of_forall fun w ↦ pow_nonneg (vec3EuclideanNorm_nonneg _) 3)]
    congr 1
    apply lintegral_congr
    intro w
    rw [ENNReal.rpow_ofNat, ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _)]
  have hvolume : (volume (parabolicCylinder z.1 z.2 r)).toReal =
      (volume (vec3Ball z.1 r)).toReal * r ^ 2 := by
    rw [volume_parabolicCylinder, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sq_nonneg _)]
  have hscale : r ^ (-2 : ℝ) = r⁻¹ ^ 2 := by
    norm_num [Real.rpow_neg_natCast, inv_pow]
  rw [gamma_cube_eq u z r hr, hreal, hscale]
  calc
    _ ≤ r⁻¹ ^ 2 * ((volume (parabolicCylinder z.1 z.2 r)).toReal * B ^ 3) :=
      mul_le_mul_of_nonneg_left hmass (sq_nonneg _)
    _ = _ := by rw [hvolume]; field_simp [hr.ne']

/-- A uniform essential velocity bound makes the normalized cubic quantity
vanish at the center. -/
theorem tendsto_gamma_of_ae_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {R B : ℝ} (hR : 0 < R)
    (hsub : closure (parabolicCylinder z.1 z.2 R) ⊆ spaceTimeSet Ω I)
    (hbound : ∀ᵐ w ∂volume.restrict (parabolicCylinder z.1 z.2 R),
      vec3EuclideanNorm (u w) ≤ B) :
    Tendsto (gamma u z) (𝓝[>] 0) (𝓝 0) := by
  have hmajor : Tendsto (fun r : ℝ ↦
      (B ^ 3 * (volume (vec3Ball z.1 r)).toReal) ^ (1 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    apply Filter.Tendsto.rpow_const_nhds_zero _ (by norm_num)
    simpa only [mul_zero] using (tendsto_real_volume_vec3Ball z.1).const_mul (B ^ 3)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact gamma_nonneg u z hr.le
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with r hr hrR
    have hsubr := (closure_parabolicCylinder_mono hr.le hrR.le).trans hsub
    have hbr := ae_restrict_of_ae_restrict_of_subset
      (parabolicCylinder_mono hr.le hrR.le) hbound
    have h := Real.rpow_le_rpow (pow_nonneg (gamma_nonneg u z hr.le) 3)
      (gamma_cube_le_of_ae_bound hsol hr hsubr hbr) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have heq : (gamma u z r ^ 3) ^ (1 / 3 : ℝ) = gamma u z r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (gamma_nonneg u z hr.le)]
      norm_num
    simpa only [heq] using h

/-- The real pressure quantity is the cube of the CKN pressure quantity. -/
theorem pressureD_eq_delta_cube
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    pressureD p z r = delta p z r ^ 3 := by
  unfold pressureD
  rw [sws_integral_abs_pow_eq_delta_cube hsol z hr hsub]
  field_simp [hr.ne']

/-- A bounded actual suitable velocity also has vanishing CKN pressure quantity. -/
theorem tendsto_delta_of_ae_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hsub : closure (parabolicCylinder z.1 z.2 R) ⊆ spaceTimeSet Ω I)
    (hbound : ∀ᵐ w ∂volume.restrict (parabolicCylinder z.1 z.2 R),
      vec3EuclideanNorm (u w) ≤ B) :
    Tendsto (delta p z) (𝓝[>] 0) (𝓝 0) := by
  have hpressure := tendsto_pressureD_of_ae_bound hsol hR hB hsub hbound
  have h := hpressure.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 1 / 3)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with r hr hrR
  rw [pressureD_eq_delta_cube hsol hr
    ((closure_parabolicCylinder_mono hr.le hrR.le).trans hsub),
    ← Real.rpow_natCast, ← Real.rpow_mul (delta_nonneg p z hr.le)]
  norm_num

/-- Actual Caccioppoli, with force zero, makes the gradient quantity vanish
once the bounded velocity and its pressure quantity vanish. -/
theorem tendsto_beta_of_ae_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hsub : closure (parabolicCylinder z.1 z.2 R) ⊆ spaceTimeSet Ω I)
    (hbound : ∀ᵐ w ∂volume.restrict (parabolicCylinder z.1 z.2 R),
      vec3EuclideanNorm (u w) ≤ B) :
    Tendsto (beta u Du z) (𝓝[>] 0) (𝓝 0) := by
  have hg := tendsto_gamma_of_ae_bound hsol hR hsub hbound
  have hd := tendsto_delta_of_ae_bound hsol hR hB hsub hbound
  have hid : Tendsto (fun r : ℝ ↦ r) (𝓝[>] 0) (𝓝 0) :=
    (continuous_id.tendsto 0).mono_left inf_le_left
  have htwo : Tendsto (fun r : ℝ ↦ 2 * r) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using hid.const_mul 2, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos (by norm_num) hr
  have hg₂ : Tendsto (fun r : ℝ ↦ gamma u z (2 * r)) (𝓝[>] 0) (𝓝 0) := hg.comp htwo
  have hd₂ : Tendsto (fun r : ℝ ↦ delta p z (2 * r)) (𝓝[>] 0) (𝓝 0) := hd.comp htwo
  let F : ℝ → ℝ := fun r ↦ CKN.Core.Endgame.startGammaConstant *
    (gamma u z (2 * r) / 2 + 2 * gamma u z (2 * r) ^ (3 / 2 : ℝ) +
      2 * delta p z (2 * r) * gamma u z (2 * r) ^ (1 / 2 : ℝ))
  have hF : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have hprod := hd₂.mul
      (hg₂.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 1 / 2))
    have h := ((hg₂.div_const 2).add
      ((hg₂.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 3 / 2)).const_mul 2)).add
        (hprod.const_mul 2)
    have h' := h.const_mul CKN.Core.Endgame.startGammaConstant
    simp only [zero_div, mul_zero, add_zero] at h'
    convert h' using 1
    funext r
    dsimp [F]
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hF
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact beta_nonneg u Du z hr.le
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by positivity : (0 : ℝ) < R / 2)).filter_mono
        nhdsWithin_le_nhds] with r hr hrR
    have htwoPos : 0 < 2 * r := mul_pos (by norm_num) hr
    have htwoR : 2 * r ≤ R := by linarith only [hrR]
    have hdom := (closure_parabolicCylinder_mono htwoPos.le htwoR).trans hsub
    have hcacc := CKN.Core.Endgame.caccioppoli_gamma_display_fixed hsol
      (mul_pos (by norm_num) hr) hr (by linarith) hdom
    have hq : 0 < q := lt_trans (by norm_num : (0 : ℝ) < 5 / 2) hsol.2.2.2.1
    have hlambda : lambda q (fun _ ↦ 0) z (2 * r) = 0 := by
      simp [lambda, vec3EuclideanNorm_zero, hq.ne', hq]
    have hratio : r / (2 * r) = (1 / 2 : ℝ) := by field_simp [hr.ne']
    rw [hratio, hlambda] at hcacc
    norm_num at hcacc
    have hα := alpha_nonneg u z hr.le
    dsimp [F]
    nlinarith only [hcacc, hα]

/-- The normalized actual Dirichlet integral vanishes for bounded velocity. -/
theorem tendsto_normalized_gradient_of_ae_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hsub : closure (parabolicCylinder z.1 z.2 R) ⊆ spaceTimeSet Ω I)
    (hbound : ∀ᵐ w ∂volume.restrict (parabolicCylinder z.1 z.2 R),
      vec3EuclideanNorm (u w) ≤ B) :
    Tendsto (fun r : ℝ ↦ (ENNReal.ofReal r)⁻¹ *
      ∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal (spatialGradientSq u Du w))
      (𝓝[>] 0) (𝓝 0) := by
  have hb := tendsto_beta_of_ae_bound hsol hR hB hsub hbound
  have h : Tendsto (fun r : ℝ ↦ ENNReal.ofReal (beta u Du z r ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (hb.pow 2)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with r hr hrR
  rw [sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq hsol z hr
    ((closure_parabolicCylinder_mono hr.le hrR.le).trans hsub),
    ← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
  congr 1
  field_simp [hr.ne']

/-- A local essential bound for an actual suitable unforced solution implies
the CKN Hölder-representative regularity predicate. -/
theorem suitable_regular_of_ae_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hsub : closure (parabolicCylinder z.1 z.2 R) ⊆ spaceTimeSet Ω I)
    (hbound : ∀ᵐ w ∂volume.restrict (parabolicCylinder z.1 z.2 R),
      vec3EuclideanNorm (u w) ≤ B) :
    IsRegularPoint Ω I u z := by
  have hz : z ∈ spaceTimeSet Ω I := by
    apply hsub
    apply subset_closure
    constructor
    · simpa only [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero] using hR
    · exact ⟨by nlinarith [sq_pos_of_pos hR], le_rfl⟩
  obtain ⟨ε, hε, hreg⟩ := CKN.epsilonRegularityGradient q hsol.2.2.2.1
  apply hreg Ω I u Du p (fun _ ↦ 0)
    (CKN.isSuitableWeakSolution_iff_integrable.mpr hsol) z hz
  rw [(tendsto_normalized_gradient_of_ae_bound hsol hR hB hsub hbound).limsup_eq]
  exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos hε)

open CKNChallenge in
/-- The same implication in the project's ordinary-coordinate suitable
solution interface, with the specified Hölder representative conclusion. -/
theorem suitable_holderRegular_of_ae_bound
    {Ω : Set Space} {I : Set ℝ} {q : ℝ≥0} (hq : 5 / 2 < (q : ℝ))
    (sol : LocalWeakNSESolution Ω I q) (hforce : sol.f = fun _ ↦ 0)
    {z : SpaceTime} {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hsub : closure (Q R z) ⊆ Ω ×ˢ I)
    (hbound : ∀ᵐ w ∂volume.restrict (Q R z), ‖sol.u w‖ ≤ B) :
    IsHolderRegularPoint sol.u z := by
  let zr : RawPoint := (rawToEuclidean.symm z.1, z.2)
  have hsolRaw : IsSuitableWeakSolutionIntegrable (rawSpace Ω) I (q : ℝ)
      (pullVelocity sol.u) (pullGradient sol.Dxu) (pullScalar sol.p) (fun _ ↦ 0) := by
    have h := CKN.isSuitableWeakSolution_iff_integrable.mp (rawSuitableWeakSolution hq sol)
    have hzero : pullVelocity (fun _ ↦ 0) = fun _ ↦ 0 := by
      funext w
      change rawToEuclidean.symm 0 = 0
      exact map_zero _
    rw [hforce, hzero] at h
    exact h
  have hsubRaw : closure (parabolicCylinder zr.1 zr.2 R) ⊆ spaceTimeSet (rawSpace Ω) I := by
    intro w hw
    have hd := hsub ((mem_closure_cylinder_iff_mem_closure_Q hR zr w).mp hw)
    change rawToEuclidean w.1 ∈ Ω ∧ w.2 ∈ I
    simpa only [rawSpaceTimeToEuclidean_apply, Set.mem_prod] using hd
  have hboundRaw : ∀ᵐ w ∂volume.restrict (parabolicCylinder zr.1 zr.2 R),
      vec3EuclideanNorm (pullVelocity sol.u w) ≤ B := by
    have hmp := rawSpaceTimeToEuclidean_measurePreserving.restrict_preimage_emb
      rawSpaceTimeToEuclidean.measurableEmbedding (Q R z)
    have h := hmp.quasiMeasurePreserving.ae hbound
    rw [rawSpaceTime_preimage_Q] at h
    simpa only [zr, pullVelocity, vec3EuclideanNorm_rawToEuclidean_symm] using h
  have hreg := suitable_regular_of_ae_bound hsolRaw hR hB hsubRaw hboundRaw
  have hout := isHolderRegularPoint_of_rawRegular hreg
  have hz : parabolicToEuclideanHomeomorph zr = z := by
    change (rawToEuclidean zr.1, zr.2) = z
    simp only [zr, rawToEuclidean.apply_symm_apply]
  rw [hz] at hout
  exact hout

open CKNChallenge in
/-- Every ordinary open neighborhood contains the closure of a sufficiently
small backward parabolic cylinder about its point. -/
theorem exists_closure_cylinder_subset_open
    {U : Set SpaceTime} {z : SpaceTime} (hU : IsOpen U) (hz : z ∈ U) :
    ∃ R : ℝ, 0 < R ∧ closure (Q R z) ⊆ U := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let R : ℝ := min (δ / 2) 1
  have hR : 0 < R := lt_min (by positivity) one_pos
  have hRone : R ≤ 1 := min_le_right _ _
  have hRδ : R < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsquare : R ^ 2 ≤ R := by nlinarith
  refine ⟨R, hR, ?_⟩
  intro w hw
  apply hball
  rw [closure_Q hR] at hw
  rw [Metric.mem_ball, Prod.dist_eq]
  have hspace : dist w.1 z.1 < δ := lt_of_le_of_lt hw.1 hRδ
  have htime : dist w.2 z.2 ≤ R ^ 2 := by
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hw.2.1, hw.2.2, sq_nonneg R]
  exact max_lt hspace (lt_of_le_of_lt (htime.trans hsquare) hRδ)

open CKNChallenge in
/-- Local essential boundedness at an interior point of an actual unforced
suitable solution implies the specified Hölder representative. -/
theorem suitable_holderRegular_of_local_ae_bound
    {Ω : Set Space} {I : Set ℝ} {q : ℝ≥0} (hq : 5 / 2 < (q : ℝ))
    (sol : LocalWeakNSESolution Ω I q) (hforce : sol.f = fun _ ↦ 0)
    {z : SpaceTime} (hzDomain : z ∈ interior (Ω ×ˢ I))
    (hbound : ∃ U : Set SpaceTime, IsOpen U ∧ z ∈ U ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ w ∂volume.restrict U, ‖sol.u w‖ ≤ B) :
    IsHolderRegularPoint sol.u z := by
  obtain ⟨U, hU, hzU, B, hB, hboundU⟩ := hbound
  obtain ⟨R, hR, hsubR⟩ := exists_closure_cylinder_subset_open
    (hU.inter isOpen_interior) ⟨hzU, hzDomain⟩
  have hsubDomain : closure (Q R z) ⊆ Ω ×ˢ I :=
    (hsubR.trans inter_subset_right).trans interior_subset
  have hsubU : Q R z ⊆ U := subset_closure.trans (hsubR.trans inter_subset_left)
  exact suitable_holderRegular_of_ae_bound hq sol hforce hR hB hsubDomain
    (ae_restrict_of_ae_restrict_of_subset hsubU hboundU)

open CKNChallenge in
/-- The manuscript's local essential boundedness and the specification's
Hölder representative convention agree for actual unforced suitable solutions
at interior points. -/
theorem suitable_holderRegular_iff_local_ae_bound
    {Ω : Set Space} {I : Set ℝ} {q : ℝ≥0} (hq : 5 / 2 < (q : ℝ))
    (sol : LocalWeakNSESolution Ω I q) (hforce : sol.f = fun _ ↦ 0)
    {z : SpaceTime} (hzDomain : z ∈ interior (Ω ×ˢ I)) :
    IsHolderRegularPoint sol.u z ↔
      ∃ U : Set SpaceTime, IsOpen U ∧ z ∈ U ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ w ∂volume.restrict U, ‖sol.u w‖ ≤ B :=
  ⟨holder_regular_has_local_ae_bound,
    suitable_holderRegular_of_local_ae_bound hq sol hforce hzDomain⟩

end FluidSingularSets
