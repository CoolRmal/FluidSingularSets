-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedCutoffErrors
public import FluidSingularSets.SuitablePressureMeanPairings

/-!
# Actual viscous pressure pairing with the endpoint velocity cost

The viscous pressure is paired in time L² with the actual corrected velocity,
whose spatial L² norm is controlled by the original source. This uses the
original local interval and the true force primitive. No corrected-velocity
energy supremum appears in this pressure estimate.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

local instance projectedViscousMixedForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance projectedViscousMixedSpaceSecondCountable : SecondCountableTopology Vec3 :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → ℝ))

/-- Genuine extended-real Young absorption also covers an infinite endpoint moment. -/
theorem ennreal_viscous_mixed_young {E X C : ℝ≥0∞} (hC : C ≠ ⊤) (hCpos : 0 < C)
    {δ : ℝ} (hδ : 0 < δ) :
    C * E ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal δ * E + C ^ 2 / (4 * ENNReal.ofReal δ) * X := by
  have hd : ENNReal.ofReal δ ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
  by_cases hE : E = ⊤
  · simp [hE, hd]
  by_cases hX : X = ⊤
  · have hc : C ^ 2 / (4 * ENNReal.ofReal δ) ≠ 0 := by
      exact ENNReal.div_ne_zero.mpr ⟨pow_ne_zero 2 hCpos.ne', by finiteness⟩
    simp [hX, hc]
  have hf₁ : ENNReal.ofReal δ * E ≠ ⊤ := by finiteness
  have hf₂ : C ^ 2 / (4 * ENNReal.ofReal δ) * X ≠ ⊤ := by
    finiteness [hC, hX, hd]
  have hfl : C * E ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) ≠ ⊤ := by
    finiteness [hC, hE, hX]
  apply (ENNReal.toReal_le_toReal hfl (ENNReal.add_ne_top.mpr ⟨hf₁, hf₂⟩)).mp
  simp only [ENNReal.toReal_add hf₁ hf₂, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hδ.le]
  have hr := projected_viscous_pressure_young (E := E.toReal) (M := X.toReal)
    (T := 1) (C := C.toReal) ENNReal.toReal_nonneg ENNReal.toReal_nonneg zero_le_one hδ
  simpa only [Real.sqrt_eq_rpow, Real.one_rpow, mul_one, div_mul_eq_mul_div] using hr

/-- A finite explicit positive endpoint coefficient for the actual cutoff pairing. -/
def projectedViscousMixedPairingCoefficient (L : ℝ) : ℝ≥0∞ :=
  1 + 12 * ENNReal.ofReal (6 * L) * projectedVelocitySliceCoefficient *
    volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ)

theorem projectedViscousMixedPairingCoefficient_ne_top (L : ℝ) :
    projectedViscousMixedPairingCoefficient L ≠ ⊤ := by
  unfold projectedViscousMixedPairingCoefficient
  have hv : volume (vec3Ball (0 : Vec3) 1) ≠ ⊤ := volume_vec3Ball_lt_top.ne
  finiteness [projectedVelocitySliceCoefficient_ne_top, hv]

theorem projectedViscousMixedPairingCoefficient_pos (L : ℝ) :
    0 < projectedViscousMixedPairingCoefficient L := by
  exact zero_lt_one.trans_le (le_add_right le_rfl)

/-- True spatial L² pressure and velocity curves give a literal time L¹ pairing. -/
theorem pressureCurve_pairing_two_two_integrable_and_bound
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ : Measure A} {ν : Measure T} {P : T → Lp ℝ 2 μ} {G : A × T → ℝ}
    (hP : MemLp P 2 ν)
    (hGs : ∀ᵐ t ∂ν, MemLp (fun x ↦ G (x, t)) 2 μ)
    (hGc : MemLp (actualSliceLp (μ := μ) (p := 2) G) 2 ν) :
    Integrable (fun t ↦ ∫ x, P t x * G (x, t) ∂μ) ν ∧
      ‖∫ t, ∫ x, P t x * G (x, t) ∂μ ∂ν‖ₑ ≤
        eLpNorm P 2 ν * eLpNorm (actualSliceLp (μ := μ) (p := 2) G) 2 ν := by
  have heq : (fun t ↦ ∫ x, P t x * G (x, t) ∂μ) =ᵐ[ν]
      (fun t ↦ inner ℝ (P t) (actualSliceLp (μ := μ) (p := 2) G t)) := by
    filter_upwards [hGs] with t ht
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [actualSliceLp_ae G t ht] with x hx
    simp only [hx, Real.inner_apply]
  have hm : MemLp (fun t ↦ inner ℝ (P t)
      (actualSliceLp (μ := μ) (p := 2) G t)) 1 ν :=
    (eLpNorm_real_inner_le (p := 2) (q := 2) (r := 1)
      hP.aestronglyMeasurable hGc.aestronglyMeasurable).trans_lt
        (ENNReal.mul_lt_top hP.eLpNorm_lt_top hGc.eLpNorm_lt_top)
  refine ⟨(memLp_one_iff_integrable.mp hm).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  exact ((enorm_integral_le_lintegral_enorm _).trans lintegral_enorm_le_eLpNorm_one).trans
    (eLpNorm_real_inner_le (p := 2) (q := 2) (r := 1)
      hP.aestronglyMeasurable hGc.aestronglyMeasurable)

/-- Restricting the genuine pressure class gives its literal time L² pairing on an inner set. -/
theorem pressureCurve_pairing_restrict_two_two_integrable_and_bound
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ η : Measure A} {ν : Measure T} (hμ : μ ≤ η)
    {P : T → Lp ℝ 2 η} {G : A × T → ℝ}
    (hP : MemLp P 2 ν)
    (hGs : ∀ᵐ t ∂ν, MemLp (fun x ↦ G (x, t)) 2 μ)
    (hGc : MemLp (actualSliceLp (μ := μ) (p := 2) G) 2 ν) :
    Integrable (fun t ↦ ∫ x, P t x * G (x, t) ∂μ) ν ∧
      ‖∫ t, ∫ x, P t x * G (x, t) ∂μ ∂ν‖ₑ ≤
        eLpNorm P 2 ν * eLpNorm (actualSliceLp (μ := μ) (p := 2) G) 2 ν := by
  have hm : μ ≤ (1 : ℝ≥0∞) • η := by simpa using hμ
  let L : Lp ℝ 2 η →L[ℝ] Lp ℝ 2 μ :=
    Lp.LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤) hm
  have hL : ‖L‖ ≤ 1 := by
    simpa [L] using Lp.norm_LpToLpOfMeasureLeSMul_le
      (E := ℝ) (p := 2) (by simp : (1 : ℝ≥0∞) ≠ ⊤) hm
  have heq (t : T) : (∫ x, L (P t) x * G (x, t) ∂μ) =
      ∫ x, P t x * G (x, t) ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul
      (by simp : (1 : ℝ≥0∞) ≠ ⊤) hm (P t)] with x hx
    exact congrArg (fun a : ℝ ↦ a * G (x, t)) hx
  have hb := pressureCurve_pairing_two_two_integrable_and_bound
    (hP.continuousLinearMap_comp L) hGs hGc
  have hnorm : eLpNorm (fun t ↦ L (P t)) 2 ν ≤ eLpNorm P 2 ν := by
    apply eLpNorm_mono_ae (hP.continuousLinearMap_comp L).aestronglyMeasurable
    exact ae_of_all _ fun t ↦ (L.le_opNorm (P t)).trans
      ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))
  simp_rw [heq] at hb
  exact ⟨hb.1, hb.2.trans (mul_le_mul' hnorm le_rfl)⟩

section LocalBox

variable {Ω : Set Vec3} {I : Set ℝ} {q a b c : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {B : Set Vec3}

/-- The actual cubed-cutoff velocity on the unchanged local interval. -/
def localBoxProjectedCutoffVelocity (u : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ) (a b c : ℝ)
    (φ : Vec3 → ℝ) (z : ParabolicPoint) : Vec3 :=
  φ z.1 ^ 3 • localBoxProjectedVelocityAmbient u D p a b c z

/-- The literal sixth-cutoff viscous pressure test component. -/
def localBoxProjectedViscousTestComponent (u : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ) (a b c : ℝ)
    (φ : Vec3 → ℝ) (θ : ℝ → ℝ) (i : Fin 3) (z : ParabolicPoint) : ℝ :=
  θ z.2 * localBoxProjectedVelocityAmbient u D p a b c z i *
    spatialDeriv (fun x ↦ φ x ^ (6 : ℕ)) i z.1

/-- The actual pressure test factors through the true cubed-cutoff velocity. -/
theorem localBoxProjectedViscousTestComponent_eq_weighted
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (θ : ℝ → ℝ) (i : Fin 3) (z : ParabolicPoint) :
    localBoxProjectedViscousTestComponent u D p a b c φ θ i z =
      (6 * θ z.2 * φ z.1 ^ 2 * spatialDeriv φ i z.1) *
        localBoxProjectedCutoffVelocity u D p a b c φ z i := by
  simp only [localBoxProjectedViscousTestComponent, localBoxProjectedCutoffVelocity,
    spatialDeriv_cutoff_sixth hφ, Pi.smul_apply, smul_eq_mul]
  ring

/-- The original suitable force controls the actual correction on the original interval. -/
theorem localBox_projected_harmonic_gradient_velocity_bound_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ x : unitBallPressureCompactInterior,
      ‖localBoxProjectedHarmonicGradientAmbient u D p a b c (x.1, t)‖ ≤
        projectedHarmonicGradientVelocityConstant * ‖unitBallVelocityCurve u t‖ := by
  filter_upwards [suitable_unitBall_velocityForce_ae_primitive_localBox hsol hbox hab hc]
    with t ht
  intro x
  rw [localBoxProjectedHarmonicGradientAmbient_eq_compact u D p a b c x t]
  unfold localBoxProjectedHarmonicGradient localBoxHarmonicTimePrimitive
  rw [← ht]
  change ‖-unitBallHarmonicForceGradientExtended (unitBallVelocityForceCurve u t) x‖ ≤ _
  rw [norm_neg]
  exact ((unitBallHarmonicForceGradientExtended (unitBallVelocityForceCurve u t)).norm_coe_le_norm x
    |>.trans (unitBallHarmonicForceGradientExtended_norm_le _)).trans
      ((mul_le_mul_of_nonneg_left (unitBallVelocityForceCurve_norm_le_actual_class u t)
        unitBallPressureGradientConstant_nonneg).trans_eq
          (by unfold projectedHarmonicGradientVelocityConstant; ring))

/-- The true projected spatial norm has its actual full-source bound on the original interval. -/
theorem localBoxProjectedVelocityAmbient_slice_norm_le_source_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      eLpNorm (fun x ↦ localBoxProjectedVelocityAmbient u D p a b c (x, t)) 2
        (volume.restrict B) ≤
        projectedVelocitySliceCoefficient * ‖unitBallVelocityCurve u t‖ₑ := by
  have hB1 : B ⊆ vec3Ball 0 1 := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  filter_upwards [slice_memLp_ae_of_sws hsol hbox,
    localBox_projected_harmonic_gradient_velocity_bound_ae hsol hbox hab hc] with t hu hb
  have hmH := (localBoxProjectedHarmonicGradientAmbient_memLp_two u D p a b c t).mono_measure
    (Measure.restrict_mono_set volume hBK)
  have hHbound : ∀ᵐ x ∂volume.restrict B,
      ‖localBoxProjectedHarmonicGradientAmbient u D p a b c (x, t)‖ ≤
        projectedHarmonicGradientVelocityConstant * ‖unitBallVelocityCurve u t‖ := by
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    exact hb ⟨x, hBK hx⟩
  have hHnorm := eLpNorm_le_of_ae_bound (p := 2) hmH.aestronglyMeasurable hHbound
  simp only [ENNReal.toReal_ofNat, inv_eq_one_div, Measure.restrict_apply_univ,
    ENNReal.ofReal_mul projectedHarmonicGradientVelocityConstant_nonneg, ofReal_norm] at hHnorm
  have hU : eLpNorm (fun x ↦ u (x, t)) 2 (volume.restrict B) ≤
      ‖unitBallVelocityCurve u t‖ₑ := by
    rw [unitBallVelocityCurve, actualSliceLp_enorm u t hu.1]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hB1)
  have hH : eLpNorm (fun x ↦ localBoxProjectedHarmonicGradientAmbient u D p a b c (x, t)) 2
      (volume.restrict B) ≤
      ENNReal.ofReal projectedHarmonicGradientVelocityConstant *
        volume unitBallPressureCompactInterior ^ (1 / 2 : ℝ) *
          ‖unitBallVelocityCurve u t‖ₑ := by
    apply hHnorm.trans
    calc
      _ = ENNReal.ofReal projectedHarmonicGradientVelocityConstant *
          volume B ^ (1 / 2 : ℝ) * ‖unitBallVelocityCurve u t‖ₑ := by ring
      _ ≤ _ := by gcongr
  have hsum := eLpNorm_add_le (f := fun x ↦ u (x, t))
    (g := fun x ↦ localBoxProjectedHarmonicGradientAmbient u D p a b c (x, t))
    (μ := volume.restrict B) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  calc
    _ ≤ eLpNorm (fun x ↦ u (x, t)) 2 (volume.restrict B) +
        eLpNorm (fun x ↦ localBoxProjectedHarmonicGradientAmbient u D p a b c (x, t)) 2
          (volume.restrict B) := hsum
    _ ≤ ‖unitBallVelocityCurve u t‖ₑ +
        ENNReal.ofReal projectedHarmonicGradientVelocityConstant *
          volume unitBallPressureCompactInterior ^ (1 / 2 : ℝ) *
            ‖unitBallVelocityCurve u t‖ₑ := add_le_add hU hH
    _ = _ := by unfold projectedVelocitySliceCoefficient; ring

/-- Finite-volume Holder bounds the genuine full-source time L² norm by its L²L⁶ moment. -/
theorem localBox_velocityCurve_two_sq_le_six_moment
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    eLpNorm (unitBallVelocityCurve u) 2 (volume.restrict (Ioo a b)) ^ 2 ≤
      volume (vec3Ball (0 : Vec3) 1) ^ (2 / 3 : ℝ) *
        ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2 := by
  let : IsFiniteMeasure (volume.restrict (vec3Ball (0 : Vec3) 1)) :=
    isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  have ha := suitable_velocityCurve_memLp_localBox hsol hbox
  have heq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    ha.aestronglyMeasurable
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at heq
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ‖unitBallVelocityCurve u t‖ₑ ^ 2 ≤ volume (vec3Ball (0 : Vec3) 1) ^ (2 / 3 : ℝ) *
        eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) ^ 2 := by
    filter_upwards [slice_memLp_ae_of_sws hsol hbox] with t ht
    rw [unitBallVelocityCurve, actualSliceLp_enorm u t ht.1]
    have hc := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 2) (q := 6)
      (by norm_num) ht.1.aestronglyMeasurable
    norm_num only [ENNReal.toReal_ofNat, Measure.restrict_apply_univ] at hc
    have hp := pow_le_pow_left' hc 2
    rw [mul_pow, ← ENNReal.rpow_natCast (volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ)) 2,
      ← ENNReal.rpow_mul] at hp
    norm_num only [show (1 / 3 : ℝ) * 2 = 2 / 3 by norm_num] at hp
    exact hp.trans_eq (mul_comm _ _)
  rw [heq]
  apply (lintegral_mono_ae hpoint).trans_eq
  exact lintegral_const_mul' _ _
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) volume_vec3Ball_lt_top.ne).ne

/-- The true endpoint velocity moment bounds the genuine source curve norm. -/
theorem localBox_velocityCurve_two_le_six_moment_sqrt
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    eLpNorm (unitBallVelocityCurve u) 2 (volume.restrict (Ioo a b)) ≤
      volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ) *
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2) ^ (1 / 2 : ℝ) := by
  have hh := ENNReal.rpow_le_rpow (localBox_velocityCurve_two_sq_le_six_moment hsol hbox)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul] at hh
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    show (2 / 3 : ℝ) * (1 / 2) = 1 / 3 by norm_num, ENNReal.rpow_one] at hh
  exact hh

/-- Actual suitability gives the pressure test genuine time L² spatial L² data. -/
theorem localBoxProjectedViscousTestComponent_curve_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i : Fin 3) :
    (∀ᵐ t ∂volume.restrict (Ioo a b), MemLp
      (fun x ↦ localBoxProjectedViscousTestComponent u D p a b c φ θ i (x, t)) 2
        (volume.restrict B)) ∧
    MemLp (actualSliceLp (μ := volume.restrict B) (p := 2)
      (localBoxProjectedViscousTestComponent u D p a b c φ θ i)) 2
        (volume.restrict (Ioo a b)) ∧
    eLpNorm (actualSliceLp (μ := volume.restrict B) (p := 2)
      (localBoxProjectedViscousTestComponent u D p a b c φ θ i)) 2
        (volume.restrict (Ioo a b)) ≤
      ENNReal.ofReal (6 * L) * projectedVelocitySliceCoefficient *
        eLpNorm (unitBallVelocityCurve u) 2 (volume.restrict (Ioo a b)) := by
  let G := localBoxProjectedViscousTestComponent u D p a b c φ θ i
  let A : Vec3 × ℝ → ℝ := fun z ↦ 6 * θ z.2 * φ z.1 ^ 5 * spatialDeriv φ i z.1
  have hA : Continuous A :=
    ((continuous_const.mul (hθ.comp continuous_snd)).mul
      ((hφ.pow 5).continuous.comp continuous_fst)).mul
        ((contDiff_spatialDeriv_smooth hφ i).continuous.comp continuous_fst)
  have heq : G = fun z ↦ A z * localBoxProjectedVelocityAmbient u D p a b c z i := by
    funext z
    simp only [G, localBoxProjectedViscousTestComponent, spatialDeriv_cutoff_sixth hφ, A]
    ring
  have hAb (z : ParabolicPoint) : ‖A z‖ ≤ 6 * L := by
    have hg : ‖spatialDeriv φ i z.1‖ ≤ L :=
      (norm_le_pi_norm (classicalGradient φ z.1) i).trans (hgrad z.1)
    have hp : ‖φ z.1 ^ 5‖ ≤ 1 := by
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (hb z.1).1]
      exact pow_le_one₀ (hb z.1).1 (hb z.1).2
    calc
      ‖A z‖ = 6 * ‖θ z.2‖ * ‖φ z.1 ^ 5‖ * ‖spatialDeriv φ i z.1‖ := by
        simp only [A, norm_mul, Real.norm_ofNat]
      _ ≤ 6 * 1 * 1 * L := by gcongr; exact hθb z.2
      _ = 6 * L := by ring
  have hV : AEStronglyMeasurable (localBoxProjectedVelocityAmbient u D p a b c)
      ((volume.restrict B).prod (volume.restrict (Ioo a b))) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact (localBoxProjectedVelocityAmbient_joint_memLp_two u D p a b c
      hsol hbox hab hc hBK).1.aestronglyMeasurable
  have hGj : AEStronglyMeasurable G
      ((volume.restrict B).prod (volume.restrict (Ioo a b))) := by
    rw [heq]
    exact hA.aestronglyMeasurable.mul ((continuous_apply i).comp_aestronglyMeasurable hV)
  have hGb (z : ParabolicPoint) : ‖G z‖ ≤ 6 * L *
      ‖localBoxProjectedVelocityAmbient u D p a b c z‖ := by
    rw [heq, norm_mul]
    exact mul_le_mul (hAb z) (norm_le_pi_norm _ i) (norm_nonneg _) (by positivity)
  have hGs : ∀ᵐ t ∂volume.restrict (Ioo a b),
      MemLp (fun x ↦ G (x, t)) 2 (volume.restrict B) := by
    filter_upwards [localBoxProjectedVelocityAmbient_weak_gradient_slices_ae
      u D p a b c hsol hbox hB hBK, hGj.prodMk_right] with t ht hgt
    exact ht.1.of_le_mul hgt (ae_of_all _ fun x ↦ hGb (x, t))
  have hcap : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ‖actualSliceLp (μ := volume.restrict B) (p := 2) G t‖ₑ ≤
        (ENNReal.ofReal (6 * L) * projectedVelocitySliceCoefficient) *
          ‖unitBallVelocityCurve u t‖ₑ := by
    filter_upwards [hGs, localBoxProjectedVelocityAmbient_slice_norm_le_source_ae
      hsol hbox hab hc hB hBK] with t hgt hvt
    rw [actualSliceLp_enorm G t hgt]
    exact (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hgt.aestronglyMeasurable
      (ae_of_all _ fun x ↦ hGb (x, t)) 2).trans
        ((mul_le_mul' le_rfl hvt).trans_eq (mul_assoc _ _ _).symm)
  have hnorm := eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' 2
    (aestronglyMeasurable_actualSliceLp hGj (by norm_num)) hcap
  have hGc : MemLp (actualSliceLp (μ := volume.restrict B) (p := 2) G) 2
      (volume.restrict (Ioo a b)) := hnorm.trans_lt
    (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top projectedVelocitySliceCoefficient_ne_top.lt_top)
      (suitable_velocityCurve_memLp_localBox hsol hbox).eLpNorm_lt_top)
  exact ⟨hGs, hGc, hnorm⟩

/-- The actual viscous pressure pairing has no corrected-velocity energy supremum term. -/
theorem suitable_projected_viscous_mixed_pairing_bound_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i : Fin 3) :
    Integrable (fun t ↦ ∫ x in B, (unitBallViscousPressureCurve D t).val x *
      localBoxProjectedViscousTestComponent u D p a b c φ θ i (x, t))
        (volume.restrict (Ioo a b)) ∧
    ‖∫ t in Ioo a b, ∫ x in B, (unitBallViscousPressureCurve D t).val x *
      localBoxProjectedViscousTestComponent u D p a b c φ θ i (x, t)‖ₑ ≤
      12 * (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ))
        ^ (1 / 2 : ℝ) * ENNReal.ofReal (6 * L) * projectedVelocitySliceCoefficient *
          volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ) *
            (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
              (volume.restrict (vec3Ball 0 1)) ^ 2) ^ (1 / 2 : ℝ) := by
  have hG := localBoxProjectedViscousTestComponent_curve_data
    hsol hbox hab hc hB hBK hφ hb hL hgrad hθ hθb i
  have hB1 : B ⊆ vec3Ball 0 1 := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  have hDn := hsol.toData.aestronglyMeasurable_gradient hbox
  have hD : AEStronglyMeasurable D
      ((volume.restrict (vec3Ball 0 1)).prod (volume.restrict (Ioo a b))) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hDn
  have hDs : ∀ᵐ t ∂volume.restrict (Ioo a b),
      MemLp (fun x ↦ D (x, t)) 2 (volume.restrict (vec3Ball 0 1)) := by
    filter_upwards [slice_memLp_ae_of_sws hsol hbox] with t ht
    exact ht.2
  have hfin : (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ D (x, t)) 2
      (volume.restrict (vec3Ball 0 1)) ^ 2) < ⊤ := by
    rw [lintegral_spatial_two_sq_eq hDn]
    exact (lintegral_mono (fun _ ↦ le_add_left le_rfl)).trans_lt
      (hsol.toData.energy_lintegral_lt_top hbox)
  have hP := unitBallViscousPressureCurve_memLp_two_of_gradient_moment hD hDs hfin
  have hPv : MemLp (fun t ↦ (unitBallViscousPressureCurve D t).val) 2
      (volume.restrict (Ioo a b)) :=
    hP.continuousLinearMap_comp unitBallMeanZeroL2.toSubmodule.subtypeL
  have hPeq : eLpNorm (fun t ↦ (unitBallViscousPressureCurve D t).val) 2
      (volume.restrict (Ioo a b)) =
      eLpNorm (unitBallViscousPressureCurve D) 2 (volume.restrict (Ioo a b)) :=
    eLpNorm_congr_norm_ae hPv.aestronglyMeasurable hP.aestronglyMeasurable
      (ae_of_all _ fun _ ↦ rfl)
  have hpbound := unitBallViscousPressureCurve_eLpNorm_two_le_gradient_moment hD hDs
  rw [lintegral_spatial_two_sq_eq hDn] at hpbound
  change eLpNorm (unitBallViscousPressureCurve D) 2 (volume.restrict (Ioo a b)) ≤
    12 * (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ))
      ^ (1 / 2 : ℝ) at hpbound
  have hh := pressureCurve_pairing_restrict_two_two_integrable_and_bound
    (Measure.restrict_mono_set volume hB1) hPv hG.1 hG.2.1
  rw [hPeq] at hh
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hgb := hG.2.2.trans (mul_le_mul' le_rfl
    (localBox_velocityCurve_two_le_six_moment_sqrt hsol hbox))
  exact (mul_le_mul' hpbound hgb).trans_eq (by ring)

/-- Actual suitable viscous pressure is absorbed by original gradient and endpoint cost alone. -/
theorem suitable_projected_viscous_mixed_pairing_young_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1)
    (i : Fin 3) {δ : ℝ} (hδ : 0 < δ) :
    ‖∫ t in Ioo a b, ∫ x in B, (unitBallViscousPressureCurve D t).val x *
      localBoxProjectedViscousTestComponent u D p a b c φ θ i (x, t)‖ₑ ≤
      ENNReal.ofReal δ * (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b,
        ‖D z‖ₑ ^ (2 : ℝ)) +
      projectedViscousMixedPairingCoefficient L ^ 2 / (4 * ENNReal.ofReal δ) *
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2) := by
  let E : ℝ≥0∞ := ∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ)
  let X : ℝ≥0∞ := ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
    (volume.restrict (vec3Ball 0 1)) ^ 2
  let A : ℝ≥0∞ := 12 * ENNReal.ofReal (6 * L) * projectedVelocitySliceCoefficient *
    volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ)
  have hh := (suitable_projected_viscous_mixed_pairing_bound_localBox
    hsol hbox hab hc hB hBK hφ hb hL hgrad hθ hθb i).2
  have hbnd : ‖∫ t in Ioo a b, ∫ x in B, (unitBallViscousPressureCurve D t).val x *
      localBoxProjectedViscousTestComponent u D p a b c φ θ i (x, t)‖ₑ ≤
      projectedViscousMixedPairingCoefficient L * E ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ A * E ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) := hh.trans_eq (by dsimp [A, E, X]; ring)
      _ ≤ _ := mul_le_mul' (mul_le_mul' (le_add_left le_rfl) le_rfl) le_rfl
  exact hbnd.trans (ennreal_viscous_mixed_young
    (projectedViscousMixedPairingCoefficient_ne_top L)
    (projectedViscousMixedPairingCoefficient_pos L) hδ)

end LocalBox

end FluidSingularSets
