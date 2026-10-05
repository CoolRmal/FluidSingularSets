-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SuitableProjectedVelocityEnergy
public import FluidSingularSets.UnitBallPressureMixedBounds
public import FluidSingularSets.MixedQuadraticSources

/-!
# Actual harmonic and pressure cutoff errors

The source norm in the harmonic estimate is the original full-ball velocity
norm. The tested velocity lives on the smaller cutoff ball. The estimates
below keep these genuine spatial domains distinct and use actual L² classes.
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

local instance projectedCutoffErrorsSpaceSecondCountable : SecondCountableTopology Vec3 :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → ℝ))

/-- An external actual source norm controls the inner quadratic source class. -/
theorem actualSliceLp_one_le_of_external_quadratic_source
    {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure A} [SFinite μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {U : A × T → E} {F : A × T → ℝ} {a : T → ℝ}
    (hU : AEStronglyMeasurable U (μ.prod ν))
    (hF : AEStronglyMeasurable F (μ.prod ν))
    (hUs : ∀ᵐ t ∂ν, MemLp (fun x ↦ U (x, t)) 2 μ) (ha : MemLp a 2 ν)
    (hUnorm : ∀ᵐ t ∂ν, ‖actualSliceLp (μ := μ) (p := 2) U t‖ ≤ ‖a t‖)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ‖F (x, t)‖ ≤ (C * ‖a t‖) * ‖U (x, t)‖) :
    (∀ᵐ t ∂ν, MemLp (fun x ↦ F (x, t)) 2 μ) ∧
      eLpNorm (actualSliceLp (μ := μ) (p := 2) F) 1 ν ≤
        ENNReal.ofReal C * eLpNorm a 2 ν ^ 2 := by
  have hgood : ∀ᵐ t ∂ν, MemLp (fun x ↦ F (x, t)) 2 μ := by
    filter_upwards [hF.prodMk_right, hUs, hbound] with t hft hut hbt
    exact hut.of_le_mul hft hbt
  have hUc : MemLp (actualSliceLp (μ := μ) (p := 2) U) 2 ν :=
    ha.of_le (aestronglyMeasurable_actualSliceLp hU (by norm_num)) hUnorm
  have hnorm : ∀ᵐ t ∂ν, ‖actualSliceLp (μ := μ) (p := 2) F t‖ₑ ≤
      ENNReal.ofReal C * ‖(‖a t‖ * ‖actualSliceLp (μ := μ) (p := 2) U t‖ : ℝ)‖ₑ := by
    filter_upwards [hgood, hUs, hbound] with t hft hut hbt
    rw [actualSliceLp_enorm F t hft]
    have hb := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      hft.aestronglyMeasurable hbt 2
    rw [ENNReal.ofReal_mul hC, ofReal_norm, ← actualSliceLp_enorm U t hut] at hb
    simpa only [enorm_mul, enorm_norm, mul_assoc] using hb
  have hsq : eLpNorm (fun t ↦ ‖a t‖ *
      ‖actualSliceLp (μ := μ) (p := 2) U t‖) 1 ν ≤ eLpNorm a 2 ν ^ 2 := by
    have hb := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 2) (q := 2) (r := 1)
      (fun x y : ℝ ↦ x * y) 1 continuous_mul ha.norm.aestronglyMeasurable
      hUc.norm.aestronglyMeasurable
      (ae_of_all _ fun _ ↦ by simp only [NNReal.coe_one, one_mul, norm_mul]; rfl)
    have hucnorm : eLpNorm (actualSliceLp (μ := μ) (p := 2) U) 2 ν ≤ eLpNorm a 2 ν :=
      eLpNorm_mono_ae hUc.aestronglyMeasurable hUnorm
    simp only [ENNReal.coe_one, one_mul, eLpNorm_norm _ ha.aestronglyMeasurable,
      eLpNorm_norm _ hUc.aestronglyMeasurable] at hb
    exact hb.trans ((mul_le_mul' le_rfl hucnorm).trans_eq (pow_two _).symm)
  exact ⟨hgood, (eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' 1
    (aestronglyMeasurable_actualSliceLp hF (by norm_num)) hnorm).trans
      (mul_le_mul' le_rfl hsq)⟩

/-- The real spacetime pairing is integrable with a genuine external quadratic source bound. -/
theorem integrable_product_bound_external_quadratic_source
    {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure A} [SFinite μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {U : A × T → E} {F G : A × T → ℝ} {a : T → ℝ}
    (hU : AEStronglyMeasurable U (μ.prod ν))
    (hF : AEStronglyMeasurable F (μ.prod ν)) (hG : AEStronglyMeasurable G (μ.prod ν))
    (hUs : ∀ᵐ t ∂ν, MemLp (fun x ↦ U (x, t)) 2 μ) (ha : MemLp a 2 ν)
    (hUnorm : ∀ᵐ t ∂ν, ‖actualSliceLp (μ := μ) (p := 2) U t‖ ≤ ‖a t‖)
    (hGs : ∀ᵐ t ∂ν, MemLp (fun x ↦ G (x, t)) 2 μ)
    (hGc : MemLp (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ‖F (x, t)‖ ≤ (C * ‖a t‖) * ‖U (x, t)‖) :
    Integrable (fun z ↦ F z * G z) (μ.prod ν) ∧
      ‖∫ z, F z * G z ∂μ.prod ν‖ₑ ≤
        ENNReal.ofReal C * eLpNorm a 2 ν ^ 2 *
          eLpNorm (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν := by
  have hb := actualSliceLp_one_le_of_external_quadratic_source hU hF hUs ha hUnorm hC hbound
  have hFc : MemLp (actualSliceLp (μ := μ) (p := 2) F) 1 ν :=
    hb.2.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.pow_lt_top ha.eLpNorm_lt_top))
  refine ⟨integrable_mul_of_actualSliceLp_one_top hF hG hb.1 hGs hFc hGc, ?_⟩
  rw [integral_mul_eq_integral_actualSliceLp_inner hF hG hb.1 hGs hFc hGc]
  exact ((enorm_integral_le_lintegral_enorm _).trans lintegral_enorm_le_eLpNorm_one).trans
    ((eLpNorm_real_inner_le (p := 1) (q := ⊤) (r := 1)
      hFc.aestronglyMeasurable hGc.aestronglyMeasurable).trans (mul_le_mul' hb.2 le_rfl))

/-- Actual spatial pressure classes paired with a true L∞ velocity class give a time integral. -/
theorem pressureCurve_pairing_one_top_integrable_and_bound
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ : Measure A} {ν : Measure T}
    {P : T → Lp ℝ 2 μ} {G : A × T → ℝ}
    (hP : MemLp P 1 ν)
    (hGs : ∀ᵐ t ∂ν, MemLp (fun x ↦ G (x, t)) 2 μ)
    (hGc : MemLp (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν) :
    Integrable (fun t ↦ ∫ x, P t x * G (x, t) ∂μ) ν ∧
      ‖∫ t, ∫ x, P t x * G (x, t) ∂μ ∂ν‖ₑ ≤
        eLpNorm P 1 ν * eLpNorm (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν := by
  have heq : (fun t ↦ ∫ x, P t x * G (x, t) ∂μ) =ᵐ[ν]
      (fun t ↦ inner ℝ (P t) (actualSliceLp (μ := μ) (p := 2) G t)) := by
    filter_upwards [hGs] with t ht
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [actualSliceLp_ae G t ht] with x hx
    simp only [hx, Real.inner_apply]
  have hm : MemLp (fun t ↦ inner ℝ (P t)
      (actualSliceLp (μ := μ) (p := 2) G t)) 1 ν :=
    (eLpNorm_real_inner_le (p := 1) (q := ⊤) (r := 1)
      hP.aestronglyMeasurable hGc.aestronglyMeasurable).trans_lt
        (ENNReal.mul_lt_top hP.eLpNorm_lt_top hGc.eLpNorm_lt_top)
  refine ⟨(memLp_one_iff_integrable.mp hm).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  exact ((enorm_integral_le_lintegral_enorm _).trans lintegral_enorm_le_eLpNorm_one).trans
    (eLpNorm_real_inner_le (p := 1) (q := ⊤) (r := 1)
      hP.aestronglyMeasurable hGc.aestronglyMeasurable)

/-- Actual viscous L² pressure classes have a true finite-time L¹ pairing estimate. -/
theorem pressureCurve_pairing_two_top_integrable_and_bound
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ : Measure A} {ν : Measure T} [IsFiniteMeasure ν]
    {P : T → Lp ℝ 2 μ} {G : A × T → ℝ}
    (hP : MemLp P 2 ν)
    (hGs : ∀ᵐ t ∂ν, MemLp (fun x ↦ G (x, t)) 2 μ)
    (hGc : MemLp (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν) :
    Integrable (fun t ↦ ∫ x, P t x * G (x, t) ∂μ) ν ∧
      ‖∫ t, ∫ x, P t x * G (x, t) ∂μ ∂ν‖ₑ ≤
        eLpNorm P 2 ν * ν univ ^ (1 / 2 : ℝ) *
          eLpNorm (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν := by
  have hb := pressureCurve_pairing_one_top_integrable_and_bound
    (hP.mono_exponent (by norm_num)) hGs hGc
  have hc := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
    (by norm_num) hP.aestronglyMeasurable
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat,
    show (1 : ℝ) / 1 - 1 / 2 = 1 / 2 by norm_num] at hc
  exact ⟨hb.1, hb.2.trans (mul_le_mul' hc le_rfl)⟩

/-- Restriction of the true pressure class preserves its literal inner-ball pairing. -/
theorem pressureCurve_pairing_restrict_one_top_integrable_and_bound
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ η : Measure A} {ν : Measure T} (hμ : μ ≤ η)
    {P : T → Lp ℝ 2 η} {G : A × T → ℝ}
    (hP : MemLp P 1 ν)
    (hGs : ∀ᵐ t ∂ν, MemLp (fun x ↦ G (x, t)) 2 μ)
    (hGc : MemLp (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν) :
    Integrable (fun t ↦ ∫ x, P t x * G (x, t) ∂μ) ν ∧
      ‖∫ t, ∫ x, P t x * G (x, t) ∂μ ∂ν‖ₑ ≤
        eLpNorm P 1 ν * eLpNorm (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν := by
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
  have hb := pressureCurve_pairing_one_top_integrable_and_bound
    (hP.continuousLinearMap_comp L) hGs hGc
  have hnorm : eLpNorm (fun t ↦ L (P t)) 1 ν ≤ eLpNorm P 1 ν := by
    apply eLpNorm_mono_ae (hP.continuousLinearMap_comp L).aestronglyMeasurable
    exact ae_of_all _ fun t ↦ (L.le_opNorm (P t)).trans
      ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))
  simp_rw [heq] at hb
  exact ⟨hb.1, hb.2.trans (mul_le_mul' hnorm le_rfl)⟩

/-- The actual full-ball viscous class controls its true inner-ball pairing in finite time. -/
theorem pressureCurve_pairing_restrict_two_top_integrable_and_bound
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ η : Measure A} {ν : Measure T} [IsFiniteMeasure ν] (hμ : μ ≤ η)
    {P : T → Lp ℝ 2 η} {G : A × T → ℝ}
    (hP : MemLp P 2 ν)
    (hGs : ∀ᵐ t ∂ν, MemLp (fun x ↦ G (x, t)) 2 μ)
    (hGc : MemLp (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν) :
    Integrable (fun t ↦ ∫ x, P t x * G (x, t) ∂μ) ν ∧
      ‖∫ t, ∫ x, P t x * G (x, t) ∂μ ∂ν‖ₑ ≤
        eLpNorm P 2 ν * ν univ ^ (1 / 2 : ℝ) *
          eLpNorm (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν := by
  have hb := pressureCurve_pairing_restrict_one_top_integrable_and_bound hμ
    (hP.mono_exponent (by norm_num)) hGs hGc
  have hc := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
    (by norm_num) hP.aestronglyMeasurable
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat,
    show (1 : ℝ) / 1 - 1 / 2 = 1 / 2 by norm_num] at hc
  exact ⟨hb.1, hb.2.trans (mul_le_mul' hc le_rfl)⟩

/-- A genuine suitable source supplies the double spatial ball used by endpoint Sobolev. -/
theorem projectedCutoffErrors_double_localBox
    {Ω : Set Vec3} {I : Set ℝ} {t₀ : ℝ}
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    localBox Ω I (euclideanBall 0 2) (Ioo (t₀ - 4) (t₀ + 4)) := by
  have h := CKN.Core.Endgame.localBox_of_parabolic_ball
    (z₀ := ((0, t₀) : ParabolicPoint)) (by norm_num : (0 : ℝ) < 2)
    ((Metric.ball_subset_ball (by norm_num : (2 : ℝ) * 2 ≤ 8)).trans hdom)
  rw [euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 2)]
  simpa only [Prod.fst, Prod.snd, show (2 : ℝ) ^ 2 = 4 by norm_num] using h

/-- Actual suitability supplies the genuine endpoint L⁶ slices, with no criterion premise. -/
theorem suitable_projected_source_memLp_six_ae
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      MemLp (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) := by
  have hbox := projectedCutoffErrors_double_localBox hdom
  filter_upwards [slice_memLp_ae_of_sws hsol hbox,
    ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)] with t ht hwt
  have hs := unitBallH1Vector_memLp_six ht.1 ht.2 hwt
  rwa [euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1)] at hs

/-- Genuine Young absorption for finite real energy and an arbitrary positive coefficient. -/
theorem projected_viscous_pressure_young {E M T C δ : ℝ}
    (hE : 0 ≤ E) (hM : 0 ≤ M) (hT : 0 ≤ T) (hδ : 0 < δ) :
    C * Real.sqrt E * Real.sqrt T * Real.sqrt M ≤
      δ * E + C ^ 2 * T * M / (4 * δ) := by
  have ha := sq_nonneg (2 * δ * Real.sqrt E - C * Real.sqrt T * Real.sqrt M)
  simp only [sub_sq, mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hT, Real.sq_sqrt hM] at ha
  have hd : 0 < 4 * δ := by positivity
  have hb : C * Real.sqrt E * Real.sqrt T * Real.sqrt M - δ * E ≤
      C ^ 2 * T * M / (4 * δ) := (le_div_iff₀ hd).mpr (by nlinarith only [ha])
  linarith

/-- The literal cubed-cutoff corrected velocity used in the sharp harmonic/pressure estimates. -/
def projectedCutoffVelocity (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) (φ : Vec3 → ℝ) (z : ParabolicPoint) : Vec3 :=
  φ z.1 ^ 3 • suitableProjectedVelocityAmbient u D p t₀ z

/-- The genuine weighted corrected slice energy supremum. -/
def projectedCutoffSliceEnergy (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) (B : Set Vec3) (φ : Vec3 → ℝ) : ℝ≥0∞ :=
  essSup (fun t ↦ ∫⁻ x in B, ‖projectedCutoffVelocity u D p t₀ φ (x, t)‖ₑ ^ (2 : ℝ))
    (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))

/-- The literal component of the actual sixth-cutoff pressure test. -/
def projectedCutoffPressureTestComponent (u : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ) (t₀ : ℝ)
    (φ : Vec3 → ℝ) (θ : ℝ → ℝ) (i : Fin 3) (z : ParabolicPoint) : ℝ :=
  θ z.2 * suitableProjectedVelocityAmbient u D p t₀ z i *
    spatialDeriv (fun x ↦ φ x ^ (6 : ℕ)) i z.1

/-- The actual spatial sixth-power derivative supplies the sharp weighted test. -/
theorem spatialDeriv_cutoff_sixth {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin 3) (x : Vec3) :
    spatialDeriv (fun y ↦ φ y ^ (6 : ℕ)) i x = 6 * φ x ^ 5 * spatialDeriv φ i x := by
  simp only [spatialDeriv, fderiv_fun_pow 6
    (hφ.differentiable (by simp)).differentiableAt, Nat.cast_ofNat,
    nsmul_eq_mul, Nat.reduceSub, smul_apply, smul_eq_mul]

/-- Every actual nonnegative bounded cutoff power decreases the genuine ordinary norm. -/
theorem projected_cutoff_power_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) : ‖a ^ n • v‖ ≤ ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha n)]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ha ha1) (norm_nonneg v)).trans_eq (one_mul _)

section ActualCutoff

variable {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {B : Set Vec3} {φ : Vec3 → ℝ}

/-- The actual cubed-cutoff field has true joint measurability on the inner ball. -/
theorem projectedCutoffVelocity_aestronglyMeasurable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    (hBK : B ⊆ unitBallPressureCompactInterior) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    AEStronglyMeasurable (projectedCutoffVelocity u D p t₀ φ)
      ((volume.restrict B).prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) := by
  have hj := (suitableProjectedVelocityAmbient_joint_memLp_two u D p t₀ hsol hdom hBK).1
  have hV : AEStronglyMeasurable (suitableProjectedVelocityAmbient u D p t₀)
      ((volume.restrict B).prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hj.aestronglyMeasurable
  exact ((hφ.pow 3).continuous.comp continuous_fst).aestronglyMeasurable.smul hV

/-- Actual suitable weak slices give genuine L² cubed-cutoff slices. -/
theorem projectedCutoffVelocity_slices_memLp_two
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      MemLp (fun x ↦ projectedCutoffVelocity u D p t₀ φ (x, t)) 2 (volume.restrict B) := by
  filter_upwards [suitableProjectedVelocityAmbient_weak_gradient_slices_ae
    u D p t₀ hsol hdom hB hBK] with t ht
  apply ht.1.of_le
    ((hφ.pow 3).continuous.aestronglyMeasurable.smul ht.1.aestronglyMeasurable)
  exact ae_of_all _ fun x ↦ projected_cutoff_power_norm_le _ (hb x).1 (hb x).2 3

/-- The genuine weighted corrected energy supremum is finite directly from suitable S1. -/
theorem projectedCutoffSliceEnergy_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) : projectedCutoffSliceEnergy u D p t₀ B φ < ∞ := by
  have hle : ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      (∫⁻ x in B, ‖projectedCutoffVelocity u D p t₀ φ (x, t)‖ₑ ^ (2 : ℝ)) ≤
        ∫⁻ x in B, ‖suitableProjectedVelocityAmbient u D p t₀ (x, t)‖ₑ ^ (2 : ℝ) :=
    ae_of_all _ fun t ↦ lintegral_mono fun x ↦ ENNReal.rpow_le_rpow
      (cutoff_power_smul_enorm_le (suitableProjectedVelocityAmbient u D p t₀ (x, t))
        (hb x).1 (hb x).2 3) (by norm_num)
  exact (essSup_mono_ae hle).trans_lt
    (suitableProjectedVelocityAmbient_essSup_energy_lt_top hsol hdom hB hBK)

/-- The actual weighted spatial class has its true square-root weighted-energy time bound. -/
theorem projectedCutoffVelocity_curve_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    MemLp (actualSliceLp (μ := volume.restrict B) (p := 2)
      (projectedCutoffVelocity u D p t₀ φ)) ⊤
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ∧
    eLpNorm (actualSliceLp (μ := volume.restrict B) (p := 2)
      (projectedCutoffVelocity u D p t₀ φ)) ⊤
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ≤
      projectedCutoffSliceEnergy u D p t₀ B φ ^ (1 / 2 : ℝ) := by
  have hj := projectedCutoffVelocity_aestronglyMeasurable hsol hdom hBK hφ
  exact ⟨actualSliceLp_memLp_top_of_sliceEnergy hj
    (projectedCutoffSliceEnergy_lt_top hsol hdom hB hBK hb),
    actualSliceLp_eLpNorm_top_le_sliceEnergy hj⟩

/-- A genuine scalar cutoff test dominated by the cubed-cutoff velocity has true mixed data. -/
theorem projectedCutoffScalar_curve_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {G : ParabolicPoint → ℝ} (hG : AEStronglyMeasurable G
      ((volume.restrict B).prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))))
    {C : ℝ} (hbound : ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      ∀ᵐ x ∂volume.restrict B, ‖G (x, t)‖ ≤ C *
        ‖projectedCutoffVelocity u D p t₀ φ (x, t)‖) :
    ProjectedEnergySliceData (volume.restrict B)
      (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ⊤ G ∧
    eLpNorm (actualSliceLp (μ := volume.restrict B) (p := 2) G) ⊤
      (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ≤
        ENNReal.ofReal C * projectedCutoffSliceEnergy u D p t₀ B φ ^ (1 / 2 : ℝ) := by
  have hs := projectedCutoffVelocity_slices_memLp_two hsol hdom hB hBK hφ hb
  have hw := projectedCutoffVelocity_curve_data hsol hdom hB hBK hφ hb
  have hd := projectedEnergySliceData_top_of_velocity_bound hG hs hw.1 hbound
  have hnorm : ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      ‖actualSliceLp (μ := volume.restrict B) (p := 2) G t‖ₑ ≤ ENNReal.ofReal C *
        ‖actualSliceLp (μ := volume.restrict B) (p := 2)
          (projectedCutoffVelocity u D p t₀ φ) t‖ₑ := by
    filter_upwards [hd.slices, hs, hbound] with t hgt hwt hbt
    rw [actualSliceLp_enorm G t hgt,
      actualSliceLp_enorm (projectedCutoffVelocity u D p t₀ φ) t hwt]
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hgt.aestronglyMeasurable hbt 2
  exact ⟨hd, (eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' ⊤
    hd.classMemLp.aestronglyMeasurable hnorm).trans (mul_le_mul' le_rfl hw.2)⟩

/-- The true inner scalar velocity class is bounded by the distinct full-ball source class. -/
theorem suitable_inner_velocity_component_class_le_full_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    (hBK : B ⊆ unitBallPressureCompactInterior) (j : Fin 3) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      ‖actualSliceLp (μ := volume.restrict B) (p := 2) (fun z ↦ u z j) t‖ ≤
        ‖unitBallVelocityCurve u t‖ := by
  have hB1 : B ⊆ vec3Ball 0 1 := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  filter_upwards [slice_memLp_ae_of_sws hsol
    (suitableProjected_unitBall_localBox hdom)] with t ht
  have huB := ht.1.mono_measure (Measure.restrict_mono_set volume hB1)
  have hb : ‖actualSliceLp (μ := volume.restrict B) (p := 2) (fun z ↦ u z j) t‖ₑ ≤
      ‖unitBallVelocityCurve u t‖ₑ := by
    rw [actualSliceLp_enorm (fun z ↦ u z j) t (huB.eval j),
      unitBallVelocityCurve, actualSliceLp_enorm u t ht.1]
    exact (eLpNorm_mono_ae (huB.eval j).aestronglyMeasurable
      (ae_of_all _ fun x ↦ norm_le_pi_norm (u (x, t)) j)).trans
        (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hB1))
  have hreal := ENNReal.toReal_mono (by simp) hb
  simpa only [toReal_enorm] using hreal

/-- A bounded genuine time cutoff times a tested velocity component has actual weighted data. -/
theorem projectedCutoff_component_time_test_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i : Fin 3) :
    ProjectedEnergySliceData (volume.restrict B)
      (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ⊤
      (fun z : ParabolicPoint ↦ θ z.2 * projectedCutoffVelocity u D p t₀ φ z i) ∧
    eLpNorm (actualSliceLp (μ := volume.restrict B) (p := 2)
      (fun z : ParabolicPoint ↦ θ z.2 * projectedCutoffVelocity u D p t₀ φ z i)) ⊤
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ≤
      projectedCutoffSliceEnergy u D p t₀ B φ ^ (1 / 2 : ℝ) := by
  have hW := projectedCutoffVelocity_aestronglyMeasurable hsol hdom hBK hφ
  have hm : AEStronglyMeasurable
      (fun z : ParabolicPoint ↦ θ z.2 * projectedCutoffVelocity u D p t₀ φ z i)
      ((volume.restrict B).prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) :=
    (hθ.comp continuous_snd).aestronglyMeasurable.mul
      ((continuous_apply i).comp_aestronglyMeasurable hW)
  have hd := projectedCutoffScalar_curve_data hsol hdom hB hBK hφ hb hm
    (C := 1) (ae_of_all _ fun t ↦ ae_of_all _ fun x ↦ by
      rw [norm_mul, one_mul]
      exact (mul_le_mul (hθb t) (norm_le_pi_norm _ i)
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  refine ⟨hd.1, ?_⟩
  simpa only [ENNReal.ofReal_one, one_mul] using hd.2

/-- Actual smooth pressure tests have genuine weighted mixed classes without extra data. -/
theorem projectedCutoff_pressure_component_test_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i : Fin 3) :
    ProjectedEnergySliceData (volume.restrict B)
      (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ⊤
      (projectedCutoffPressureTestComponent u D p t₀ φ θ i) ∧
    eLpNorm (actualSliceLp (μ := volume.restrict B) (p := 2)
      (projectedCutoffPressureTestComponent u D p t₀ φ θ i)) ⊤
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ≤
      ENNReal.ofReal (6 * L) * projectedCutoffSliceEnergy u D p t₀ B φ ^ (1 / 2 : ℝ) := by
  let A : Vec3 × ℝ → ℝ := fun z ↦ 6 * θ z.2 * φ z.1 ^ 2 * spatialDeriv φ i z.1
  have hA : Continuous A :=
    ((continuous_const.mul (hθ.comp continuous_snd)).mul
      ((hφ.pow 2).continuous.comp continuous_fst)).mul
        ((contDiff_spatialDeriv_smooth hφ i).continuous.comp continuous_fst)
  have heq : projectedCutoffPressureTestComponent u D p t₀ φ θ i =
      fun z ↦ A z * projectedCutoffVelocity u D p t₀ φ z i := by
    funext z
    simp only [projectedCutoffPressureTestComponent, spatialDeriv_cutoff_sixth hφ,
      A, projectedCutoffVelocity, Pi.smul_apply, smul_eq_mul]
    ring
  have hAb (z : ParabolicPoint) : ‖A z‖ ≤ 6 * L := by
    have hg : ‖spatialDeriv φ i z.1‖ ≤ L :=
      (norm_le_pi_norm (classicalGradient φ z.1) i).trans (hgrad z.1)
    have hp : ‖φ z.1 ^ 2‖ ≤ 1 := by
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (hb z.1).1]
      exact pow_le_one₀ (hb z.1).1 (hb z.1).2
    calc
      ‖A z‖ = 6 * ‖θ z.2‖ * ‖φ z.1 ^ 2‖ * ‖spatialDeriv φ i z.1‖ := by
        simp only [A, norm_mul, Real.norm_ofNat]
      _ ≤ 6 * 1 * 1 * L := by gcongr; exact hθb z.2
      _ = 6 * L := by ring
  have hW := projectedCutoffVelocity_aestronglyMeasurable hsol hdom hBK hφ
  have hm : AEStronglyMeasurable
      (projectedCutoffPressureTestComponent u D p t₀ φ θ i)
      ((volume.restrict B).prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) := by
    rw [heq]
    exact hA.aestronglyMeasurable.mul
      ((continuous_apply i).comp_aestronglyMeasurable hW)
  apply projectedCutoffScalar_curve_data hsol hdom hB hBK hφ hb hm
  exact ae_of_all _ fun t ↦ ae_of_all _ fun x ↦ by
    rw [heq, norm_mul]
    exact mul_le_mul (hAb (x, t)) (norm_le_pi_norm _ i)
      (norm_nonneg _) (by positivity)

/-- The true cutoff harmonic component is integrable with its external full-source bound. -/
theorem suitable_projected_harmonic_cutoff_component_integrable_and_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i j : Fin 3) :
    Integrable (fun z : ParabolicPoint ↦ θ z.2 * φ z.1 ^ 6 * u z j *
      suitableProjectedHarmonicDerivativeAmbient u D p t₀ z i j *
        suitableProjectedVelocityAmbient u D p t₀ z i)
      (volume.restrict (B ×ˢ Ioo (t₀ - 4) (t₀ + 4))) ∧
    ‖∫ z : ParabolicPoint in B ×ˢ Ioo (t₀ - 4) (t₀ + 4),
      θ z.2 * φ z.1 ^ 6 * u z j *
        suitableProjectedHarmonicDerivativeAmbient u D p t₀ z i j *
          suitableProjectedVelocityAmbient u D p t₀ z i‖ₑ ≤
      ENNReal.ofReal projectedHarmonicHessianVelocityConstant *
        eLpNorm (unitBallVelocityCurve u) 2
          (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ^ 2 *
            projectedCutoffSliceEnergy u D p t₀ B φ ^ (1 / 2 : ℝ) := by
  let J := Ioo (t₀ - 4) (t₀ + 4)
  let F : ParabolicPoint → ℝ := fun z ↦ φ z.1 ^ 3 * u z j *
    suitableProjectedHarmonicDerivativeAmbient u D p t₀ z i j
  let G : ParabolicPoint → ℝ :=
    fun z ↦ θ z.2 * projectedCutoffVelocity u D p t₀ φ z i
  have hB1 : B ⊆ vec3Ball 0 1 := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  have hU : AEStronglyMeasurable u ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact (hsol.toData.aestronglyMeasurable_velocity
      (suitableProjected_unitBall_localBox hdom)).mono_measure
        (Measure.restrict_mono_set volume (Set.prod_mono hB1 le_rfl))
  have hDH : AEStronglyMeasurable
      (fun z ↦ suitableProjectedHarmonicDerivativeAmbient u D p t₀ z i j)
      ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    have h0 := (suitableProjectedHarmonicAmbient_joint_memLp_two u D p t₀ hsol hdom).2
    have h1 := h0.mono_measure (Measure.restrict_mono_set volume (Set.prod_mono hBK le_rfl))
    exact ((h1.eval i).eval j).aestronglyMeasurable
  have hF : AEStronglyMeasurable F ((volume.restrict B).prod (volume.restrict J)) :=
    (((hφ.pow 3).continuous.comp continuous_fst).aestronglyMeasurable.mul
      ((continuous_apply j).comp_aestronglyMeasurable hU)).mul hDH
  have hgd := projectedCutoff_component_time_test_data hsol hdom hB hBK hφ hb hθ hθb i
  have hUs : ∀ᵐ t ∂volume.restrict J,
      MemLp (fun x ↦ u (x, t) j) 2 (volume.restrict B) := by
    filter_upwards [slice_memLp_ae_of_sws hsol
      (suitableProjected_unitBall_localBox hdom)] with t ht
    exact (ht.1.mono_measure (Measure.restrict_mono_set volume hB1)).eval j
  have hcap : ∀ᵐ t ∂volume.restrict J,
      ‖actualSliceLp (μ := volume.restrict B) (p := 2) (fun z ↦ u z j) t‖ ≤
        ‖(‖unitBallVelocityCurve u t‖ : ℝ)‖ := by
    simpa only [norm_norm] using
      suitable_inner_velocity_component_class_le_full_ae hsol hdom hBK j
  have hbound : ∀ᵐ t ∂volume.restrict J, ∀ᵐ x ∂volume.restrict B,
      ‖F (x, t)‖ ≤ (projectedHarmonicHessianVelocityConstant *
        ‖(‖unitBallVelocityCurve u t‖ : ℝ)‖) * ‖u (x, t) j‖ := by
    filter_upwards [suitable_projected_harmonic_hessian_velocity_bound_ae hsol hdom] with t ht
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    have hdh := ht ⟨x, hBK hx⟩ i j
    rw [← suitableProjectedHarmonicDerivativeAmbient_eq_compact u D p t₀ ⟨x, hBK hx⟩ t i j]
      at hdh
    have hφn : ‖φ x ^ 3‖ ≤ 1 := by
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (hb x).1]
      exact pow_le_one₀ (hb x).1 (hb x).2
    calc
      _ = ‖φ x ^ 3‖ * ‖u (x, t) j‖ *
          ‖suitableProjectedHarmonicDerivativeAmbient u D p t₀ (x, t) i j‖ := by
        simp only [F, norm_mul]
      _ ≤ 1 * ‖u (x, t) j‖ *
          (projectedHarmonicHessianVelocityConstant * ‖unitBallVelocityCurve u t‖) := by
        gcongr
      _ = _ := by rw [norm_norm]; ring
  have ha := suitable_velocityCurve_memLp hsol (projectedCutoffErrors_double_localBox hdom)
  have hresult := integrable_product_bound_external_quadratic_source
    ((continuous_apply j).comp_aestronglyMeasurable hU) hF hgd.1.joint hUs ha.norm hcap
    hgd.1.slices hgd.1.classMemLp projectedHarmonicHessianVelocityConstant_nonneg hbound
  have heq : (fun z : ParabolicPoint ↦ θ z.2 * φ z.1 ^ 6 * u z j *
      suitableProjectedHarmonicDerivativeAmbient u D p t₀ z i j *
        suitableProjectedVelocityAmbient u D p t₀ z i) = fun z ↦ F z * G z := by
    funext z
    simp only [F, G, projectedCutoffVelocity, Pi.smul_apply, smul_eq_mul]
    ring
  have hm : (volume : Measure ParabolicPoint).restrict (B ×ˢ J) =
      (volume.restrict B).prod (volume.restrict J) := by
    rw [Measure.prod_restrict, volume_parabolicPoint_eq_prod]
  rw [heq, hm]
  refine ⟨hresult.1, ?_⟩
  rw [eLpNorm_norm _ ha.aestronglyMeasurable] at hresult
  exact hresult.2.trans (mul_le_mul' le_rfl hgd.2)

/-- Actual finite-volume endpoint control keeps the genuine full source norm explicit. -/
theorem suitable_projected_velocityCurve_two_sq_le_six_moment
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    eLpNorm (unitBallVelocityCurve u) 2
      (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ^ 2 ≤
      volume (vec3Ball (0 : Vec3) 1) ^ (2 / 3 : ℝ) *
        ∫⁻ t in Ioo (t₀ - 4) (t₀ + 4),
          eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) ^ 2 := by
  let : IsFiniteMeasure (volume.restrict (vec3Ball (0 : Vec3) 1)) :=
    isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  have ha := suitable_velocityCurve_memLp hsol (projectedCutoffErrors_double_localBox hdom)
  have heq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    ha.aestronglyMeasurable
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at heq
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      ‖unitBallVelocityCurve u t‖ₑ ^ 2 ≤ volume (vec3Ball (0 : Vec3) 1) ^ (2 / 3 : ℝ) *
        eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) ^ 2 := by
    filter_upwards [suitable_projected_source_memLp_six_ae hsol hdom] with t ht
    rw [unitBallVelocityCurve, actualSliceLp_enorm u t (ht.mono_exponent (by norm_num))]
    have hc := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 2) (q := 6)
      (by norm_num) ht.aestronglyMeasurable
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

/-- The literal harmonic cutoff component is bounded by the actual endpoint velocity cost. -/
theorem suitable_projected_harmonic_cutoff_component_endpoint_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i j : Fin 3) :
    ‖∫ z : ParabolicPoint in B ×ˢ Ioo (t₀ - 4) (t₀ + 4),
      θ z.2 * φ z.1 ^ 6 * u z j *
        suitableProjectedHarmonicDerivativeAmbient u D p t₀ z i j *
          suitableProjectedVelocityAmbient u D p t₀ z i‖ₑ ≤
      ENNReal.ofReal projectedHarmonicHessianVelocityConstant *
        volume (vec3Ball (0 : Vec3) 1) ^ (2 / 3 : ℝ) *
          (∫⁻ t in Ioo (t₀ - 4) (t₀ + 4),
            eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) ^ 2) *
              projectedCutoffSliceEnergy u D p t₀ B φ ^ (1 / 2 : ℝ) := by
  have hc := (suitable_projected_harmonic_cutoff_component_integrable_and_bound
    hsol hdom hB hBK hφ hb hθ hθb i j).2
  exact hc.trans ((mul_le_mul'
    (mul_le_mul' le_rfl (suitable_projected_velocityCurve_two_sq_le_six_moment hsol hdom))
    le_rfl).trans_eq (by ring))

/-- A true full-ball pressure curve pairs with the literal sixth-cutoff component. -/
theorem suitable_projected_pressure_cutoff_component_one_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i : Fin 3)
    {P : ℝ → Lp ℝ 2 (volume.restrict (vec3Ball 0 1))}
    (hP : MemLp P 1 (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) :
    Integrable (fun t ↦ ∫ x in B, P t x *
      projectedCutoffPressureTestComponent u D p t₀ φ θ i (x, t))
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ∧
    ‖∫ t in Ioo (t₀ - 4) (t₀ + 4), ∫ x in B, P t x *
      projectedCutoffPressureTestComponent u D p t₀ φ θ i (x, t)‖ₑ ≤
        eLpNorm P 1 (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) *
          ENNReal.ofReal (6 * L) *
            projectedCutoffSliceEnergy u D p t₀ B φ ^ (1 / 2 : ℝ) := by
  have hB1 : B ⊆ vec3Ball 0 1 := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  have hG := projectedCutoff_pressure_component_test_data
    hsol hdom hB hBK hφ hb hL hgrad hθ hθb i
  have hh := pressureCurve_pairing_restrict_one_top_integrable_and_bound
    (Measure.restrict_mono_set volume hB1) hP hG.1.slices hG.1.classMemLp
  exact ⟨hh.1, hh.2.trans ((mul_le_mul' le_rfl hG.2).trans_eq (by ring))⟩

/-- The true viscous curve pairs with the weighted test and its actual finite time length. -/
theorem suitable_projected_pressure_cutoff_component_two_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i : Fin 3)
    {P : ℝ → Lp ℝ 2 (volume.restrict (vec3Ball 0 1))}
    (hP : MemLp P 2 (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) :
    Integrable (fun t ↦ ∫ x in B, P t x *
      projectedCutoffPressureTestComponent u D p t₀ φ θ i (x, t))
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ∧
    ‖∫ t in Ioo (t₀ - 4) (t₀ + 4), ∫ x in B, P t x *
      projectedCutoffPressureTestComponent u D p t₀ φ θ i (x, t)‖ₑ ≤
        eLpNorm P 2 (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) *
          volume (Ioo (t₀ - 4) (t₀ + 4)) ^ (1 / 2 : ℝ) * ENNReal.ofReal (6 * L) *
            projectedCutoffSliceEnergy u D p t₀ B φ ^ (1 / 2 : ℝ) := by
  let ν := volume.restrict (Ioo (t₀ - 4) (t₀ + 4))
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioo])
  have hB1 : B ⊆ vec3Ball 0 1 := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  have hG := projectedCutoff_pressure_component_test_data
    hsol hdom hB hBK hφ hb hL hgrad hθ hθb i
  have hh := pressureCurve_pairing_restrict_two_top_integrable_and_bound
    (Measure.restrict_mono_set volume hB1) hP hG.1.slices hG.1.classMemLp
  simp only [Measure.restrict_apply_univ] at hh
  exact ⟨hh.1, hh.2.trans ((mul_le_mul' le_rfl hG.2).trans_eq (by ring))⟩

/-- The actual suitable convective pressure has the literal weighted endpoint pairing bound. -/
theorem suitable_projected_convective_pressure_cutoff_component_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i : Fin 3) :
    Integrable (fun t ↦ ∫ x in B, (unitBallConvectivePressureCurve u t).val x *
      projectedCutoffPressureTestComponent u D p t₀ φ θ i (x, t))
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ∧
    ‖∫ t in Ioo (t₀ - 4) (t₀ + 4), ∫ x in B,
      (unitBallConvectivePressureCurve u t).val x *
        projectedCutoffPressureTestComponent u D p t₀ φ θ i (x, t)‖ₑ ≤
      12 * volume (vec3Ball (0 : Vec3) 1) ^ (1 / 6 : ℝ) *
        (∫⁻ t in Ioo (t₀ - 4) (t₀ + 4),
          eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) ^ 2) *
            ENNReal.ofReal (6 * L) *
              projectedCutoffSliceEnergy u D p t₀ B φ ^ (1 / 2 : ℝ) := by
  let ν := volume.restrict (Ioo (t₀ - 4) (t₀ + 4))
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioo])
  have hP : MemLp (unitBallConvectivePressureCurve u) 1 ν :=
    (suitable_convectivePressureCurve_memLp hsol
      (projectedCutoffErrors_double_localBox hdom)).mono_exponent (by norm_num)
  have hPv : MemLp (fun t ↦ (unitBallConvectivePressureCurve u t).val) 1 ν :=
    hP.continuousLinearMap_comp unitBallMeanZeroL2.toSubmodule.subtypeL
  have hPeq : eLpNorm (fun t ↦ (unitBallConvectivePressureCurve u t).val) 1 ν =
      eLpNorm (unitBallConvectivePressureCurve u) 1 ν :=
    eLpNorm_congr_norm_ae hPv.aestronglyMeasurable hP.aestronglyMeasurable
      (ae_of_all _ fun _ ↦ rfl)
  have hh := suitable_projected_pressure_cutoff_component_one_bound
    hsol hdom hB hBK hφ hb hL hgrad hθ hθb i hPv
  have hu : AEStronglyMeasurable u ((volume.restrict (vec3Ball 0 1)).prod ν) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hsol.toData.aestronglyMeasurable_velocity (suitableProjected_unitBall_localBox hdom)
  have hpn := unitBallConvectivePressureCurve_eLpNorm_one_le_six_moment hu
    (suitable_projected_source_memLp_six_ae hsol hdom)
  rw [hPeq] at hh
  exact ⟨hh.1, hh.2.trans (mul_le_mul' (mul_le_mul' hpn le_rfl) le_rfl)⟩

/-- Actual suitable gradient energy controls the literal weighted viscous pressure pairing. -/
theorem suitable_projected_viscous_pressure_cutoff_component_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i : Fin 3) :
    Integrable (fun t ↦ ∫ x in B, (unitBallViscousPressureCurve D t).val x *
      projectedCutoffPressureTestComponent u D p t₀ φ θ i (x, t))
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ∧
    ‖∫ t in Ioo (t₀ - 4) (t₀ + 4), ∫ x in B, (unitBallViscousPressureCurve D t).val x *
      projectedCutoffPressureTestComponent u D p t₀ φ θ i (x, t)‖ₑ ≤
      12 * (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo (t₀ - 4) (t₀ + 4),
        ‖D z‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          volume (Ioo (t₀ - 4) (t₀ + 4)) ^ (1 / 2 : ℝ) * ENNReal.ofReal (6 * L) *
            projectedCutoffSliceEnergy u D p t₀ B φ ^ (1 / 2 : ℝ) := by
  let ν := volume.restrict (Ioo (t₀ - 4) (t₀ + 4))
  have hP := suitable_viscousPressureCurve_memLp hsol
    (projectedCutoffErrors_double_localBox hdom)
  have hPv : MemLp (fun t ↦ (unitBallViscousPressureCurve D t).val) 2 ν :=
    hP.continuousLinearMap_comp unitBallMeanZeroL2.toSubmodule.subtypeL
  have hPeq : eLpNorm (fun t ↦ (unitBallViscousPressureCurve D t).val) 2 ν =
      eLpNorm (unitBallViscousPressureCurve D) 2 ν :=
    eLpNorm_congr_norm_ae hPv.aestronglyMeasurable hP.aestronglyMeasurable
      (ae_of_all _ fun _ ↦ rfl)
  have hh := suitable_projected_pressure_cutoff_component_two_bound
    hsol hdom hB hBK hφ hb hL hgrad hθ hθb i hPv
  have hDn := hsol.toData.aestronglyMeasurable_gradient
    (suitableProjected_unitBall_localBox hdom)
  have hD : AEStronglyMeasurable D ((volume.restrict (vec3Ball 0 1)).prod ν) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hDn
  have hDs : ∀ᵐ t ∂ν,
      MemLp (fun x ↦ D (x, t)) 2 (volume.restrict (vec3Ball 0 1)) := by
    filter_upwards [slice_memLp_ae_of_sws hsol
      (suitableProjected_unitBall_localBox hdom)] with t ht
    exact ht.2
  have hpn := unitBallViscousPressureCurve_eLpNorm_two_le_gradient_moment hD hDs
  rw [lintegral_spatial_two_sq_eq hDn] at hpn
  rw [hPeq] at hh
  exact ⟨hh.1, hh.2.trans
    (mul_le_mul' (mul_le_mul' (mul_le_mul' hpn le_rfl) le_rfl) le_rfl)⟩

/-- Genuine Young absorption for the actual viscous pressure cutoff component. -/
theorem suitable_projected_viscous_pressure_cutoff_component_young
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1)
    (i : Fin 3) {δ : ℝ} (hδ : 0 < δ) :
    ‖∫ t in Ioo (t₀ - 4) (t₀ + 4), ∫ x in B, (unitBallViscousPressureCurve D t).val x *
      projectedCutoffPressureTestComponent u D p t₀ φ θ i (x, t)‖ ≤
      δ * (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo (t₀ - 4) (t₀ + 4),
        ‖D z‖ₑ ^ (2 : ℝ)).toReal +
          (72 * L) ^ 2 * (volume (Ioo (t₀ - 4) (t₀ + 4))).toReal *
            (projectedCutoffSliceEnergy u D p t₀ B φ).toReal / (4 * δ) := by
  let E : ℝ≥0∞ := ∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo (t₀ - 4) (t₀ + 4),
    ‖D z‖ₑ ^ (2 : ℝ)
  let M := projectedCutoffSliceEnergy u D p t₀ B φ
  let T := volume (Ioo (t₀ - 4) (t₀ + 4))
  have hE : E < ⊤ :=
    (lintegral_mono (fun _ ↦ le_add_left le_rfl)).trans_lt
      (hsol.toData.energy_lintegral_lt_top (suitableProjected_unitBall_localBox hdom))
  have hM : M < ⊤ := projectedCutoffSliceEnergy_lt_top hsol hdom hB hBK hb
  have hT : T < ⊤ := by simp [T, Real.volume_Ioo]
  have hc := (suitable_projected_viscous_pressure_cutoff_component_bound
    hsol hdom hB hBK hφ hb hL hgrad hθ hθb i).2
  have hf : 12 * E ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) * ENNReal.ofReal (6 * L) *
      M ^ (1 / 2 : ℝ) ≠ ⊤ := by finiteness [hE.ne, hM.ne, hT.ne]
  have hr := ENNReal.toReal_mono hf hc
  have h6L : 0 ≤ 6 * L := by positivity
  simp only [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal h6L] at hr
  have hh : ‖∫ t in Ioo (t₀ - 4) (t₀ + 4), ∫ x in B,
      (unitBallViscousPressureCurve D t).val x *
        projectedCutoffPressureTestComponent u D p t₀ φ θ i (x, t)‖ ≤
      (72 * L) * Real.sqrt E.toReal * Real.sqrt T.toReal * Real.sqrt M.toReal := by
    exact hr.trans_eq (by simp only [Real.sqrt_eq_rpow]; ring)
  exact hh.trans (projected_viscous_pressure_young ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hδ)

end ActualCutoff

end FluidSingularSets
