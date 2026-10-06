-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallPressureOscillationMoment
public import FluidSingularSets.LocalBoxEnergyForces
public import FluidSingularSets.FullBallProjectedSixControl
public import FluidSingularSets.FullBallProjectedGradientControl
public import FluidSingularSets.FullBallVelocityMomentFinite

/-!
# Actual all-scale projected pressure quantities on a native suitable box

The original unit-ball Stokes projection is fixed. The scaled energy contains
the literal Euclidean projected-velocity square supremum, the literal coordinate
gradient-square dissipation, and the centered convective-pressure L¹-time/L²-space
oscillation to power 3/2. The projected fields retain their original force
primitive parameters.

Actual full-ball weak Sobolev gives quartic velocity slices on the same suitable
box. Thus genuine local pressure decay needs no doubled spatial carrier.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Literal projected Euclidean slice energy on the smaller backward time interval. -/
def fullBallProjectedIterationSliceEnergy
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c r τ : ℝ) : ℝ≥0∞ :=
  essSup (fun t ↦ ∫⁻ x in vec3Ball 0 r, ENNReal.ofReal
    (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c (x, t)) ^ 2))
      (volume.restrict (Ioo (τ - r ^ 2) τ))

/-- Literal coordinate dissipation of the same projected field and smaller cylinder. -/
def fullBallProjectedIterationDissipation
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c r τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (τ - r ^ 2) τ,
    ENNReal.ofReal (projectedGradientSquare
      (fullBallProjectedVelocityDerivativeAmbient u D p a b c z))

/-- The genuinely scale-normalized projected energy, with the fixed original projection. -/
def fullBallNormalizedProjectedIterationEnergy
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c r τ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal r⁻¹ * (fullBallProjectedIterationSliceEnergy u D p a b c r τ +
    fullBallProjectedIterationDissipation u D p a b c r τ)

/-- Actual scale-normalized centered convective-pressure oscillation. -/
def fullBallNormalizedConvectiveOscillation (u : ParabolicPoint → Vec3)
    (r τ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (r ^ (-3 / 2 : ℝ)) *
    unitBallConvectiveOscillationMoment u r (Ioo (τ - r ^ 2) τ)

/-- The actual quantity for the projected endpoint energy and pressure iteration. -/
def fullBallEndpointIterationQuantity
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c r τ : ℝ) : ℝ≥0∞ :=
  fullBallNormalizedProjectedIterationEnergy u D p a b c r τ +
    fullBallNormalizedConvectiveOscillation u r τ ^ (3 / 2 : ℝ)

/-- Actual native suitable data give a genuine full time set for local pressure decay. -/
theorem suitable_unitBallConvectivePressureCurve_centered_decay_four_ae_localBox
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J)
    {r s ρ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s) (hsρ : s ≤ ρ) (hρ : ρ < 1) :
    ∀ᵐ t ∂volume.restrict J,
      let P := (unitBallConvectivePressureCurve u t :
        Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))
      let γ := fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal s ^ (5 / 2 : ℝ)
      eLpNorm (fun y ↦ P y - average (volume.restrict (vec3Ball 0 (r * s))) P) 2
          (volume.restrict (vec3Ball 0 (r * s))) ≤
        (24 + 12 * γ) * eLpNorm (fun y ↦ u (y, t)) 4
          (volume.restrict (vec3Ball 0 r)) ^ 2 +
        γ * eLpNorm (fun y ↦ P y - average (volume.restrict (vec3Ball 0 r)) P) 2
          (volume.restrict (vec3Ball 0 r)) := by
  filter_upwards [suitable_unitBall_memLp_four_ae_localBox hsol hbox] with t ht
  have hb := ballNonlinearPressure_centered_local_decay_four 0 zero_lt_one hr hr1
    (fun y ↦ u (y, t)) ht hs hsρ hρ
  rw [← ballConvectivePressureCurve_eq 0 zero_lt_one u t ht,
    ballConvectivePressureCurve_zero_one] at hb
  exact hb

/-- Genuine same-box pressure decay integrates on nested time sets. -/
theorem suitable_unitBallConvectiveOscillationMoment_local_decay_localBox
    {Ω : Set Vec3} {I J J' : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) (hJ : J' ⊆ J)
    {r s ρ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s) (hsρ : s ≤ ρ) (hρ : ρ < 1) :
    let γ := fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal s ^ (5 / 2 : ℝ)
    unitBallConvectiveOscillationMoment u (r * s) J' ≤
      (24 + 12 * γ) * unitBallVelocityFourSquareMoment u r J +
        γ * unitBallConvectiveOscillationMoment u r J := by
  let γ := fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal s ^ (5 / 2 : ℝ)
  let P : ℝ → Lp ℝ 2 (volume.restrict (vec3Ball 0 1)) :=
    fun t ↦ unitBallConvectivePressureCurve u t
  have hu : AEStronglyMeasurable u
      ((volume.restrict (vec3Ball 0 1)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hsol.toData.aestronglyMeasurable_velocity hbox
  have hP : AEStronglyMeasurable P (volume.restrict J) :=
    unitBallMeanZeroL2.toSubmodule.subtypeL.continuous.comp_aestronglyMeasurable
      (unitBallConvectivePressureCurve_aestronglyMeasurable hu)
  have hm := (ballCenteredPressureL_seminorm_aemeasurable 0 hr1 hP).mono_measure
    (Measure.restrict_mono hJ le_rfl)
  have hγ : γ ≠ ⊤ := by
    dsimp [γ, fullBallHarmonicOscillationConstant]
    finiteness [(volume_vec3Ball_lt_top (x := 0) (r := 1)).ne]
  have hcoeff : (24 + 12 * γ : ℝ≥0∞) ≠ ⊤ := by finiteness
  have hpoint := (suitable_unitBallConvectivePressureCurve_centered_decay_four_ae_localBox
    hsol hbox hr hr1 hs hsρ hρ).filter_mono
      (ae_mono (Measure.restrict_mono hJ le_rfl))
  calc
    _ ≤ ∫⁻ t in J', (24 + 12 * γ) * eLpNorm (fun y ↦ u (y, t)) 4
          (volume.restrict (vec3Ball 0 r)) ^ 2 +
        γ * eLpNorm (fun y ↦ P t y - average (volume.restrict (vec3Ball 0 r)) (P t)) 2
          (volume.restrict (vec3Ball 0 r)) := lintegral_mono_ae hpoint
    _ = (24 + 12 * γ) * unitBallVelocityFourSquareMoment u r J' +
        γ * unitBallConvectiveOscillationMoment u r J' := by
      rw [lintegral_add_right' _ (hm.const_mul γ),
        lintegral_const_mul' _ _ hcoeff, lintegral_const_mul' _ _ hγ]
      rfl
    _ ≤ _ := add_le_add
      (mul_le_mul' le_rfl (lintegral_mono_set hJ))
      (mul_le_mul' le_rfl (lintegral_mono_set hJ))

/-- Same-box actual pressure decay holds on every sufficiently small backward cylinder. -/
theorem suitable_unitBallConvectiveOscillationMoment_backward_decay_localBox
    {Ω : Set Vec3} {I : Set ℝ} {q τ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    {r s ρ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s) (hsρ : s ≤ ρ) (hρ : ρ < 1)
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (τ - r ^ 2) τ)) :
    let γ := fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal s ^ (5 / 2 : ℝ)
    unitBallConvectiveOscillationMoment u (r * s) (Ioo (τ - (r * s) ^ 2) τ) ≤
      (24 + 12 * γ) * unitBallVelocityFourSquareMoment u r (Ioo (τ - r ^ 2) τ) +
        γ * unitBallConvectiveOscillationMoment u r (Ioo (τ - r ^ 2) τ) := by
  apply suitable_unitBallConvectiveOscillationMoment_local_decay_localBox
    hsol hbox _ hr hr1 hs hsρ hρ
  have hrs : r * s ≤ r := by nlinarith
  have hsquare : (r * s) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (mul_pos hr hs).le hrs 2
  intro t ht
  exact ⟨by linarith [ht.1], ht.2⟩

end FluidSingularSets
