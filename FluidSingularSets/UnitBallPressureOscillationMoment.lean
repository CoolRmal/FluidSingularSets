-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallPressureMixedBounds
public import CKN.Foundation.Sobolev.WeakGradientGluingTPressureMean

/-!
# Actual centered pressure decay moments

The large-radius spatial mean is removed before harmonic decay, so the
remainder estimate depends on centered large-radius pressure. The genuine
local Stokes pressure source then gives the actual velocity L⁴ square cost.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A genuine harmonic pressure remainder controls centered pressure at both radii. -/
theorem ball_centered_pressure_decay_of_harmonic_difference
    (x : Vec3) {r : ℝ} (hr : 0 < r) {q p : Vec3 → ℝ}
    (hq : MemLp q 2 (volume.restrict (vec3Ball x r)))
    (hp : MemLp p 2 (volume.restrict (vec3Ball x r)))
    (hH : WeaklyHarmonicOn (vec3Ball x r) (q - p))
    {s ρ : ℝ} (hs : 0 < s) (hsρ : s ≤ ρ) (hρ : ρ < 1) :
    eLpNorm (fun y ↦ q y - average (volume.restrict (vec3Ball x (r * s))) q) 2
        (volume.restrict (vec3Ball x (r * s))) ≤
      2 * eLpNorm p 2 (volume.restrict (vec3Ball x r)) +
        fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal s ^ (5 / 2 : ℝ) *
          (eLpNorm (fun y ↦ q y - average (volume.restrict (vec3Ball x r)) q) 2
              (volume.restrict (vec3Ball x r)) +
            eLpNorm p 2 (volume.restrict (vec3Ball x r))) := by
  let ν := volume.restrict (vec3Ball x r)
  let μ := volume.restrict (vec3Ball x (r * s))
  let a := average ν q
  let qc : Vec3 → ℝ := fun y ↦ q y - a
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  have hsmall : vec3Ball x (r * s) ⊆ vec3Ball x r := vec3Ball_mono (by nlinarith)
  have hμ : μ univ ≠ 0 := by
    simpa only [μ, Measure.restrict_apply_univ] using (volume_vec3Ball_pos (mul_pos hr hs)).ne'
  let : NeZero μ := ⟨fun hm ↦ hμ (by rw [hm]; simp)⟩
  have hqc : MemLp qc 2 ν := hq.sub (memLp_const a)
  have hqc' := hqc.mono_measure (Measure.restrict_mono hsmall le_rfl)
  have hp' := hp.mono_measure (Measure.restrict_mono hsmall le_rfl)
  have hq' := hq.mono_measure (Measure.restrict_mono hsmall le_rfl)
  have havqc : average μ qc = average μ q - a := by
    change average μ (q - fun _ ↦ a) = _
    rw [average_sub (hq'.integrable (by norm_num)) (integrable_const a), average_const]
  have hloc : LocallyIntegrableOn (q - p) (vec3Ball x r) volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((hq.sub hp).locallyIntegrable (by norm_num))
  have hHc : WeaklyHarmonicOn (vec3Ball x r) (qc - p) := by
    have hw := hH.sub_const (isOpen_vec3Ball x r) hloc a
    have he : (fun y ↦ (q - p) y - a) = qc - p := by
      funext y
      simp only [Pi.sub_apply, qc]
      ring
    rw [he] at hw
    exact hw
  have hav : average μ (qc - p) = average μ qc - average μ p :=
    average_sub (hqc'.integrable (by norm_num)) (hp'.integrable (by norm_num))
  have hsplit : (fun y ↦ q y - average μ q) =
      (fun y ↦ p y - average μ p) + (fun y ↦ (qc - p) y - average μ (qc - p)) := by
    funext y
    simp only [Pi.add_apply, Pi.sub_apply, hav, havqc, qc]
    ring
  have hcenter : eLpNorm (fun y ↦ p y - average μ p) 2 μ ≤ 2 * eLpNorm p 2 ν := by
    have hb := centered_eLpNorm_le_two hμ hp'.aestronglyMeasurable
      (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
    norm_num only [ENNReal.ofReal_ofNat] at hb
    exact hb.trans (mul_le_mul' le_rfl
      (eLpNorm_mono_measure p (Measure.restrict_mono hsmall le_rfl)))
  have hdecay := ballHarmonic_centered_eLpNorm_two_decay x hr (hqc.sub hp) hHc hs hsρ hρ
  have hdiff : eLpNorm (qc - p) 2 ν ≤ eLpNorm qc 2 ν + eLpNorm p 2 ν :=
    eLpNorm_sub_le (p := 2) (by norm_num)
  change eLpNorm (fun y ↦ q y - average μ q) 2 μ ≤ _
  rw [hsplit]
  exact (eLpNorm_add_le (p := 2) (by norm_num)).trans
    (add_le_add hcenter (hdecay.trans (mul_le_mul' le_rfl hdiff)))

/-- Actual nonlinear pressure decay uses centered large-radius pressure and the
local L⁴ source. -/
theorem ballNonlinearPressure_centered_local_decay_four
    (x : Vec3) {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R)
    (u : Vec3 → Vec3) (hu : MemLp u 4 (volume.restrict (vec3Ball x R)))
    {s ρ : ℝ} (hs : 0 < s) (hsρ : s ≤ ρ) (hρ : ρ < 1) :
    let q := ballNonlinearPressure x hR u hu
    let γ := fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal s ^ (5 / 2 : ℝ)
    eLpNorm (fun y ↦ q y - average (volume.restrict (vec3Ball x (r * s))) q) 2
        (volume.restrict (vec3Ball x (r * s))) ≤
      (24 + 12 * γ) * eLpNorm u 4 (volume.restrict (vec3Ball x r)) ^ 2 +
        γ * eLpNorm (fun y ↦ q y - average (volume.restrict (vec3Ball x r)) q) 2
          (volume.restrict (vec3Ball x r)) := by
  let q : Vec3 → ℝ := ballNonlinearPressure x hR u hu
  let hur := hu.mono_measure (Measure.restrict_mono (vec3Ball_mono hrR) le_rfl)
  let p : Vec3 → ℝ := ballNonlinearPressure x hr u hur
  have hq := (Lp.memLp (ballNonlinearPressure x hR u hu)).mono_measure
    (Measure.restrict_mono (vec3Ball_mono hrR) le_rfl)
  have hp := Lp.memLp (ballNonlinearPressure x hr u hur)
  have hb := ball_centered_pressure_decay_of_harmonic_difference x hr hq hp
    (ballNonlinearPressure_local_difference_weaklyHarmonic x hR hr hrR u hu) hs hsρ hρ
  have hsource := ballNonlinearPressure_eLpNorm_two_le x hr u hur
  exact hb.trans ((add_le_add (mul_le_mul' le_rfl hsource)
    (mul_le_mul' le_rfl (add_le_add le_rfl hsource))).trans_eq (by ring))

/-- The actual native convective pressure has centered decay on one suitable full time set. -/
theorem suitable_unitBallConvectivePressureCurve_centered_local_decay_four_ae
    {Ω : Set Vec3} {I J : Set ℝ} {a : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I a u D p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J)
    {r s ρ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s) (hsρ : s ≤ ρ) (hρ : ρ < 1) :
    ∀ᵐ t ∂volume.restrict J,
      let q := (unitBallConvectivePressureCurve u t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))
      let γ := fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal s ^ (5 / 2 : ℝ)
      eLpNorm (fun y ↦ q y - average (volume.restrict (vec3Ball 0 (r * s))) q) 2
          (volume.restrict (vec3Ball 0 (r * s))) ≤
        (24 + 12 * γ) * eLpNorm (fun y ↦ u (y, t)) 4 (volume.restrict (vec3Ball 0 r)) ^ 2 +
          γ * eLpNorm (fun y ↦ q y - average (volume.restrict (vec3Ball 0 r)) q) 2
            (volume.restrict (vec3Ball 0 r)) := by
  have hbox' : localBox Ω I (euclideanBall 0 (2 * 1)) J := by simpa only [mul_one] using hbox
  filter_upwards [suitable_ball_memLp_four_ae hsol 0 zero_lt_one hbox'] with t ht
  have hb := ballNonlinearPressure_centered_local_decay_four 0 zero_lt_one hr hr1
    (fun y ↦ u (y, t)) ht hs hsρ hρ
  rw [← ballConvectivePressureCurve_eq 0 zero_lt_one u t ht,
    ballConvectivePressureCurve_zero_one] at hb
  exact hb

/-- The actual nonlinear pressure oscillation integrated on a time set. -/
def unitBallConvectiveOscillationMoment (u : ParabolicPoint → Vec3) (r : ℝ)
    (J : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ t in J, eLpNorm
    (fun y ↦ (unitBallConvectivePressureCurve u t :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) y -
        average (volume.restrict (vec3Ball 0 r))
          (unitBallConvectivePressureCurve u t :
            Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))) 2
    (volume.restrict (vec3Ball 0 r))

/-- The actual time-integrated spatial L⁴ square source on a ball. -/
def unitBallVelocityFourSquareMoment (u : ParabolicPoint → Vec3) (r : ℝ)
    (J : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ t in J, eLpNorm (fun y ↦ u (y, t)) 4 (volume.restrict (vec3Ball 0 r)) ^ 2

/-- Actual suitable data give the centered decay moment on nested time sets. -/
theorem suitable_unitBallConvectiveOscillationMoment_local_decay
    {Ω : Set Vec3} {I J J' : Set ℝ} {a : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I a u D p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) (hJ : J' ⊆ J)
    {r s ρ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s) (hsρ : s ≤ ρ) (hρ : ρ < 1) :
    let γ := fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal s ^ (5 / 2 : ℝ)
    unitBallConvectiveOscillationMoment u (r * s) J' ≤
      (24 + 12 * γ) * unitBallVelocityFourSquareMoment u r J +
        γ * unitBallConvectiveOscillationMoment u r J := by
  let γ := fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal s ^ (5 / 2 : ℝ)
  let P : ℝ → Lp ℝ 2 (volume.restrict (vec3Ball 0 1)) :=
    fun t ↦ unitBallConvectivePressureCurve u t
  have hP : AEStronglyMeasurable P (volume.restrict J) :=
    unitBallMeanZeroL2.toSubmodule.subtypeL.continuous.comp_aestronglyMeasurable
      (suitable_convectivePressureCurve_aestronglyMeasurable hsol hbox)
  have hm := (ballCenteredPressureL_seminorm_aemeasurable 0 hr1 hP).mono_measure
    (Measure.restrict_mono hJ le_rfl)
  have hγ : γ ≠ ⊤ := by
    dsimp [γ, fullBallHarmonicOscillationConstant]
    finiteness [(volume_vec3Ball_lt_top (x := 0) (r := 1)).ne]
  have hcoeff : (24 + 12 * γ : ℝ≥0∞) ≠ ⊤ := by finiteness
  have hpoint := (suitable_unitBallConvectivePressureCurve_centered_local_decay_four_ae
    hsol hbox hr hr1 hs hsρ hρ).filter_mono
      (ae_mono (Measure.restrict_mono hJ le_rfl))
  change unitBallConvectiveOscillationMoment u (r * s) J' ≤ _
  calc
    _ ≤ ∫⁻ t in J',
        (24 + 12 * γ) * eLpNorm (fun y ↦ u (y, t)) 4
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

/-- The genuine pressure estimate integrates on nested backward parabolic cylinders. -/
theorem suitable_unitBallConvectiveOscillationMoment_backward_decay
    {Ω : Set Vec3} {I : Set ℝ} {a τ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I a u D p f)
    {r s ρ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s) (hsρ : s ≤ ρ) (hρ : ρ < 1)
    (hbox : localBox Ω I (euclideanBall 0 2) (Ioo (τ - r ^ 2) τ)) :
    let γ := fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal s ^ (5 / 2 : ℝ)
    unitBallConvectiveOscillationMoment u (r * s) (Ioo (τ - (r * s) ^ 2) τ) ≤
      (24 + 12 * γ) * unitBallVelocityFourSquareMoment u r (Ioo (τ - r ^ 2) τ) +
        γ * unitBallConvectiveOscillationMoment u r (Ioo (τ - r ^ 2) τ) := by
  apply suitable_unitBallConvectiveOscillationMoment_local_decay hsol hbox _ hr hr1 hs hsρ hρ
  have hrs : r * s ≤ r := by nlinarith
  have hsquare : (r * s) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (mul_pos hr hs).le hrs 2
  intro t ht
  exact ⟨by linarith [ht.1], ht.2⟩

/-- The genuine Weyl constant admits a universal strict pressure-oscillation contraction. -/
theorem exists_fullBallHarmonicOscillation_contraction :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧
      fullBallHarmonicOscillationConstant (1 / 2) * ENNReal.ofReal s ^ (5 / 2 : ℝ) ≤
        (1 / 4 : ℝ≥0∞) := by
  let C := fullBallHarmonicOscillationConstant (1 / 2)
  have hC : C ≠ ⊤ := by
    dsimp [C, fullBallHarmonicOscillationConstant]
    finiteness [(volume_vec3Ball_lt_top (x := 0) (r := 1)).ne]
  let s := (4 * (C.toReal + 1))⁻¹
  have hden : 0 < 4 * (C.toReal + 1) := by positivity
  have hs : 0 < s := inv_pos.mpr hden
  have he : 4 * (C.toReal + 1) * s = 1 := mul_inv_cancel₀ hden.ne'
  have hprod : 0 ≤ C.toReal * s := mul_nonneg ENNReal.toReal_nonneg hs.le
  have hsquarter : s ≤ 1 / 4 := by nlinarith
  have hCs : C.toReal * s ≤ 1 / 4 := by nlinarith
  refine ⟨s, hs, by linarith, ?_⟩
  have hpow : s ^ (5 / 2 : ℝ) ≤ s :=
    Real.rpow_le_self_of_le_one hs.le (by linarith) (by norm_num)
  calc
    C * ENNReal.ofReal s ^ (5 / 2 : ℝ) =
        ENNReal.ofReal (C.toReal * s ^ (5 / 2 : ℝ)) := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hC, ENNReal.ofReal_rpow_of_nonneg hs.le (by norm_num)]
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) := ENNReal.ofReal_le_ofReal
      ((mul_le_mul_of_nonneg_left hpow ENNReal.toReal_nonneg).trans hCs)
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
        ENNReal.ofReal_ofNat, one_div]

/-- The actual nonlinear pressure moment contracts with a universal ratio and source constant 27. -/
theorem suitable_unitBallConvectiveOscillationMoment_backward_contraction
    {Ω : Set Vec3} {I : Set ℝ} {a τ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I a u D p f) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      localBox Ω I (euclideanBall 0 2) (Ioo (τ - r ^ 2) τ) →
      unitBallConvectiveOscillationMoment u (r * s) (Ioo (τ - (r * s) ^ 2) τ) ≤
        27 * unitBallVelocityFourSquareMoment u r (Ioo (τ - r ^ 2) τ) +
          (1 / 4) * unitBallConvectiveOscillationMoment u r (Ioo (τ - r ^ 2) τ) := by
  obtain ⟨s, hs, hsρ, hγ⟩ := exists_fullBallHarmonicOscillation_contraction
  refine ⟨s, hs, hsρ, fun r hr hr1 hbox ↦ ?_⟩
  have hb := suitable_unitBallConvectiveOscillationMoment_backward_decay
    hsol hr hr1 hs hsρ (by norm_num : (1 / 2 : ℝ) < 1) hbox
  apply hb.trans
  apply add_le_add
  · apply mul_le_mul' _ le_rfl
    have hnum : (12 : ℝ≥0∞) * (1 / 4) + 24 = 27 := by
      rw [show (12 : ℝ≥0∞) = 3 * 4 by norm_num, one_div, mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
      norm_num
    exact (add_le_add (le_refl (24 : ℝ≥0∞))
      (mul_le_mul' (le_refl (12 : ℝ≥0∞)) hγ)).trans_eq
      (by rw [add_comm]; exact hnum)
  · exact mul_le_mul' hγ le_rfl

/-- Actual spatial L⁶ slices control the local time-integrated L⁴ square source. -/
theorem unitBallVelocityFourSquareMoment_le_six_moment
    (u : ParabolicPoint → Vec3) (r : ℝ) (J : Set ℝ)
    (hu : ∀ᵐ t ∂volume.restrict J,
      MemLp (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball 0 r))) :
    unitBallVelocityFourSquareMoment u r J ≤
      volume (vec3Ball 0 r) ^ (1 / 6 : ℝ) *
        ∫⁻ t in J, eLpNorm (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball 0 r)) ^ 2 := by
  have hp := hu.mono fun t ht ↦ ball_velocity_four_squared_eLpNorm_le_six 0 r _ ht
  exact (lintegral_mono_ae hp).trans_eq (lintegral_const_mul' _ _
    (by finiteness [(volume_vec3Ball_lt_top (x := 0) (r := r)).ne]))

/-- The true endpoint velocity cost supplies the source in the pressure contraction. -/
theorem suitable_unitBallConvectiveOscillationMoment_backward_contraction_six
    {Ω : Set Vec3} {I : Set ℝ} {a τ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I a u D p f) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      localBox Ω I (euclideanBall 0 2) (Ioo (τ - r ^ 2) τ) →
      unitBallConvectiveOscillationMoment u (r * s) (Ioo (τ - (r * s) ^ 2) τ) ≤
        27 * volume (vec3Ball 0 r) ^ (1 / 6 : ℝ) *
          (∫⁻ t in Ioo (τ - r ^ 2) τ, eLpNorm (fun y ↦ u (y, t)) 6
            (volume.restrict (vec3Ball 0 r)) ^ 2) +
          (1 / 4) * unitBallConvectiveOscillationMoment u r (Ioo (τ - r ^ 2) τ) := by
  obtain ⟨s, hs, hsρ, hdecay⟩ :=
    suitable_unitBallConvectiveOscillationMoment_backward_contraction hsol
  refine ⟨s, hs, hsρ, fun r hr hr1 hbox ↦ ?_⟩
  have hbox' : localBox Ω I (euclideanBall 0 (2 * 1)) (Ioo (τ - r ^ 2) τ) := by
    simpa only [mul_one] using hbox
  have hus := (suitable_ball_memLp_six_ae hsol 0 zero_lt_one hbox').mono fun t ht ↦
    ht.mono_measure (Measure.restrict_mono (vec3Ball_mono hr1) le_rfl)
  have hb := unitBallVelocityFourSquareMoment_le_six_moment u r (Ioo (τ - r ^ 2) τ) hus
  exact (hdecay r hr hr1 hbox).trans
    (add_le_add ((mul_le_mul' (le_refl (27 : ℝ≥0∞)) hb).trans_eq
      (by rw [mul_assoc])) le_rfl)

end FluidSingularSets
