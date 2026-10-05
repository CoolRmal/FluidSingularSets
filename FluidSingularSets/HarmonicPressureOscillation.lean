-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallHarmonicRegularity
public import FluidSingularSets.CanonicalForcePressureValues
public import FluidSingularSets.UniformMixedSlices
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import CKN.Foundation.Parabolic.Integration.Average
public import CKN.Foundation.Parabolic.BallDisplays

/-!
# Genuine harmonic pressure oscillation

The actual harmonic derivative estimate controls the difference from the
literal spatial average on a smaller ball. This gives the true radius times
square-root-volume factor in the L² pressure oscillation.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- True uniformly bounded differences control the literal average difference. -/
theorem norm_sub_average_le_of_ae_difference_bound
    {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ] [NeZero μ]
    {f : A → ℝ} (hf : Integrable f μ) (a : ℝ) {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖a - f x‖ ≤ C) : ‖a - average μ f‖ ≤ C := by
  have hm : μ.real univ ≠ 0 := (measureReal_ne_zero_iff).mpr (NeZero.ne (μ univ))
  have heq : a - average μ f = average μ (fun x ↦ a - f x) := by
    change a - average μ f = average μ ((fun _ : A ↦ a) - f)
    rw [average_sub (integrable_const a) hf, average_const]
  rw [heq, average_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr measureReal_nonneg)]
  calc
    _ ≤ (μ.real univ)⁻¹ * (C * μ.real univ) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const hbound)
        (inv_nonneg.mpr measureReal_nonneg)
    _ = C := by field_simp

/-- A genuine local C² function with the actual harmonic gradient bound is Lipschitz inside. -/
theorem fullBallHarmonic_representative_sub_bound {h H : Vec3 → ℝ}
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)))
    (hweak : WeaklyHarmonicOn (vec3Ball 0 1) h)
    (hH : ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 1))
    (hae : h =ᵐ[volume.restrict (vec3Ball 0 1)] H)
    {ρ : ℝ} (hρ : ρ < 1) {x y : Vec3}
    (hx : x ∈ vec3Ball 0 ρ) (hy : y ∈ vec3Ball 0 ρ) :
    ‖H x - H y‖ ≤ 3 * fullBallHarmonicGradientConstant ρ *
      lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)) * ‖x - y‖ := by
  have hρpos : 0 < ρ := by
    have hxn : vec3EuclideanNorm x < ρ := by
      simpa only [mem_vec3Ball, sub_zero] using hx
    exact (vec3EuclideanNorm_nonneg x).trans_lt hxn
  have hconv : Convex ℝ (vec3Ball (0 : Vec3) ρ) := by
    rw [← euclideanBall_eq_vec3Ball hρpos]
    exact convex_euclideanBall hρpos
  have hd : ∀ z ∈ vec3Ball 0 ρ, DifferentiableAt ℝ H z := by
    intro z hz
    exact (hH.contDiffAt ((isOpen_vec3Ball 0 1).mem_nhds
      (vec3Ball_mono hρ.le hz))).differentiableAt (by norm_num)
  have hb : ∀ z ∈ vec3Ball 0 ρ, ‖fderiv ℝ H z‖ ≤
      3 * fullBallHarmonicGradientConstant ρ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)) := by
    intro z hz
    exact (fderiv_norm_le_three_euclidean_classicalGradient z).trans
      (by nlinarith [fullBallHarmonic_representative_gradient_bound hmem hweak hH hae hρ hz])
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hd hb hconv hy hx

/-- The actual harmonic representative differs from its true small-ball average by O(r). -/
theorem fullBallHarmonic_representative_average_sub_bound {h H : Vec3 → ℝ}
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)))
    (hweak : WeaklyHarmonicOn (vec3Ball 0 1) h)
    (hH : ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 1))
    (hae : h =ᵐ[volume.restrict (vec3Ball 0 1)] H)
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρ : ρ < 1)
    {x : Vec3} (hx : x ∈ vec3Ball 0 r) :
    ‖H x - average (volume.restrict (vec3Ball 0 r)) H‖ ≤
      6 * fullBallHarmonicGradientConstant ρ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)) * r := by
  let μ := volume.restrict (vec3Ball (0 : Vec3) r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  let : NeZero μ := ⟨by
    intro he
    have hz := congrArg (fun m : Measure Vec3 ↦ m univ) he
    have hv : volume (vec3Ball (0 : Vec3) r) = 0 := by
      simpa [μ] using hz
    exact (volume_vec3Ball_pos hr).ne' hv⟩
  have hsub : vec3Ball (0 : Vec3) r ⊆ vec3Ball 0 1 :=
    vec3Ball_mono (hrρ.trans hρ.le)
  have hae' : h =ᵐ[μ] H := ae_restrict_of_ae_restrict_of_subset hsub hae
  have hmem' : MemLp H (ENNReal.ofReal (3 / 2 : ℝ)) μ :=
    (hmem.mono_measure (Measure.restrict_mono hsub le_rfl)).ae_eq hae'
  apply norm_sub_average_le_of_ae_difference_bound
    (hmem'.integrable (by norm_num))
  filter_upwards [ae_restrict_mem (isOpen_vec3Ball 0 r).measurableSet] with y hy
  have hb := fullBallHarmonic_representative_sub_bound hmem hweak hH hae hρ
    (vec3Ball_mono hrρ hx) (vec3Ball_mono hrρ hy)
  have hxy : ‖x - y‖ ≤ 2 * r := by
    have hxn : ‖x‖ < r := (norm_le_vec3EuclideanNorm x).trans_lt (by
      simpa only [mem_vec3Ball, sub_zero] using hx)
    have hyn : ‖y‖ < r := (norm_le_vec3EuclideanNorm y).trans_lt (by
      simpa only [mem_vec3Ball, sub_zero] using hy)
    exact (norm_sub_le x y).trans (by linarith)
  have hC := fullBallHarmonicGradientConstant_nonneg hρ
  have hN : 0 ≤ lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball 0 1)) := lpNorm_nonneg
  exact hb.trans ((mul_le_mul_of_nonneg_left hxy (by positivity)).trans_eq (by ring))

/-- The actual harmonic pressure oscillation has its genuine L² radius-volume bound. -/
theorem fullBallHarmonic_centered_eLpNorm_two_le {h : Vec3 → ℝ}
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)))
    (hweak : WeaklyHarmonicOn (vec3Ball 0 1) h)
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρ : ρ < 1) :
    eLpNorm (fun x ↦ h x - average (volume.restrict (vec3Ball 0 r)) h) 2
        (volume.restrict (vec3Ball 0 r)) ≤
      ENNReal.ofReal (6 * fullBallHarmonicGradientConstant ρ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)) * r) *
          volume (vec3Ball 0 r) ^ (1 / 2 : ℝ) := by
  obtain ⟨H, hH, hae, _⟩ := exists_fullBall_weaklyHarmonic_C2_representative hmem hweak
  have hsub : vec3Ball (0 : Vec3) r ⊆ vec3Ball 0 1 :=
    vec3Ball_mono (hrρ.trans hρ.le)
  have hae' : h =ᵐ[volume.restrict (vec3Ball 0 r)] H :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have hav := average_congr hae'
  have hC := fullBallHarmonicGradientConstant_nonneg hρ
  have hN : 0 ≤ lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball 0 1)) := lpNorm_nonneg
  have hb : ∀ᵐ x ∂volume.restrict (vec3Ball 0 r),
      ‖h x - average (volume.restrict (vec3Ball 0 r)) h‖ ≤
        6 * fullBallHarmonicGradientConstant ρ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)) * r := by
    filter_upwards [hae', ae_restrict_mem (isOpen_vec3Ball 0 r).measurableSet] with x hx hxb
    rw [hx, hav]
    exact fullBallHarmonic_representative_average_sub_bound hmem hweak hH hae hr hrρ hρ hxb
  have hbound := eLpNorm_sub_le_uniform_bound (p := 2) (by norm_num) (by norm_num)
    (hmem.mono_measure (Measure.restrict_mono hsub le_rfl)).aestronglyMeasurable
    aestronglyMeasurable_const (by positivity) hb
  have heq : (h - fun _ ↦ average (volume.restrict (vec3Ball 0 r)) h) =
      fun x ↦ h x - average (volume.restrict (vec3Ball 0 r)) h := rfl
  rw [heq] at hbound
  simpa only [Measure.restrict_apply_univ, ENNReal.toReal_ofNat] using hbound

/-- The true finite-volume L² to L³ᐟ² pressure seminorm comparison. -/
theorem unitBall_threeHalves_eLpNorm_le_two {h : Vec3 → ℝ}
    (hmem : MemLp h 2 (volume.restrict (vec3Ball 0 1))) :
    eLpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)) ≤
      eLpNorm h 2 (volume.restrict (vec3Ball 0 1)) *
        volume (vec3Ball 0 1) ^ (1 / 6 : ℝ) := by
  have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := 2) (by norm_num) hmem.aestronglyMeasurable
  norm_num only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 3 / 2),
    ENNReal.toReal_ofNat, Measure.restrict_apply_univ] at hb
  exact hb

/-- Actual L² harmonic pressure has the genuine centered L² oscillation bound. -/
theorem fullBallHarmonic_centered_eLpNorm_two_le_of_memLp_two {h : Vec3 → ℝ}
    (hmem : MemLp h 2 (volume.restrict (vec3Ball 0 1)))
    (hweak : WeaklyHarmonicOn (vec3Ball 0 1) h)
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρ : ρ < 1) :
    eLpNorm (fun x ↦ h x - average (volume.restrict (vec3Ball 0 r)) h) 2
        (volume.restrict (vec3Ball 0 r)) ≤
      ENNReal.ofReal (6 * fullBallHarmonicGradientConstant ρ * r) *
        eLpNorm h 2 (volume.restrict (vec3Ball 0 1)) *
          volume (vec3Ball 0 1) ^ (1 / 6 : ℝ) *
            volume (vec3Ball 0 r) ^ (1 / 2 : ℝ) := by
  have hfinite : IsFiniteMeasure (volume.restrict (vec3Ball (0 : Vec3) 1)) :=
    isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  have h15 : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball 0 1)) := hmem.mono_exponent (by norm_num)
  have hb := fullBallHarmonic_centered_eLpNorm_two_le h15 hweak hr hrρ hρ
  have hc := fullBallHarmonicGradientConstant_nonneg hρ
  have he : 6 * fullBallHarmonicGradientConstant ρ *
      lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)) * r =
      (6 * fullBallHarmonicGradientConstant ρ * r) *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball 0 1)) := by ring
  rw [he, ENNReal.ofReal_mul (by positivity), lpNorm,
    ENNReal.ofReal_toReal h15.eLpNorm_ne_top] at hb
  exact hb.trans ((mul_le_mul' (mul_le_mul' le_rfl
    (unitBall_threeHalves_eLpNorm_le_two hmem)) le_rfl).trans_eq (by ring))

/-- The exact three-dimensional radius-volume factor is the power r⁵ᐟ². -/
theorem vec3Ball_radius_sqrt_volume_eq (r : ℝ) :
    ENNReal.ofReal r * volume (vec3Ball 0 r) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal r ^ (5 / 2 : ℝ) *
        ENNReal.ofReal (Real.pi * 4 / 3) ^ (1 / 2 : ℝ) := by
  rw [volume_vec3Ball_eq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [← ENNReal.rpow_natCast (ENNReal.ofReal r) 3, ← ENNReal.rpow_mul]
  rw [show (5 / 2 : ℝ) = 1 + 3 * (1 / 2 : ℝ) by norm_num,
    ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num), ENNReal.rpow_one]
  ring_nf

/-- The finite dimensional constant in the actual harmonic pressure decay bound. -/
def fullBallHarmonicOscillationConstant (ρ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (6 * fullBallHarmonicGradientConstant ρ) *
    volume (vec3Ball 0 1) ^ (1 / 6 : ℝ) *
      ENNReal.ofReal (Real.pi * 4 / 3) ^ (1 / 2 : ℝ)

/-- The actual harmonic pressure has the true r⁵ᐟ² centered L² decay. -/
theorem fullBallHarmonic_centered_eLpNorm_two_decay {h : Vec3 → ℝ}
    (hmem : MemLp h 2 (volume.restrict (vec3Ball 0 1)))
    (hweak : WeaklyHarmonicOn (vec3Ball 0 1) h)
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρ : ρ < 1) :
    eLpNorm (fun x ↦ h x - average (volume.restrict (vec3Ball 0 r)) h) 2
        (volume.restrict (vec3Ball 0 r)) ≤
      fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal r ^ (5 / 2 : ℝ) *
        eLpNorm h 2 (volume.restrict (vec3Ball 0 1)) := by
  have hb := fullBallHarmonic_centered_eLpNorm_two_le_of_memLp_two hmem hweak hr hrρ hρ
  have hc := fullBallHarmonicGradientConstant_nonneg hρ
  rw [ENNReal.ofReal_mul (by positivity)] at hb
  refine hb.trans_eq ?_
  calc
    _ = ENNReal.ofReal (6 * fullBallHarmonicGradientConstant ρ) *
        volume (vec3Ball 0 1) ^ (1 / 6 : ℝ) *
        (ENNReal.ofReal r * volume (vec3Ball 0 r) ^ (1 / 2 : ℝ)) *
        eLpNorm h 2 (volume.restrict (vec3Ball 0 1)) := by ring
    _ = _ := by rw [vec3Ball_radius_sqrt_volume_eq]; simp only
               [fullBallHarmonicOscillationConstant]; ring

end FluidSingularSets
