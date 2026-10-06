-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallPressureOscillationDecay
public import FluidSingularSets.FullBallRadiusCaccioppoli
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Find

/-!
# Genuine interpolation between shrinking projected-energy radii

The literal projected slice energy and dissipation are monotone before radius
normalization. A geometric sequence therefore controls every intermediate
radius with the true reciprocal shrink factor. Pressure oscillation is not
used in this interpolation.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Every positive radius below the root lies between two genuine successive geometric radii. -/
theorem exists_geometric_radius_bracket {θ r₀ r : ℝ}
    (hθ : 0 < θ) (hθone : θ < 1) (_hr₀ : 0 < r₀) (hr : 0 < r) (hrr₀ : r ≤ r₀) :
    ∃ n : ℕ, θ * (r₀ * θ ^ n) < r ∧ r ≤ r₀ * θ ^ n := by
  have hz : Tendsto (fun n : ℕ ↦ r₀ * θ ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθone)
  have he : ∃ n : ℕ, r₀ * θ ^ n < r := (hz.eventually (eventually_lt_nhds hr)).exists
  have hmin := Nat.find_spec he
  have hn : Nat.find he ≠ 0 := by
    intro hn
    simp only [hn, pow_zero, mul_one] at hmin
    linarith
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine ⟨n, ?_, ?_⟩
  · rw [hn, pow_succ] at hmin
    nlinarith
  · exact le_of_not_gt (Nat.find_min he (by rw [hn]; exact Nat.lt_succ_self n))

/-- True projected Euclidean slice energies are monotone before normalization. -/
theorem fullBallProjectedIterationSliceEnergy_mono_radius
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    fullBallProjectedIterationSliceEnergy u D p a b c r 0 ≤
      fullBallProjectedIterationSliceEnergy u D p a b c R 0 := by
  have ht : Ioo (-(r ^ 2)) 0 ⊆ Ioo (-(R ^ 2)) 0 := by
    intro t ht
    exact ⟨by nlinarith [ht.1], ht.2⟩
  simp only [fullBallProjectedIterationSliceEnergy, zero_sub]
  calc
    _ ≤ essSup (fun t ↦ ∫⁻ x in vec3Ball 0 R, ENNReal.ofReal
        (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c (x, t)) ^ 2))
          (volume.restrict (Ioo (-(r ^ 2)) 0)) := by
      refine essSup_mono_ae ?_
      exact ae_of_all _ fun t ↦ lintegral_mono_set (vec3Ball_mono hrR)
    _ ≤ _ := essSup_mono_measure' (Measure.restrict_mono_set volume ht)

/-- True projected coordinate dissipations are monotone before normalization. -/
theorem fullBallProjectedIterationDissipation_mono_radius
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    fullBallProjectedIterationDissipation u D p a b c r 0 ≤
      fullBallProjectedIterationDissipation u D p a b c R 0 := by
  simp only [fullBallProjectedIterationDissipation, zero_sub]
  exact lintegral_mono_set (centered_backwardCylinder_subset hr hrR)

/-- Literal normalized projected energy interpolates with exactly the reciprocal shrink ratio. -/
theorem fullBallNormalizedProjectedIterationEnergy_radius_le
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {θ r R : ℝ}
    (hθ : 0 < θ) (hR : 0 < R) (hθR : θ * R ≤ r) (hrR : r ≤ R) :
    fullBallNormalizedProjectedIterationEnergy u D p a b c r 0 ≤
      ENNReal.ofReal θ⁻¹ * fullBallNormalizedProjectedIterationEnergy u D p a b c R 0 := by
  have hr : 0 < r := (mul_pos hθ hR).trans_le hθR
  have hc : r⁻¹ ≤ θ⁻¹ * R⁻¹ := by
    have hh := one_div_le_one_div_of_le (mul_pos hθ hR) hθR
    simpa only [one_div, mul_inv_rev, mul_comm] using hh
  have hM := fullBallProjectedIterationSliceEnergy_mono_radius u D p a b c hr.le hrR
  have hD := fullBallProjectedIterationDissipation_mono_radius u D p a b c hr.le hrR
  unfold fullBallNormalizedProjectedIterationEnergy
  calc
    _ ≤ ENNReal.ofReal (θ⁻¹ * R⁻¹) *
        (fullBallProjectedIterationSliceEnergy u D p a b c R 0 +
          fullBallProjectedIterationDissipation u D p a b c R 0) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hc) (add_le_add hM hD)
    _ = _ := by rw [ENNReal.ofReal_mul (inv_nonneg.mpr hθ.le), mul_assoc]

/-- A proved bound on the genuine geometric radii controls every smaller positive radius. -/
theorem fullBallNormalizedProjectedIterationEnergy_le_of_geometric_bounds
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {θ r₀ K : ℝ}
    (hθ : 0 < θ) (hθone : θ < 1) (hr₀ : 0 < r₀)
    (hbound : ∀ n : ℕ, fullBallNormalizedProjectedIterationEnergy u D p a b c
      (r₀ * θ ^ n) 0 ≤ ENNReal.ofReal K) {r : ℝ} (hr : 0 < r) (hrr₀ : r ≤ r₀) :
    fullBallNormalizedProjectedIterationEnergy u D p a b c r 0 ≤
      ENNReal.ofReal (θ⁻¹ * K) := by
  obtain ⟨n, hnlo, hnhi⟩ := exists_geometric_radius_bracket hθ hθone hr₀ hr hrr₀
  calc
    _ ≤ ENNReal.ofReal θ⁻¹ * fullBallNormalizedProjectedIterationEnergy u D p a b c
        (r₀ * θ ^ n) 0 := fullBallNormalizedProjectedIterationEnergy_radius_le u D p a b c
      hθ (mul_pos hr₀ (pow_pos hθ n)) hnlo.le hnhi
    _ ≤ ENNReal.ofReal θ⁻¹ * ENNReal.ofReal K := mul_le_mul' le_rfl (hbound n)
    _ = _ := (ENNReal.ofReal_mul (inv_nonneg.mpr hθ.le)).symm

end FluidSingularSets
