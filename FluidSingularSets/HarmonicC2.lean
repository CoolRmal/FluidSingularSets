-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.LocalHarmonicDerivatives
public import CKN.Foundation.Parabolic.Vec3Norm

/-!
# Actual C² regularity from two genuine Weyl steps

The existing CKN Weyl theorem first constructs a C¹ harmonic representative.
Its actual first derivatives are weakly harmonic and bounded on the inner
ball. A second Weyl application makes each derivative C¹ on a smaller ball.
Continuity identifies those representatives pointwise, giving actual C²
regularity without a higher-regularity premise.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Actual coordinate partials reconstruct the actual Fréchet derivative. -/
theorem fderiv_eq_sum_spatialDeriv (H : Vec3 → ℝ) :
    fderiv ℝ H = fun x ↦ ∑ i : Fin 3,
      spatialDeriv H i x • (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ) := by
  funext x
  ext v
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  calc
    (fderiv ℝ H x) v = (fderiv ℝ H x) (∑ i : Fin 3, v i • basisVec i) := by
      rw [sum_smul_basisVec]
    _ = ∑ i : Fin 3, v i * spatialDeriv H i x := by
      simp [map_sum, spatialDeriv]
    _ = ∑ i : Fin 3, spatialDeriv H i x * v i := by
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Genuine C¹ coordinate partials upgrade a local C¹ function to C². -/
theorem contDiffOn_two_of_partials {U : Set Vec3} {H : Vec3 → ℝ}
    (hU : IsOpen U) (hH : ContDiffOn ℝ (1 : ℕ∞) H U)
    (hpartial : ∀ i : Fin 3, ContDiffOn ℝ (1 : ℕ∞) (spatialDeriv H i) U) :
    ContDiffOn ℝ (2 : ℕ∞) H U := by
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) hU).mpr
  refine ⟨hH.differentiableOn (by norm_num), ?_, ?_⟩
  · intro h
    norm_num at h
  · rw [fderiv_eq_sum_spatialDeriv]
    exact ContDiffOn.sum fun i _ ↦ (hpartial i).smul contDiffOn_const

/-- C¹ almost-everywhere representatives of all partials give genuine local C² regularity. -/
theorem contDiffOn_two_of_ae_partial_representatives {U V : Set Vec3} {H : Vec3 → ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (hH : ContDiffOn ℝ (1 : ℕ∞) H U)
    (G : Fin 3 → Vec3 → ℝ)
    (hG : ∀ i, ContDiffOn ℝ (1 : ℕ∞) (G i) V)
    (hae : ∀ i, spatialDeriv H i =ᵐ[volume.restrict V] G i) :
    ContDiffOn ℝ (2 : ℕ∞) H V := by
  apply contDiffOn_two_of_partials hV (hH.mono hVU)
  intro i
  have hcont : ContinuousOn (spatialDeriv H i) V :=
    ((hH.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply
      continuousOn_const).mono hVU
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq (hae i) hV hcont (hG i).continuousOn
  exact (hG i).congr heq

private theorem harmonicC2_ball_open (x₀ : Vec3) (ρ : ℝ) : IsOpen (euclideanBall x₀ ρ) :=
  isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const

private theorem harmonicC2_ball_subset {x₀ : Vec3} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hle : r ≤ R) : euclideanBall x₀ r ⊆ euclideanBall x₀ R := by
  intro x hx
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr] at hx
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR]
  exact hx.trans_le hle

/-- Genuine distributional harmonicity and integrability give an interior C² representative. -/
theorem exists_weaklyHarmonic_C2_representative {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)))
    (hweak : WeaklyHarmonicOn (euclideanBall x₀ ρ) h) :
    ∃ H : Vec3 → ℝ, ContDiffOn ℝ (2 : ℕ∞) H (euclideanBall x₀ (ρ / 4)) ∧
      h =ᵐ[volume.restrict (euclideanBall x₀ (ρ / 4))] H := by
  obtain ⟨H, hH, hae, _hval, hgrad⟩ := weakly_harmonic_interior_smooth hρ hmem hweak
  have hhalf : 0 < ρ / 2 := by positivity
  have hquarter : 0 < ρ / 4 := by positivity
  have hsubHalf := harmonicC2_ball_subset (x₀ := x₀) hhalf hρ (by linarith : ρ / 2 ≤ ρ)
  have hsubQuarter := harmonicC2_ball_subset (x₀ := x₀) hquarter hhalf
    (by linarith : ρ / 4 ≤ ρ / 2)
  have hhalfOpen := harmonicC2_ball_open x₀ (ρ / 2)
  have hquarterOpen := harmonicC2_ball_open x₀ (ρ / 4)
  have hHweak : WeaklyHarmonicOn (euclideanBall x₀ (ρ / 2)) H :=
    localWeaklyHarmonicOn_congr_ae hae (localWeaklyHarmonicOn_restrict hsubHalf hweak)
  let : IsFiniteMeasure (volume.restrict (euclideanBall x₀ (ρ / 2))) :=
    isFiniteMeasure_restrict.mpr (by
      rw [euclideanBall_eq_vec3Ball hhalf]
      exact volume_vec3Ball_lt_top.ne)
  let B : ℝ := 1728 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
    lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall x₀ ρ))
  have hm : ∀ i : Fin 3, MemLp (spatialDeriv H i) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ (ρ / 2))) := by
    intro i
    have hcont : ContinuousOn (spatialDeriv H i) (euclideanBall x₀ (ρ / 2)) :=
      (hH.continuousOn_fderiv_of_isOpen hhalfOpen (by norm_num)).clm_apply continuousOn_const
    apply MemLp.of_bound (hcont.aestronglyMeasurable hhalfOpen.measurableSet) B
    filter_upwards [ae_restrict_mem hhalfOpen.measurableSet] with x hx
    rw [Real.norm_eq_abs]
    exact (abs_apply_le_vec3EuclideanNorm (classicalGradient H x) i).trans (hgrad x hx)
  have hderiv : ∀ i : Fin 3, ∃ G : Vec3 → ℝ,
      ContDiffOn ℝ (1 : ℕ∞) G (euclideanBall x₀ (ρ / 4)) ∧
        spatialDeriv H i =ᵐ[volume.restrict (euclideanBall x₀ (ρ / 4))] G := by
    intro i
    obtain ⟨G, hG, hGa, _hGval, _hGgrad⟩ := weakly_harmonic_interior_smooth hhalf
      (hm i) (weaklyHarmonicOn_spatialDeriv_of_contDiffOn hhalfOpen hH hHweak i)
    have heq : ρ / 2 / 2 = ρ / 4 := by ring
    rw [heq] at hG hGa
    exact ⟨G, hG, hGa⟩
  choose G hG hGa using hderiv
  refine ⟨H, contDiffOn_two_of_ae_partial_representatives hhalfOpen hquarterOpen
    hsubQuarter hH G hG hGa, ?_⟩
  exact ae_restrict_of_ae_restrict_of_subset hsubQuarter hae

end FluidSingularSets
