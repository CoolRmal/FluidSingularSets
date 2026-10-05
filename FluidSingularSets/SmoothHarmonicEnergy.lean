-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.AcceleratedEnergy
public import FluidSingularSets.ProjectedEnergyAlgebra
public import CKN.Foundation.IntegrationByParts

/-!
# Genuine compact-test identities for smooth harmonic corrections

Classical space-time integration by parts cancels the time derivative and
spatial Dirichlet terms of an actual smooth correction. Only harmonicity on
the support of the energy test is required. These identities are the smooth
analytic part of the projected-energy expansion.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance (priority := high) : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd

/-- The actual spatial product derivative of two smooth fields is additive. -/
theorem spatialPartial_add_smooth {f g : Vec3 × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial (fun w ↦ f w + g w) i z = spatialPartial f i z + spatialPartial g i z := by
  have hfs : DifferentiableAt ℝ (fun x : Vec3 ↦ f (x, z.2)) z.1 :=
    (hf.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) |>.differentiableAt
  have hgs : DifferentiableAt ℝ (fun x : Vec3 ↦ g (x, z.2)) z.1 :=
    (hg.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) |>.differentiableAt
  simp only [spatialPartial, fderiv_fun_add hfs hgs, add_apply]

/-- The actual second spatial derivative of a smooth square. -/
theorem spatialSecondPartial_square_smooth {f : Vec3 × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) (z : Vec3 × ℝ) :
    spatialSecondPartial (fun w ↦ f w ^ 2) i i z =
      2 * spatialPartial f i z ^ 2 + 2 * f z * spatialSecondPartial f i i z := by
  let D : Vec3 × ℝ → ℝ := fun w ↦ spatialPartial f i w
  have hD : ContDiff ℝ (⊤ : ℕ∞) D := spatialPartial_contDiff hf i
  have heq : (fun w : Vec3 × ℝ ↦ spatialPartial (fun y ↦ f y ^ 2) i w) =
      fun w ↦ D w * f w + f w * D w := by
    funext w
    simpa only [pow_two, D] using CKN.Core.Step3.spatialPartial_mul_full hf hf i w
  change spatialPartial (fun w ↦ spatialPartial (fun y ↦ f y ^ 2) i w) i z = _
  have hcongr := congrArg (fun g : ParabolicPoint → ℝ ↦ spatialPartial g i z) heq
  refine hcongr.trans ?_
  have hadd := spatialPartial_add_smooth (hD.mul hf) (hf.mul hD) i z
  have hleft := CKN.Core.Step3.spatialPartial_mul_full hD hf i z
  have hright := CKN.Core.Step3.spatialPartial_mul_full hf hD i z
  refine hadd.trans ((congrArg₂ (fun a b : ℝ ↦ a + b) hleft hright).trans ?_)
  change spatialSecondPartial f i i z * f z + spatialPartial f i z * spatialPartial f i z +
    (spatialPartial f i z * spatialPartial f i z + f z * spatialSecondPartial f i i z) = _
  ring

/-- The true time derivative of the square of a smooth field. -/
theorem timePartial_square_smooth {f : Vec3 × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : Vec3 × ℝ) :
    timePartial (fun w ↦ f w ^ 2) z = 2 * f z * timePartial f z := by
  have hfs : DifferentiableAt ℝ (fun t : ℝ ↦ f (z.1, t)) z.2 :=
    (hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) |>.differentiableAt
  simpa only [timePartial, deriv, Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 by decide, pow_one] using
    (hfs.hasDerivAt.fun_pow 2).deriv

/-- Genuine compact tests supply all three smooth-square derivative integrability facts. -/
theorem smooth_square_test_integrable {f ψ : Vec3 × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ) :
    Integrable (fun z ↦ f z ^ 2 * timePartial ψ z) volume ∧
      Integrable (fun z ↦ f z * timePartial f z * ψ z) volume ∧
      (∀ i : Fin 3, Integrable (fun z ↦ f z ^ 2 * spatialSecondPartial ψ i i z) volume) ∧
      (∀ i : Fin 3, Integrable (fun z ↦ spatialPartial f i z ^ 2 * ψ z) volume) := by
  have hft := contDiff_timePartial hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hC := (hf.pow 2).continuous.mul (contDiff_timePartial hψ).continuous
    exact hC.integrable_of_hasCompactSupport (hasCompactSupport_timePartial hcψ).mul_left
  · exact ((hf.mul hft).continuous.mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  · intro i
    have hC := (hf.pow 2).continuous.mul
      (spatialPartial_contDiff (spatialPartial_contDiff hψ i) i).continuous
    exact hC.integrable_of_hasCompactSupport
      (hasCompactSupport_spatialSecondPartial hcψ i i).mul_left
  · intro i
    change Integrable (fun z : Vec3 × ℝ ↦ spatialPartial f i z ^ 2 * ψ z) volume
    have hC := ((spatialPartial_contDiff hf i).pow 2).continuous.mul hψ.continuous
    exact hC.integrable_of_hasCompactSupport hcψ.mul_left

/-- Actual time integration by parts gives the exact smooth square correction. -/
theorem smooth_square_time_pairing {f ψ : Vec3 × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ) :
    (∫ z : Vec3 × ℝ, f z ^ 2 * timePartial ψ z) =
      -2 * (∫ z : Vec3 × ℝ, f z * timePartial f z * ψ z) := by
  calc
    _ = -(∫ z : Vec3 × ℝ, timePartial (fun w ↦ f w ^ 2) z * ψ z) :=
      integral_mul_timePartial_eq_neg_timePartial_mul (hf.pow 2) hψ hcψ
    _ = -(∫ z : Vec3 × ℝ, 2 * (f z * timePartial f z * ψ z)) := by
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun z ↦ by
        have hsq := timePartial_square_smooth hf z
        change timePartial (fun w ↦ f w ^ 2) z * ψ z = 2 * (f z * timePartial f z * ψ z)
        rw [hsq]
        ring
    _ = _ := by rw [integral_const_mul]; ring

/-- Two genuine integrations by parts move the spatial Laplacian across a compact test. -/
theorem smooth_square_second_pairing {f ψ : Vec3 × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ) (i : Fin 3) :
    (∫ z : Vec3 × ℝ, f z ^ 2 * spatialSecondPartial ψ i i z) =
      ∫ z : Vec3 × ℝ, spatialSecondPartial (fun w ↦ f w ^ 2) i i z * ψ z := by
  calc
    _ = -(∫ z : Vec3 × ℝ, spatialPartial (fun w ↦ f w ^ 2) i z *
        spatialPartial ψ i z) :=
      integral_mul_spatialPartial_eq_neg_spatialPartial_mul (hf.pow 2)
        (spatialPartial_contDiff hψ i) (hasCompactSupport_spatialPartial hcψ i) i
    _ = _ := by
      have h := integral_mul_spatialPartial_eq_neg_spatialPartial_mul
        (spatialPartial_contDiff (hf.pow 2) i) hψ hcψ i
      exact neg_eq_iff_eq_neg.mpr h

/-- Actual harmonicity on the test support cancels the Laplacian of a smooth square. -/
theorem smooth_harmonic_square_laplacian_pairing {f ψ : Vec3 × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ)
    (hh : ∀ z ∈ tsupport ψ, (∑ i : Fin 3, spatialSecondPartial f i i z) = 0) :
    (∫ z : Vec3 × ℝ, f z ^ 2 * ∑ i : Fin 3, spatialSecondPartial ψ i i z) =
      2 * (∫ z : Vec3 × ℝ, (∑ i : Fin 3, spatialPartial f i z ^ 2) * ψ z) := by
  have hInts := smooth_square_test_integrable hf hψ hcψ
  have hsec (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ ↦ spatialSecondPartial (fun w ↦ f w ^ 2) i i z * ψ z) volume :=
    ((spatialPartial_contDiff (spatialPartial_contDiff (hf.pow 2) i) i).continuous.mul
      hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  calc
    _ = ∑ i : Fin 3, ∫ z : Vec3 × ℝ, f z ^ 2 * spatialSecondPartial ψ i i z := by
      simp_rw [Finset.mul_sum]
      exact integral_finsetSum Finset.univ (fun i _ ↦ hInts.2.2.1 i)
    _ = ∑ i : Fin 3, ∫ z : Vec3 × ℝ,
        spatialSecondPartial (fun w ↦ f w ^ 2) i i z * ψ z := by
      apply Finset.sum_congr rfl
      intro i _
      exact smooth_square_second_pairing hf hψ hcψ i
    _ = ∫ z : Vec3 × ℝ, ∑ i : Fin 3,
        spatialSecondPartial (fun w ↦ f w ^ 2) i i z * ψ z :=
      (integral_finsetSum Finset.univ (fun i _ ↦ hsec i)).symm
    _ = ∫ z : Vec3 × ℝ, 2 * ((∑ i : Fin 3, spatialPartial f i z ^ 2) * ψ z) := by
      apply integral_congr_ae
      apply ae_of_all
      intro z
      simp_rw [spatialSecondPartial_square_smooth hf]
      have heq : (∑ i : Fin 3,
          (2 * spatialPartial f i z ^ 2 + 2 * f z * spatialSecondPartial f i i z) * ψ z) =
          2 * ((∑ i : Fin 3, spatialPartial f i z ^ 2) * ψ z) +
            2 * f z * (∑ i : Fin 3, spatialSecondPartial f i i z) * ψ z := by
        simp only [Fin.sum_univ_three]
        ring
      rw [heq]
      by_cases hz : z ∈ tsupport ψ
      · rw [hh z hz]
        ring
      · rw [image_eq_zero_of_notMem_tsupport hz]
        ring
    _ = _ := integral_const_mul _ _

end FluidSingularSets
