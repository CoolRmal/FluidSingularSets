-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SmoothHarmonicEnergy

/-!
# Actual weak-gradient pairings with smooth spatial corrections

Compact smooth products are legitimate tests of the original suitable weak
gradient. Every individual cross term is integrable before the product rule
is integrated. Harmonicity then removes the genuine Laplacian contribution.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
  {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-- Actual suitable velocity multiplied by a continuous compact test product is integrable. -/
theorem suitable_velocity_continuous_test_product_integrable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {F ψ : Vec3 × ℝ → ℝ} (hF : Continuous F)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) (i : Fin 3) :
    Integrable (fun z : Vec3 × ℝ ↦ u z i * F z * ψ z) volume := by
  have hK := isCompact_tsupport_parabolic hψ.2.1
  have hKs := tsupport_parabolic_subset_spaceTimeSet hψ
  have hu := velocity_component_integrableOn_compact_of_data hsol.toData hK hKs i
  have hC : Continuous (fun z : ParabolicPoint ↦ F z * ψ z) :=
    (hF.mul hψ.1.continuous).comp continuous_parabolicPoint_to_prod
  have hprod : IntegrableOn (fun z : ParabolicPoint ↦ u z i * F z * ψ z)
      (tsupport (show ParabolicPoint → ℝ from ψ)) volume := by
    have h := hu.smul_continuousOn hC.continuousOn hK
    simpa only [smul_eq_mul, mul_assoc] using h
  have hs : Function.support (fun z : ParabolicPoint ↦ u z i * F z * ψ z) ⊆
      tsupport (show ParabolicPoint → ℝ from ψ) := by
    intro z hz
    by_contra hout
    exact hz (mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hout))
  exact (integrableOn_iff_integrable_of_support_subset hs).mp hprod

/-- Actual suitable weak gradient multiplied by a continuous compact product is integrable. -/
theorem suitable_gradient_continuous_test_product_integrable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {F ψ : Vec3 × ℝ → ℝ} (hF : Continuous F)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) (i j : Fin 3) :
    Integrable (fun z : Vec3 × ℝ ↦ Du z i j * F z * ψ z) volume := by
  have hK := isCompact_tsupport_parabolic hψ.2.1
  have hKs := tsupport_parabolic_subset_spaceTimeSet hψ
  have hD := gradient_entry_integrableOn_compact_of_data hsol.toData hK hKs i j
  have hC : Continuous (fun z : ParabolicPoint ↦ F z * ψ z) :=
    (hF.mul hψ.1.continuous).comp continuous_parabolicPoint_to_prod
  have hprod : IntegrableOn (fun z : ParabolicPoint ↦ Du z i j * F z * ψ z)
      (tsupport (show ParabolicPoint → ℝ from ψ)) volume := by
    have h := hD.smul_continuousOn hC.continuousOn hK
    simpa only [smul_eq_mul, mul_assoc] using h
  have hs : Function.support (fun z : ParabolicPoint ↦ Du z i j * F z * ψ z) ⊆
      tsupport (show ParabolicPoint → ℝ from ψ) := by
    intro z hz
    by_contra hout
    exact hz (mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hout))
  exact (integrableOn_iff_integrable_of_support_subset hs).mp hprod

/-- A genuine compact scalar space-time test remains a test after spatial differentiation. -/
theorem spaceTimeTest_spatialPartial
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) (j : Fin 3) :
    (fun z : Vec3 × ℝ ↦ spatialPartial ψ j z) ∈
      spaceTimeTestFunction (V := ℝ) Ω I :=
  ⟨spatialPartial_contDiff hψ.1 j, hasCompactSupport_spatialPartial hψ.2.1 j,
    (tsupport_spatialPartial_subset j).trans hψ.2.2⟩

/-- The actual product rule splits a suitable weak-gradient compact pairing.
Both velocity terms and the weak-gradient term are genuinely integrable. -/
theorem suitable_spatial_product_pairing
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {F ψ : Vec3 × ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) (i j : Fin 3) :
    Integrable (fun z : Vec3 × ℝ ↦ u z i * spatialPartial F j z * ψ z) volume ∧
      Integrable (fun z : Vec3 × ℝ ↦ u z i * F z * spatialPartial ψ j z) volume ∧
      Integrable (fun z : Vec3 × ℝ ↦ Du z i j * F z * ψ z) volume ∧
      (∫ z : Vec3 × ℝ, u z i * spatialPartial F j z * ψ z) +
          (∫ z : Vec3 × ℝ, u z i * F z * spatialPartial ψ j z) =
        -(∫ z : Vec3 × ℝ, Du z i j * F z * ψ z) := by
  have hA := suitable_velocity_continuous_test_product_integrable hsol
    (spatialPartial_contDiff hF j).continuous hψ i
  have hB := suitable_velocity_continuous_test_product_integrable hsol hF.continuous
    (spaceTimeTest_spatialPartial hψ j) i
  have hD := suitable_gradient_continuous_test_product_integrable hsol hF.continuous hψ i j
  have ht := spaceTimeTestFunction_mul_smooth hψ hF
  have hw := (suitable_joint_spatial_integration_by_parts hsol ht i j).2.2
  refine ⟨hA, hB, hD, ?_⟩
  have hleft : (∫ z : Vec3 × ℝ, u z i * spatialPartial (fun w ↦ ψ w * F w) j z) =
      (∫ z : Vec3 × ℝ, u z i * spatialPartial F j z * ψ z) +
        (∫ z : Vec3 × ℝ, u z i * F z * spatialPartial ψ j z) := by
    calc
      _ = ∫ z : Vec3 × ℝ, u z i * spatialPartial F j z * ψ z +
          u z i * F z * spatialPartial ψ j z := by
        apply integral_congr_ae
        apply ae_of_all
        intro z
        have hd := CKN.Core.Step3.spatialPartial_mul_full hψ.1 hF j z
        convert congrArg (fun a : ℝ ↦ u z i * a) hd using 1
        ring
      _ = _ := integral_add hA hB
  have hright : (∫ z : Vec3 × ℝ, Du z i j * (ψ z * F z)) =
      ∫ z : Vec3 × ℝ, Du z i j * F z * ψ z := by
    apply integral_congr_ae
    exact ae_of_all _ fun _ ↦ by ring
  exact hleft.symm.trans (hw.trans (congrArg Neg.neg hright))

/-- Actual harmonicity cancels the Laplacian term in the suitable weak-gradient pairing. -/
theorem suitable_harmonic_gradient_cross_pairing
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {H ψ : Vec3 × ℝ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hh : ∀ z ∈ tsupport ψ, (∑ j : Fin 3, spatialSecondPartial H j j z) = 0)
    (i : Fin 3) :
    Integrable (fun z : Vec3 × ℝ ↦
      (∑ j : Fin 3, Du z i j * spatialPartial H j z) * ψ z) volume ∧
      Integrable (fun z : Vec3 × ℝ ↦
        ∑ j : Fin 3, u z i * spatialPartial H j z * spatialPartial ψ j z) volume ∧
      (∫ z : Vec3 × ℝ, (∑ j : Fin 3, Du z i j * spatialPartial H j z) * ψ z) =
        -(∫ z : Vec3 × ℝ,
          ∑ j : Fin 3, u z i * spatialPartial H j z * spatialPartial ψ j z) := by
  let A : Fin 3 → Vec3 × ℝ → ℝ := fun j z ↦
    u z i * spatialSecondPartial H j j z * ψ z
  let B : Fin 3 → Vec3 × ℝ → ℝ := fun j z ↦
    u z i * spatialPartial H j z * spatialPartial ψ j z
  let D : Fin 3 → Vec3 × ℝ → ℝ := fun j z ↦
    Du z i j * spatialPartial H j z * ψ z
  have hpair (j : Fin 3) := suitable_spatial_product_pairing hsol
    (spatialPartial_contDiff hH j) hψ i j
  have hA (j : Fin 3) : Integrable (A j) volume := (hpair j).1
  have hB (j : Fin 3) : Integrable (B j) volume := (hpair j).2.1
  have hD (j : Fin 3) : Integrable (D j) volume := (hpair j).2.2.1
  have hzero : (∑ j : Fin 3, ∫ z : Vec3 × ℝ, A j z) = 0 := by
    rw [← integral_finsetSum Finset.univ (fun j _ ↦ hA j)]
    have hz : (fun z : Vec3 × ℝ ↦ ∑ j : Fin 3, A j z) = fun _ ↦ (0 : ℝ) := by
      funext z
      have halg : (∑ j : Fin 3, A j z) =
          u z i * (∑ j : Fin 3, spatialSecondPartial H j j z) * ψ z := by
        simp only [A, Fin.sum_univ_three]
        ring
      refine halg.trans ?_
      by_cases hz : z ∈ tsupport ψ
      · rw [hh z hz]
        ring
      · rw [image_eq_zero_of_notMem_tsupport hz]
        ring
    rw [hz, integral_zero]
  have heq : (∑ j : Fin 3, ∫ z : Vec3 × ℝ, A j z) +
      (∑ j : Fin 3, ∫ z : Vec3 × ℝ, B j z) =
        -(∑ j : Fin 3, ∫ z : Vec3 × ℝ, D j z) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ (hpair j).2.2.2
  have hsumD : Integrable (fun z : Vec3 × ℝ ↦ ∑ j : Fin 3, D j z) volume :=
    integrable_finsetSum _ fun j _ ↦ hD j
  have hsumB : Integrable (fun z : Vec3 × ℝ ↦ ∑ j : Fin 3, B j z) volume :=
    integrable_finsetSum _ fun j _ ↦ hB j
  have hfunD : (fun z : Vec3 × ℝ ↦
      (∑ j : Fin 3, Du z i j * spatialPartial H j z) * ψ z) =
        fun z ↦ ∑ j : Fin 3, D j z := by
    funext z
    simp only [D, Finset.sum_mul]
  rw [hfunD]
  refine ⟨hsumD, hsumB, ?_⟩
  rw [integral_finsetSum Finset.univ (fun j _ ↦ hD j),
    integral_finsetSum Finset.univ (fun j _ ↦ hB j)]
  rw [hzero, zero_add] at heq
  linarith only [heq]

end Suitable

end FluidSingularSets
