-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.HarmonicCorrectionCrossTerms

/-!
# Genuine divergence cancellation for smooth pressure corrections

The original suitable divergence identity cancels the convection of the square
of an actual smooth correction. The weak-gradient product identity also moves
the test Laplacian across the genuine velocity-correction cross term.
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

/-- The true suitable divergence equation holds globally for each compact scalar test. -/
theorem suitable_global_compact_divergence
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    Integrable (fun z : Vec3 × ℝ ↦ ∑ j : Fin 3, u z j * spatialPartial ψ j z) volume ∧
      (∫ z : Vec3 × ℝ, ∑ j : Fin 3, u z j * spatialPartial ψ j z) = 0 := by
  have htube : acceleratedFrameMapProd (fun _ ↦ (0 : Vec3)) '' (Ω ×ˢ I) ⊆ Ω ×ˢ I := by
    rintro z ⟨w, hw, rfl⟩
    simpa only [acceleratedFrameMapProd, zero_add] using hw
  have h := suitable_accelerated_global_divergence (m := fun _ ↦ (0 : Vec3))
    hsol contDiff_const contDiff_const
    htube hψ
  simpa only [acceleratedVelocity, acceleratedFrameMap, Pi.zero_apply, zero_add,
    sub_zero] using h

/-- The genuine divergence equation cancels the convection of a smooth correction square. -/
theorem suitable_smooth_square_convection_pairing
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {H ψ : Vec3 × ℝ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    Integrable (fun z : Vec3 × ℝ ↦
      2 * (∑ j : Fin 3, u z j * H z * spatialPartial H j z) * ψ z +
        H z ^ 2 * (∑ j : Fin 3, u z j * spatialPartial ψ j z)) volume ∧
      (∫ z : Vec3 × ℝ,
        2 * (∑ j : Fin 3, u z j * H z * spatialPartial H j z) * ψ z +
          H z ^ 2 * (∑ j : Fin 3, u z j * spatialPartial ψ j z)) = 0 := by
  have ht := spaceTimeTestFunction_mul_smooth hψ (hH.pow 2)
  have hd (j : Fin 3) (z : Vec3 × ℝ) : spatialPartial (fun w ↦ H w ^ 2) j z =
      2 * H z * spatialPartial H j z := by
    have h := CKN.Core.Step3.spatialPartial_mul_full hH hH j z
    calc
      _ = spatialPartial H j z * H z + H z * spatialPartial H j z := by
        simpa only [pow_two] using h
      _ = _ := by ring
  have hp (j : Fin 3) (z : Vec3 × ℝ) :
      u z j * spatialPartial (fun w ↦ ψ w * H w ^ 2) j z =
        2 * (u z j * H z * spatialPartial H j z) * ψ z +
          H z ^ 2 * (u z j * spatialPartial ψ j z) := by
    calc
      _ = u z j * (spatialPartial ψ j z * H z ^ 2 +
          ψ z * spatialPartial (fun w ↦ H w ^ 2) j z) :=
        congrArg (fun a : ℝ ↦ u z j * a)
          (CKN.Core.Step3.spatialPartial_mul_full hψ.1 (hH.pow 2) j z)
      _ = u z j * (spatialPartial ψ j z * H z ^ 2 +
          ψ z * (2 * H z * spatialPartial H j z)) :=
        congrArg (fun a : ℝ ↦ u z j * (spatialPartial ψ j z * H z ^ 2 + ψ z * a))
          (hd j z)
      _ = _ := by ring
  have hfun : (fun z : Vec3 × ℝ ↦
      ∑ j : Fin 3, u z j * spatialPartial (fun w ↦ ψ w * H w ^ 2) j z) =
        fun z : Vec3 × ℝ ↦
          2 * (∑ j : Fin 3, u z j * H z * spatialPartial H j z) * ψ z +
            H z ^ 2 * (∑ j : Fin 3, u z j * spatialPartial ψ j z) := by
    funext z
    have heq := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun j _ ↦ hp j z)
    refine heq.trans ?_
    simp only [Fin.sum_univ_three]
    ring
  have hw := suitable_global_compact_divergence hsol ht
  exact ⟨hw.1.congr (ae_of_all _ fun z ↦ congrFun hfun z),
    (congrArg (fun g : Vec3 × ℝ → ℝ ↦ ∫ z, g z) hfun).symm.trans hw.2⟩

/-- The genuine weak-gradient product rule moves the test Laplacian across a smooth correction. -/
theorem suitable_smooth_cross_laplacian_pairing
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {H ψ : Vec3 × ℝ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) (i : Fin 3) :
    Integrable (fun z : Vec3 × ℝ ↦
      u z i * H z * (∑ j : Fin 3, spatialSecondPartial ψ j j z)) volume ∧
      Integrable (fun z : Vec3 × ℝ ↦
        ∑ j : Fin 3, Du z i j * H z * spatialPartial ψ j z) volume ∧
      Integrable (fun z : Vec3 × ℝ ↦
        ∑ j : Fin 3, u z i * spatialPartial H j z * spatialPartial ψ j z) volume ∧
      (∫ z : Vec3 × ℝ, u z i * H z *
          (∑ j : Fin 3, spatialSecondPartial ψ j j z)) =
        -(∫ z : Vec3 × ℝ, ∑ j : Fin 3, Du z i j * H z * spatialPartial ψ j z) -
          (∫ z : Vec3 × ℝ,
            ∑ j : Fin 3, u z i * spatialPartial H j z * spatialPartial ψ j z) := by
  let A : Fin 3 → Vec3 × ℝ → ℝ := fun j z ↦
    u z i * H z * spatialSecondPartial ψ j j z
  let B : Fin 3 → Vec3 × ℝ → ℝ := fun j z ↦
    u z i * spatialPartial H j z * spatialPartial ψ j z
  let D : Fin 3 → Vec3 × ℝ → ℝ := fun j z ↦
    Du z i j * H z * spatialPartial ψ j z
  have hpair (j : Fin 3) := suitable_spatial_product_pairing hsol hH
    (spaceTimeTest_spatialPartial hψ j) i j
  have hA (j : Fin 3) : Integrable (A j) volume := (hpair j).2.1
  have hB (j : Fin 3) : Integrable (B j) volume := (hpair j).1
  have hD (j : Fin 3) : Integrable (D j) volume := (hpair j).2.2.1
  have hsumA : Integrable (fun z : Vec3 × ℝ ↦ ∑ j : Fin 3, A j z) volume :=
    integrable_finsetSum _ fun j _ ↦ hA j
  have hsumB : Integrable (fun z : Vec3 × ℝ ↦ ∑ j : Fin 3, B j z) volume :=
    integrable_finsetSum _ fun j _ ↦ hB j
  have hsumD : Integrable (fun z : Vec3 × ℝ ↦ ∑ j : Fin 3, D j z) volume :=
    integrable_finsetSum _ fun j _ ↦ hD j
  have hfunA : (fun z : Vec3 × ℝ ↦
      u z i * H z * (∑ j : Fin 3, spatialSecondPartial ψ j j z)) =
        fun z ↦ ∑ j : Fin 3, A j z := by
    funext z
    simp only [A, Finset.mul_sum]
  rw [hfunA]
  refine ⟨hsumA, hsumD, hsumB, ?_⟩
  rw [integral_finsetSum Finset.univ (fun j _ ↦ hA j),
    integral_finsetSum Finset.univ (fun j _ ↦ hD j),
    integral_finsetSum Finset.univ (fun j _ ↦ hB j)]
  have heq : (∑ j : Fin 3, ∫ z : Vec3 × ℝ, B j z) +
      (∑ j : Fin 3, ∫ z : Vec3 × ℝ, A j z) =
        -(∑ j : Fin 3, ∫ z : Vec3 × ℝ, D j z) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ (hpair j).2.2.2
  linarith only [heq]

end Suitable

end FluidSingularSets
