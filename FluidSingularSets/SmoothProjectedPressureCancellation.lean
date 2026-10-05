-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SmoothProjectedDivergence

/-!
# Actual smooth pressure-gradient cancellation

A genuine smooth divergence-free correction obeys the classical compact-test
identity. Together with the original suitable divergence equation, this
cancels the pressure-gradient pairing of the actual projected velocity.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Genuine smooth divergence-free vector fields annihilate compact scalar gradients. -/
theorem smooth_divergence_compact_pairing
    {H : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ)
    (hdiv : ∀ z ∈ tsupport ψ,
      (∑ i : Fin 3, spatialPartial (fun w ↦ H w i) i z) = 0) :
    Integrable (fun z : Vec3 × ℝ ↦ ∑ i : Fin 3, H z i * spatialPartial ψ i z) volume ∧
      (∫ z : Vec3 × ℝ, ∑ i : Fin 3, H z i * spatialPartial ψ i z) = 0 := by
  have hHi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ ↦ H z i) :=
    (contDiff_apply ℝ ℝ i).comp hH
  have hL (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ ↦ H z i * spatialPartial ψ i z) volume := by
    have hC := (hHi i).continuous.mul (spatialPartial_contDiff hψ i).continuous
    exact hC.integrable_of_hasCompactSupport (hasCompactSupport_spatialPartial hcψ i).mul_left
  have hR (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ ↦ spatialPartial (fun w ↦ H w i) i z * ψ z) volume := by
    have hC := (spatialPartial_contDiff (hHi i) i).continuous.mul hψ.continuous
    exact hC.integrable_of_hasCompactSupport hcψ.mul_left
  refine ⟨integrable_finsetSum _ fun i _ ↦ hL i, ?_⟩
  calc
    _ = ∑ i : Fin 3, ∫ z : Vec3 × ℝ, H z i * spatialPartial ψ i z :=
      integral_finsetSum Finset.univ fun i _ ↦ hL i
    _ = ∑ i : Fin 3, -(∫ z : Vec3 × ℝ,
        spatialPartial (fun w ↦ H w i) i z * ψ z) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_mul_spatialPartial_eq_neg_spatialPartial_mul (hHi i) hψ hcψ i
    _ = -(∫ z : Vec3 × ℝ,
        ∑ i : Fin 3, spatialPartial (fun w ↦ H w i) i z * ψ z) := by
      rw [Finset.sum_neg_distrib, integral_finsetSum Finset.univ fun i _ ↦ hR i]
    _ = 0 := by
      have heq : (fun z : Vec3 × ℝ ↦
          ∑ i : Fin 3, spatialPartial (fun w ↦ H w i) i z * ψ z) = fun _ ↦ (0 : ℝ) := by
        funext z
        rw [← Finset.sum_mul]
        by_cases hz : z ∈ tsupport ψ
        · rw [hdiv z hz, zero_mul]
        · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
      rw [heq, integral_zero, neg_zero]

/-- Original suitable divergence and genuine correction divergence cancel the true
projected pressure-gradient term against every compact scalar energy test. -/
theorem suitable_smooth_projected_pressure_pairing
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {H : Vec3 × ℝ → Vec3} {P ψ : Vec3 × ℝ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hdiv : ∀ z ∈ tsupport ψ,
      (∑ i : Fin 3, spatialPartial (fun w ↦ H w i) i z) = 0) :
    Integrable (fun z : Vec3 × ℝ ↦
      (∑ i : Fin 3, (u z i + H z i) * spatialPartial P i z) * ψ z +
        P z * (∑ i : Fin 3, (u z i + H z i) * spatialPartial ψ i z)) volume ∧
      (∫ z : Vec3 × ℝ,
        (∑ i : Fin 3, (u z i + H z i) * spatialPartial P i z) * ψ z +
          P z * (∑ i : Fin 3, (u z i + H z i) * spatialPartial ψ i z)) = 0 := by
  have ht := spaceTimeTestFunction_mul_smooth hψ hP
  have hu := suitable_global_compact_divergence hsol ht
  have hh := smooth_divergence_compact_pairing hH ht.1 ht.2.1
    (fun z hz ↦ hdiv z ((tsupport_mul_subset_left (f := ψ) (g := P)) hz))
  have hfun : (fun z : Vec3 × ℝ ↦
      (∑ i : Fin 3, u z i * spatialPartial (fun w ↦ ψ w * P w) i z) +
        (∑ i : Fin 3, H z i * spatialPartial (fun w ↦ ψ w * P w) i z)) =
      fun z : Vec3 × ℝ ↦
        (∑ i : Fin 3, (u z i + H z i) * spatialPartial P i z) * ψ z +
          P z * (∑ i : Fin 3, (u z i + H z i) * spatialPartial ψ i z) := by
    funext z
    have hd (i : Fin 3) := CKN.Core.Step3.spatialPartial_mul_full hψ.1 hP i z
    have hsumU := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun i _ ↦ congrArg (fun a : ℝ ↦ u z i * a) (hd i))
    have hsumH := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun i _ ↦ congrArg (fun a : ℝ ↦ H z i * a) (hd i))
    refine (congrArg₂ (fun a b : ℝ ↦ a + b) hsumU hsumH).trans ?_
    simp only [Fin.sum_univ_three]
    ring
  have hi := hu.1.add hh.1
  refine ⟨hi.congr (ae_of_all _ fun z ↦ congrFun hfun z), ?_⟩
  calc
    _ = ∫ z : Vec3 × ℝ,
        (∑ i : Fin 3, u z i * spatialPartial (fun w ↦ ψ w * P w) i z) +
          (∑ i : Fin 3, H z i * spatialPartial (fun w ↦ ψ w * P w) i z) :=
      (congrArg (fun g : Vec3 × ℝ → ℝ ↦ ∫ z, g z) hfun).symm
    _ = 0 := (integral_add hu.1 hh.1).trans
      ((congrArg₂ (fun a b : ℝ ↦ a + b) hu.2 hh.2).trans (zero_add 0))

end FluidSingularSets
