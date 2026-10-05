-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallPressureBounds

/-!
# Genuine local Hessian calculus and divergence of harmonic gradients

All derivatives are actual Fréchet coordinate derivatives on open sets.
Local equality identifies actual Hessians, genuine C² regularity gives true
component weak gradients, and compact-test integration by parts proves that
the actual gradient of a weakly harmonic C¹ function is divergence-free.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A genuine local C² function has actual C¹ first coordinate derivatives. -/
theorem contDiffOn_spatialDeriv_of_two {U : Set Vec3} {f : Vec3 → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (2 : ℕ∞) f U) (j : Fin 3) :
    ContDiffOn ℝ (1 : ℕ∞) (spatialDeriv f j) U :=
  ((contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) hU).mp hf).2.2.clm_apply contDiffOn_const

/-- Local equality on an open set identifies every actual mixed derivative. -/
theorem mixedSecond_eqOn_of_eqOn {U : Set Vec3} {f g : Vec3 → ℝ}
    (hU : IsOpen U) (heq : EqOn f g U) (i j : Fin 3) :
    EqOn (mixedSecond f i j) (mixedSecond g i j) U := by
  have hfirst := classicalGradient_eqOn_of_eqOn hU heq
  have hj : EqOn (spatialDeriv f j) (spatialDeriv g j) U := by
    intro x hx
    exact congrArg (fun v : Vec3 ↦ v j) (hfirst hx)
  have hsecond := classicalGradient_eqOn_of_eqOn hU hj
  intro x hx
  exact congrArg (fun v : Vec3 ↦ v i) (hsecond hx)

/-- Actual local first derivatives respect addition of differentiable functions. -/
theorem spatialDeriv_add_eqOn {U : Set Vec3} {f g : Vec3 → ℝ} (hU : IsOpen U)
    (hf : DifferentiableOn ℝ f U) (hg : DifferentiableOn ℝ g U) (j : Fin 3) :
    EqOn (spatialDeriv (f + g) j) (spatialDeriv f j + spatialDeriv g j) U := by
  intro x hx
  unfold spatialDeriv
  rw [fderiv_add (hf.differentiableAt (hU.mem_nhds hx))
    (hg.differentiableAt (hU.mem_nhds hx))]
  rfl

/-- Actual local first derivatives respect real scaling. -/
theorem spatialDeriv_smul_eqOn {U : Set Vec3} {f : Vec3 → ℝ} (hU : IsOpen U)
    (hf : DifferentiableOn ℝ f U) (c : ℝ) (j : Fin 3) :
    EqOn (spatialDeriv (c • f) j) (c • spatialDeriv f j) U := by
  intro x hx
  unfold spatialDeriv
  rw [fderiv_const_smul (hf.differentiableAt (hU.mem_nhds hx))]
  rfl

/-- Genuine local Hessians respect addition of actual C² functions. -/
theorem mixedSecond_add_eqOn {U : Set Vec3} {f g : Vec3 → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (2 : ℕ∞) f U) (hg : ContDiffOn ℝ (2 : ℕ∞) g U) (i j : Fin 3) :
    EqOn (mixedSecond (f + g) i j) (mixedSecond f i j + mixedSecond g i j) U := by
  have hfirst := spatialDeriv_add_eqOn hU (hf.differentiableOn (by norm_num))
    (hg.differentiableOn (by norm_num)) j
  have hsecond := classicalGradient_eqOn_of_eqOn hU hfirst
  have hsum := spatialDeriv_add_eqOn hU
    ((contDiffOn_spatialDeriv_of_two hU hf j).differentiableOn (by norm_num))
    ((contDiffOn_spatialDeriv_of_two hU hg j).differentiableOn (by norm_num)) i
  intro x hx
  exact (congrArg (fun v : Vec3 ↦ v i) (hsecond hx)).trans (hsum hx)

/-- Genuine local Hessians respect real scaling. -/
theorem mixedSecond_smul_eqOn {U : Set Vec3} {f : Vec3 → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (2 : ℕ∞) f U) (c : ℝ) (i j : Fin 3) :
    EqOn (mixedSecond (c • f) i j) (c • mixedSecond f i j) U := by
  have hfirst := spatialDeriv_smul_eqOn hU (hf.differentiableOn (by norm_num)) c j
  have hsecond := classicalGradient_eqOn_of_eqOn hU hfirst
  have hsmul := spatialDeriv_smul_eqOn hU
    ((contDiffOn_spatialDeriv_of_two hU hf j).differentiableOn (by norm_num)) c i
  intro x hx
  exact (congrArg (fun v : Vec3 ↦ v i) (hsecond hx)).trans (hsmul hx)

/-- The actual Hessian is the genuine derivative-first weak gradient of each component. -/
theorem hasWeakGradientOn_gradient_of_contDiffOn_two {U : Set Vec3} {f : Vec3 → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (2 : ℕ∞) f U) (j : Fin 3) :
    HasWeakGradientOn U (fun x ↦ classicalGradient f x j)
      (fun x i ↦ mixedSecond f i j x) :=
  hasWeakGradientOn_of_contDiffOn hU (contDiffOn_spatialDeriv_of_two hU hf j)

/-- The actual gradient of a genuine C¹ weakly harmonic function is weakly divergence-free. -/
theorem classicalGradient_weakly_divergenceFree_of_weaklyHarmonic
    {U : Set Vec3} {H : Vec3 → ℝ} (hU : IsOpen U)
    (hH : ContDiffOn ℝ (1 : ℕ∞) H U) (hweak : WeaklyHarmonicOn U H)
    (ψ : Vec3 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ U) :
    (∫ x in U, ∑ i : Fin 3, classicalGradient H x i * spatialDeriv ψ i x) = 0 := by
  let φ : WeakTestFunction U := ⟨ψ, hψ, hc, hs⟩
  have hgrad := hasWeakGradientOn_of_contDiffOn hU hH
  have hpartialCont (i : Fin 3) : ContinuousOn (spatialDeriv H i) U :=
    (hH.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const
  have hi (i : Fin 3) : Integrable (fun x ↦ spatialDeriv H i x * spatialDeriv ψ i x)
      (volume.restrict U) :=
    (integrable_continuousOn_mul_stokesWeakTest hU (hpartialCont i)
      (stokesWeakTestDerivative φ i)).mono_measure Measure.restrict_le_self
  have hj (i : Fin 3) : Integrable (fun x ↦ H x * spatialDeriv (spatialDeriv ψ i) i x)
      (volume.restrict U) :=
    (integrable_continuousOn_mul_stokesWeakTest hU hH.continuousOn
      (stokesWeakTestDerivative (stokesWeakTestDerivative φ i) i)).mono_measure
        Measure.restrict_le_self
  have hparts (i : Fin 3) :
      (∫ x in U, spatialDeriv H i x * spatialDeriv ψ i x) =
        -(∫ x in U, H x * spatialDeriv (spatialDeriv ψ i) i x) := by
    let φi := stokesWeakTestDerivative φ i
    have h := hgrad i φi.toFun φi.contDiff φi.hasCompactSupport φi.tsupport_subset
    change (∫ x in U, H x * spatialDeriv (spatialDeriv ψ i) i x) =
      -(∫ x in U, spatialDeriv H i x * spatialDeriv ψ i x) at h
    linarith
  calc
    _ = ∑ i : Fin 3, ∫ x in U, spatialDeriv H i x * spatialDeriv ψ i x :=
      integral_finsetSum Finset.univ (fun i _ ↦ hi i)
    _ = ∑ i : Fin 3, -(∫ x in U, H x * spatialDeriv (spatialDeriv ψ i) i x) :=
      Finset.sum_congr rfl (fun i _ ↦ hparts i)
    _ = -(∫ x in U, H x * spatialLaplacian ψ x) := by
      rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ (fun i _ ↦ hj i)]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [spatialLaplacian, Finset.mul_sum]
    _ = 0 := by rw [hweak ψ hψ hc hs, neg_zero]

end FluidSingularSets
