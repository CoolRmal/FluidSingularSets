-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StokesGradientTest
public import CKN.Foundation.Harmonic.InteriorSmooth
public import CKN.Foundation.Parabolic.BallBasics
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Genuine differentiation of locally harmonic representatives

Local C¹ functions satisfy actual weak integration by parts against compact
interior tests. First derivatives of a weakly harmonic C¹ representative
are therefore genuinely weakly harmonic themselves.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- A continuous local function times a compact interior test is genuinely continuous globally. -/
theorem continuousOn_mul_stokesWeakTest {U : Set Vec3} {f : Vec3 → ℝ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (ψ : WeakTestFunction U) :
    Continuous (fun x ↦ f x * ψ x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hf.continuousAt (hU.mem_nhds hx)).mul ψ.contDiff.continuous.continuousAt
  · have hnot : x ∉ tsupport ψ.toFun := fun h ↦ hx (ψ.tsupport_subset h)
    have hz : (fun y ↦ f y * ψ y) =ᶠ[𝓝 x] fun _ ↦ 0 :=
      ((isClosed_tsupport ψ.toFun).isOpen_compl.eventually_mem hnot).mono fun y hy ↦ by
        change f y * ψ y = 0
        rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    change Tendsto (fun y ↦ f y * ψ y) (𝓝 x) (𝓝 (f x * ψ x))
    rw [stokesWeakTest_eq_zero_outside ψ hx, mul_zero]
    exact tendsto_const_nhds.congr' hz.symm

/-- The same literal local test product is actually integrable globally. -/
theorem integrable_continuousOn_mul_stokesWeakTest {U : Set Vec3} {f : Vec3 → ℝ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (ψ : WeakTestFunction U) :
    Integrable (fun x ↦ f x * ψ x) volume :=
  (continuousOn_mul_stokesWeakTest hU hf ψ).integrable_of_hasCompactSupport
    (ψ.hasCompactSupport.mul_left (f := f))

/-- Local C¹ regularity gives the literal actual spatial weak derivative. -/
theorem hasWeakGradientOn_of_contDiffOn {U : Set Vec3} {f : Vec3 → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (1 : ℕ∞) f U) :
    HasWeakGradientOn U f (classicalGradient f) := by
  intro i φ hφ hcompact hsub
  let ψ : WeakTestFunction U := ⟨φ, hφ, hcompact, hsub⟩
  have hdf : ContinuousOn (spatialDeriv f i) U :=
    (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const
  have hintdf := integrable_continuousOn_mul_stokesWeakTest hU hdf ψ
  have hintf := integrable_continuousOn_mul_stokesWeakTest hU hf.continuousOn ψ
  have hintdφ := integrable_continuousOn_mul_stokesWeakTest hU hf.continuousOn
    (stokesWeakTestDerivative ψ i)
  have hglobal := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hintdf hintdφ hintf
    (fun x hx ↦ (hf.contDiffAt (hU.mem_nhds (ψ.tsupport_subset hx))).differentiableAt
      (by norm_num))
    (fun x _hx ↦ hφ.differentiable (by norm_num) x)
  change (∫ x in U, f x * spatialDeriv φ i x) =
    -(∫ x in U, spatialDeriv f i x * φ x)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hglobal
  · intro x hx
    change spatialDeriv f i x * ψ x = 0
    rw [stokesWeakTest_eq_zero_outside ψ hx, mul_zero]
  · intro x hx
    have hz := stokesWeakTest_eq_zero_outside (stokesWeakTestDerivative ψ i) hx
    change spatialDeriv φ i x = 0 at hz
    rw [hz, mul_zero]

/-- The actual Laplacian of a genuine compact test is again a genuine compact test. -/
def stokesWeakTestLaplacian {U : Set Vec3} (ψ : WeakTestFunction U) : WeakTestFunction U where
  toFun := spatialLaplacian ψ.toFun
  contDiff := by
    unfold spatialLaplacian
    exact ContDiff.sum fun i _ ↦
      (stokesWeakTestDerivative (stokesWeakTestDerivative ψ i) i).contDiff
  hasCompactSupport := by
    apply HasCompactSupport.of_support_subset_isCompact ψ.hasCompactSupport.isCompact
    intro x hx
    by_contra hxψ
    apply hx
    change (∑ i : Fin 3, spatialDeriv (spatialDeriv ψ.toFun i) i x) = 0
    apply Finset.sum_eq_zero
    intro i _
    have hsub : tsupport (spatialDeriv (spatialDeriv ψ.toFun i) i) ⊆ tsupport ψ.toFun :=
      (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := spatialDeriv ψ.toFun i) (basisVec i)).trans
        (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := ψ.toFun) (basisVec i))
    exact image_eq_zero_of_notMem_tsupport fun h ↦ hxψ (hsub h)
  tsupport_subset := by
    refine (closure_minimal ?_ (isClosed_tsupport ψ.toFun)).trans ψ.tsupport_subset
    intro x hx
    by_contra hxψ
    apply hx
    change (∑ i : Fin 3, spatialDeriv (spatialDeriv ψ.toFun i) i x) = 0
    apply Finset.sum_eq_zero
    intro i _
    have hsub : tsupport (spatialDeriv (spatialDeriv ψ.toFun i) i) ⊆ tsupport ψ.toFun :=
      (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := spatialDeriv ψ.toFun i) (basisVec i)).trans
        (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := ψ.toFun) (basisVec i))
    exact image_eq_zero_of_notMem_tsupport fun h ↦ hxψ (hsub h)

/-- Literal Laplacian and first derivative commute on actual smooth compact tests. -/
theorem spatialLaplacian_spatialDeriv_commute {ψ : Vec3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin 3) :
    spatialLaplacian (spatialDeriv ψ i) = spatialDeriv (spatialLaplacian ψ) i := by
  funext x
  unfold spatialLaplacian spatialDeriv
  rw [show (fun x : Vec3 ↦ ∑ j : Fin 3,
      (fderiv ℝ (fun z ↦ (fderiv ℝ ψ z) (basisVec j)) x) (basisVec j)) =
      ∑ j : Fin 3, (fun x : Vec3 ↦
        (fderiv ℝ (fun z ↦ (fderiv ℝ ψ z) (basisVec j)) x) (basisVec j)) by
      funext z
      rfl]
  rw [fderiv_sum]
  · change (∑ j : Fin 3, spatialDeriv (mixedSecond ψ j i) j x) =
      ∑ j : Fin 3, spatialDeriv (mixedSecond ψ j j) i x
    apply Finset.sum_congr rfl
    intro j _
    exact congrFun (stokes_hessian_third_derivative hψ j i) x
  · intro j _
    exact (contDiff_spatialDeriv_smooth
      (contDiff_spatialDeriv_smooth hψ j) j).differentiable (by simp) x

/-- Weak harmonicity restricts to any actual subdomain, by compact-test support. -/
theorem localWeaklyHarmonicOn_restrict {U V : Set Vec3} {H : Vec3 → ℝ}
    (hsub : V ⊆ U) (hH : WeaklyHarmonicOn U H) : WeaklyHarmonicOn V H := by
  intro ψ hψ hc hs
  let φ : WeakTestFunction V := ⟨ψ, hψ, hc, hs⟩
  have hz : ∀ x ∉ V, H x * spatialLaplacian ψ x = 0 := by
    intro x hx
    have h := stokesWeakTest_eq_zero_outside (stokesWeakTestLaplacian φ) hx
    change spatialLaplacian ψ x = 0 at h
    rw [h, mul_zero]
  have h := hH ψ hψ hc (hs.trans hsub)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx ↦ hz x fun hxV ↦ hx (hsub hxV))] at h
  exact h

/-- Actual almost-everywhere representatives preserve the literal harmonic test equation. -/
theorem localWeaklyHarmonicOn_congr_ae {U : Set Vec3} {H G : Vec3 → ℝ}
    (hHG : H =ᵐ[volume.restrict U] G) (hH : WeaklyHarmonicOn U H) :
    WeaklyHarmonicOn U G := by
  intro ψ hψ hc hs
  calc
    _ = ∫ x in U, H x * spatialLaplacian ψ x := by
      apply integral_congr_ae
      filter_upwards [hHG] with x hx
      rw [hx]
    _ = 0 := hH ψ hψ hc hs

/-- First derivatives of a local C¹ harmonic representative are genuinely weakly harmonic. -/
theorem weaklyHarmonicOn_spatialDeriv_of_contDiffOn {U : Set Vec3} {H : Vec3 → ℝ}
    (hU : IsOpen U) (hH : ContDiffOn ℝ (1 : ℕ∞) H U)
    (hweak : WeaklyHarmonicOn U H) (i : Fin 3) :
    WeaklyHarmonicOn U (spatialDeriv H i) := by
  intro ψ hψ hc hs
  let φ : WeakTestFunction U := ⟨ψ, hψ, hc, hs⟩
  let φLap := stokesWeakTestLaplacian φ
  let φDer := stokesWeakTestDerivative φ i
  have hg := hasWeakGradientOn_of_contDiffOn hU hH i
    φLap.toFun φLap.contDiff φLap.hasCompactSupport φLap.tsupport_subset
  change (∫ x in U, H x * spatialDeriv (spatialLaplacian ψ) i x) =
    -(∫ x in U, spatialDeriv H i x * spatialLaplacian ψ x) at hg
  rw [← spatialLaplacian_spatialDeriv_commute hψ i] at hg
  have hh := hweak φDer.toFun φDer.contDiff φDer.hasCompactSupport φDer.tsupport_subset
  change (∫ x in U, H x * spatialLaplacian (spatialDeriv ψ i) x) = 0 at hh
  linarith

end FluidSingularSets
