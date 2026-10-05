-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.LocalStokesEnergy
public import FluidSingularSets.WeightedBallDivergence
public import CKN.Foundation.Harmonic.InteriorWeak
public import CKN.Foundation.Euclidean.SmoothIBP

/-!
# Genuine Hessian testing of the completed Stokes energy space

Mixed-derivative integration by parts identifies the Hessian pairing with
the divergence--Laplacian pairing, first on compact smooth tests and then on
the actual Hilbert completion. This gives distributional harmonicity of
the actual Stokes pressure whenever the source vanishes on gradient tests.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- A genuine spatial derivative remains a compact smooth test in the same domain. -/
def stokesWeakTestDerivative {U : Set Vec3} (ψ : WeakTestFunction U) (i : Fin 3) :
    WeakTestFunction U where
  toFun := spatialDeriv ψ.toFun i
  contDiff := contDiff_spatialDeriv_smooth ψ.contDiff i
  hasCompactSupport := ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
  tsupport_subset := (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := ψ.toFun)
    (basisVec i)).trans ψ.tsupport_subset

/-- The literal gradient of a genuine compact scalar test. -/
def stokesScalarGradientTest {U : Set Vec3} (ψ : WeakTestFunction U) : StokesVectorTest U :=
  stokesWeakTestDerivative ψ

theorem stokesWeakTest_eq_zero_outside {U : Set Vec3} (ψ : WeakTestFunction U)
    {x : Vec3} (hx : x ∉ U) : ψ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hx (ψ.tsupport_subset h)

/-- Multiplication by a genuine test is actually integrable in the domain. -/
theorem stokesWeakTest_integrableOn_mul {U : Set Vec3} {a : Vec3 → ℝ}
    (ha : Continuous a) (ψ : WeakTestFunction U) :
    Integrable (fun x ↦ a x * ψ x) (volume.restrict U) :=
  (ha.mul ψ.contDiff.continuous).integrable_of_hasCompactSupport
    (ψ.hasCompactSupport.mul_left (f := a)) |>.mono_measure Measure.restrict_le_self

/-- Genuine compact test integration by parts, with the actual restricted volume. -/
theorem stokesWeakTest_integral_ibp {U : Set Vec3} {a : Vec3 → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (ψ : WeakTestFunction U) (i : Fin 3) :
    (∫ x in U, a x * spatialDeriv ψ.toFun i x) =
      -(∫ x in U, spatialDeriv a i x * ψ x) := by
  have hleft : ∀ x ∉ U, a x * spatialDeriv ψ.toFun i x = 0 := by
    intro x hx
    have hz := stokesWeakTest_eq_zero_outside (stokesWeakTestDerivative ψ i) hx
    exact mul_eq_zero_of_right (a x) hz
  have hright : ∀ x ∉ U, spatialDeriv a i x * ψ x = 0 := by
    intro x hx
    rw [stokesWeakTest_eq_zero_outside ψ hx, mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hleft,
    setIntegral_eq_integral_of_forall_compl_eq_zero hright]
  exact integral_mul_spatialDeriv_eq_neg_integral_spatialDeriv_mul
    ha ψ.contDiff ψ.hasCompactSupport i

/-- The actual third derivative needed for Hessian testing commutes. -/
theorem stokes_hessian_third_derivative {a : Vec3 → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (i j : Fin 3) :
    spatialDeriv (mixedSecond a i j) i = spatialDeriv (mixedSecond a i i) j := by
  have hm : mixedSecond a i j = mixedSecond a j i := by
    funext x
    exact mixedSecond_commute_smooth ha i j x
  rw [hm]
  funext x
  exact mixedSecond_commute_smooth (contDiff_spatialDeriv_smooth ha i) i j x

/-- A genuine componentwise Hessian pairing equals its divergence counterpart. -/
theorem stokesWeakTest_hessian_ibp {U : Set Vec3} (a ψ : WeakTestFunction U)
    (i j : Fin 3) :
    (∫ x in U, spatialDeriv a.toFun i x * mixedSecond ψ.toFun i j x) =
      ∫ x in U, spatialDeriv a.toFun j x * mixedSecond ψ.toFun i i x := by
  have hleft := stokesWeakTest_integral_ibp a.contDiff
    (stokesWeakTestDerivative (stokesWeakTestDerivative ψ j) i) i
  have hright := stokesWeakTest_integral_ibp a.contDiff
    (stokesWeakTestDerivative (stokesWeakTestDerivative ψ i) i) j
  change (∫ x in U, a x * spatialDeriv (mixedSecond ψ.toFun i j) i x) =
    -(∫ x in U, spatialDeriv a.toFun i x * mixedSecond ψ.toFun i j x) at hleft
  change (∫ x in U, a x * spatialDeriv (mixedSecond ψ.toFun i i) j x) =
    -(∫ x in U, spatialDeriv a.toFun j x * mixedSecond ψ.toFun i i x) at hright
  rw [stokes_hessian_third_derivative ψ.contDiff i j] at hleft
  linarith

/-- The divergence of a genuine gradient test is the literal classical Laplacian. -/
theorem stokesScalarGradientTest_divergence_ae {U : Set Vec3} (ψ : WeakTestFunction U) :
    stokesEnergyDivergence U (stokesEnergyTest (stokesScalarGradientTest ψ))
      =ᵐ[volume.restrict U]
      spatialLaplacian ψ.toFun := by
  have h := stokesEnergyDivergence_test_ae (stokesScalarGradientTest ψ)
  exact h.trans (.of_forall fun x ↦ rfl)

/-- Hessian pairing of two genuine test gradients, expressed as a true integral. -/
theorem stokesTestGradient_inner_gradientTest {U : Set Vec3}
    (φ : StokesVectorTest U) (ψ : WeakTestFunction U) :
    inner ℝ (stokesTestGradientL2 φ)
      (stokesTestGradientL2 (stokesScalarGradientTest ψ)) =
        ∫ x in U, ∑ ij : Fin 3 × Fin 3,
          spatialDeriv (φ ij.2).toFun ij.1 x * mixedSecond ψ.toFun ij.1 ij.2 x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(stokesTestGradient_memLp φ).coeFn_toLp,
    (stokesTestGradient_memLp (stokesScalarGradientTest ψ)).coeFn_toLp] with x hx hy
  change stokesTestGradientL2 φ x = stokesTestGradient φ x at hx
  change stokesTestGradientL2 (stokesScalarGradientTest ψ) x =
    stokesTestGradient (stokesScalarGradientTest ψ) x at hy
  rw [hx, hy, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro ij _
  simp [stokesTestGradient, stokesScalarGradientTest, stokesWeakTestDerivative,
    WeakTestFunction.partialDeriv, mixedSecond, spatialDeriv, RCLike.inner_apply]
  ring

/-- The full actual Hessian identity on genuine compact vector tests. -/
theorem stokesEnergyTest_inner_gradientTest {U : Set Vec3}
    (φ : StokesVectorTest U) (ψ : WeakTestFunction U) :
    inner ℝ (stokesEnergyTest φ) (stokesEnergyTest (stokesScalarGradientTest ψ)) =
      inner ℝ (stokesEnergyDivergence U (stokesEnergyTest φ))
        (stokesEnergyDivergence U (stokesEnergyTest (stokesScalarGradientTest ψ))) := by
  change inner ℝ (stokesTestGradientL2 φ)
    (stokesTestGradientL2 (stokesScalarGradientTest ψ)) = _
  rw [stokesTestGradient_inner_gradientTest, L2.inner_def]
  have hright : (∫ x in U,
      inner ℝ (stokesEnergyDivergence U (stokesEnergyTest φ) x)
        (stokesEnergyDivergence U (stokesEnergyTest (stokesScalarGradientTest ψ)) x)) =
      ∫ x in U, (∑ j : Fin 3, spatialDeriv (φ j).toFun j x) *
        ∑ i : Fin 3, mixedSecond ψ.toFun i i x := by
    apply integral_congr_ae
    filter_upwards [stokesEnergyDivergence_test_ae φ,
      stokesScalarGradientTest_divergence_ae ψ] with x hx hy
    rw [hx, hy]
    simp only [spatialLaplacian, RCLike.inner_apply, conj_trivial,
      WeakTestFunction.partialDeriv, mixedSecond, spatialDeriv]
    ring
  rw [hright]
  have hInt (i j : Fin 3) : Integrable
      (fun x ↦ spatialDeriv (φ j).toFun i x * mixedSecond ψ.toFun i j x)
      (volume.restrict U) :=
    stokesWeakTest_integrableOn_mul
      (contDiff_spatialDeriv_smooth (φ j).contDiff i).continuous
      (stokesWeakTestDerivative (stokesWeakTestDerivative ψ j) i)
  have hIntDiag (i j : Fin 3) : Integrable
      (fun x ↦ spatialDeriv (φ j).toFun j x * mixedSecond ψ.toFun i i x)
      (volume.restrict U) :=
    stokesWeakTest_integrableOn_mul
      (contDiff_spatialDeriv_smooth (φ j).contDiff j).continuous
      (stokesWeakTestDerivative (stokesWeakTestDerivative ψ i) i)
  rw [integral_finsetSum Finset.univ (fun ij _ ↦ hInt ij.1 ij.2), Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ
    (fun j _ ↦ integrable_finsetSum _ fun i _ ↦ hIntDiag i j)]
  simp_rw [integral_finsetSum Finset.univ (fun i _ ↦ hIntDiag i _)]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact stokesWeakTest_hessian_ibp (φ j) ψ i j

/-- Actual Hessian integration by parts extends to every element of the completed energy space. -/
theorem stokesEnergy_inner_gradientTest {U : Set Vec3}
    (v : stokesGradientEnergySpace U) (ψ : WeakTestFunction U) :
    inner ℝ v (stokesEnergyTest (stokesScalarGradientTest ψ)) =
      inner ℝ (stokesEnergyDivergence U v)
        (stokesEnergyDivergence U (stokesEnergyTest (stokesScalarGradientTest ψ))) := by
  let g := stokesTestGradientL2 (stokesScalarGradientTest ψ)
  let D : StokesGradientL2 U →L[ℝ] Lp ℝ 2 (volume.restrict U) :=
    stokesMatrixTrace.compLpL 2 (volume.restrict U)
  let F : StokesGradientL2 U →L[ℝ] ℝ := innerSL ℝ g -
    (innerSL ℝ (D g)).comp D
  have hspan : Submodule.span ℝ (range (stokesTestGradientL2 (U := U))) ≤ F.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨φ, rfl⟩
    change inner ℝ g (stokesTestGradientL2 φ) -
      inner ℝ (D g) (D (stokesTestGradientL2 φ)) = 0
    rw [real_inner_comm (stokesTestGradientL2 φ) g,
      real_inner_comm (D (stokesTestGradientL2 φ)) (D g)]
    exact sub_eq_zero.mpr (stokesEnergyTest_inner_gradientTest φ ψ)
  have hclosure := Submodule.topologicalClosure_minimal _ hspan F.isClosed_ker
  have hv := hclosure v.property
  change inner ℝ g v.1 - inner ℝ (D g) (D v.1) = 0 at hv
  rw [real_inner_comm v.1 g, real_inner_comm (D v.1) (D g)] at hv
  exact sub_eq_zero.mp hv

/-- The genuine solenoidal Stokes solution has zero pairing with every compact gradient test. -/
theorem stokesEnergySolution_inner_gradientTest {U : Set Vec3}
    (F : StokesEnergyForce U) (ψ : WeakTestFunction U) :
    inner ℝ (stokesEnergySolution F : stokesGradientEnergySpace U)
      (stokesEnergyTest (stokesScalarGradientTest ψ)) = 0 := by
  rw [stokesEnergy_inner_gradientTest]
  have hdiv : stokesEnergyDivergence U
      (stokesEnergySolution F : stokesGradientEnergySpace U) = 0 :=
    (stokesEnergySolution F).property
  rw [hdiv, inner_zero_left]

/-- A genuine variational Stokes pressure is weakly harmonic for gradient-free source data. -/
theorem stokesPressure_weaklyHarmonic_of_gradient_tests {U : Set Vec3}
    (F : StokesEnergyForce U) (p : Lp ℝ 2 (volume.restrict U))
    (hp : ∀ v : stokesGradientEnergySpace U,
      inner ℝ (stokesEnergySolution F : stokesGradientEnergySpace U) v -
        inner ℝ p (stokesEnergyDivergence U v) = F v)
    (hF : ∀ ψ : WeakTestFunction U, F (stokesEnergyTest (stokesScalarGradientTest ψ)) = 0) :
    WeaklyHarmonicOn U (p : Vec3 → ℝ) := by
  intro ψ hψ hcompact hsub
  let φ : WeakTestFunction U := ⟨ψ, hψ, hcompact, hsub⟩
  have heq := hp (stokesEnergyTest (stokesScalarGradientTest φ))
  rw [stokesEnergySolution_inner_gradientTest, hF] at heq
  have hpair : inner ℝ p
      (stokesEnergyDivergence U (stokesEnergyTest (stokesScalarGradientTest φ))) = 0 :=
    by linarith
  rw [L2.inner_def] at hpair
  have hint : (∫ x in U, inner ℝ (p x)
      (stokesEnergyDivergence U (stokesEnergyTest (stokesScalarGradientTest φ)) x)) =
      ∫ x in U, p x * spatialLaplacian ψ x := by
    apply integral_congr_ae
    filter_upwards [stokesScalarGradientTest_divergence_ae φ] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  exact hint ▸ hpair

/-- Literal weakly divergence-free vector data give a genuinely harmonic Stokes pressure.
The source is specified by its actual compact-test integral, rather than a harmonicity premise. -/
theorem stokesPressure_weaklyHarmonic_of_divergenceFree_source {U : Set Vec3}
    (u : Vec3 → Vec3) (F : StokesEnergyForce U) (p : Lp ℝ 2 (volume.restrict U))
    (hp : ∀ v : stokesGradientEnergySpace U,
      inner ℝ (stokesEnergySolution F : stokesGradientEnergySpace U) v -
        inner ℝ p (stokesEnergyDivergence U v) = F v)
    (hforce : ∀ φ : StokesVectorTest U, F (stokesEnergyTest φ) =
      ∫ x in U, ∑ i : Fin 3, u x i * φ i x)
    (hdiv : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x in U, ∑ i : Fin 3, u x i * spatialDeriv ψ i x) = 0) :
    WeaklyHarmonicOn U (p : Vec3 → ℝ) := by
  apply stokesPressure_weaklyHarmonic_of_gradient_tests F p hp
  intro ψ
  rw [hforce]
  exact hdiv ψ.toFun ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset

end FluidSingularSets
