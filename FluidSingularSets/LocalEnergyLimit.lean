-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StrongLpIntegrands
public import FluidSingularSets.AcceleratedEnergyAlgebra
public import FluidSingularSets.WeakEquationLimit
public import CKN.ClassEquivalence.Constructor
public import CKN.Setting.Energy.AELocalEnergy

/-!
# Strong limits of the genuine local-energy polynomials

The local-energy density is an explicit sum of quadratic, cubic,
pressure-velocity and force-velocity monomials. Exact Holder exponents make
all these monomials integrable on a compact test support, and strong convergence
preserves their actual integrals. This gives the closed local energy inequality
needed when smooth frames approximate the actual absolutely continuous mean.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The genuine energy density is exactly the finite coordinate polynomial. -/
theorem frameEnergyPolynomial_eq_monomials (U F G : Vec3) (p ψ τ Λ : ℝ) :
    frameEnergyPolynomial U F G p ψ τ Λ =
      (∑ j : Fin 3, U j ^ 2 * (τ + Λ)) +
        (∑ i : Fin 3, ∑ j : Fin 3, (U j * U j) * U i * G i) +
          2 * (∑ i : Fin 3, (p * U i) * G i) +
            2 * (∑ i : Fin 3, (F i * U i) * ψ) := by
  have hnorm : vec3EuclideanNorm U ^ 2 = ∑ i : Fin 3, U i ^ 2 := by
    rw [vec3EuclideanNorm, Real.sq_sqrt
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg (U i))]
  simp only [frameEnergyPolynomial, hnorm, Fin.sum_univ_three]
  ring

private theorem localEnergy_holder_three_three :
    ENNReal.HolderTriple 3 3 (ENNReal.ofReal (3 / 2 : ℝ)) := by
  have h : Real.HolderTriple 3 3 (3 / 2 : ℝ) := by constructor <;> norm_num
  simpa using h.ennrealOfReal

private theorem localEnergy_holder_threeHalves_three :
    ENNReal.HolderTriple (ENNReal.ofReal (3 / 2 : ℝ)) 3 1 := by
  have h : Real.HolderTriple (3 / 2 : ℝ) 3 1 := by constructor <;> norm_num
  simpa using h.ennrealOfReal

/-- All four literal energy monomial families are genuinely integrable at the
exact suitable-solution exponents. -/
theorem localEnergy_monomials_integrable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {U F G : α → Vec3} {p ψ τ Λ : α → ℝ}
    (hU : ∀ i, MemLp (fun z ↦ U z i) 3 μ)
    (hF : ∀ i, MemLp (fun z ↦ F z i) (ENNReal.ofReal (3 / 2 : ℝ)) μ)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) μ)
    (hG : ∀ i, MemLp (fun z ↦ G z i) ⊤ μ)
    (hψ : MemLp ψ ⊤ μ) (hτ : MemLp τ ⊤ μ) (hΛ : MemLp Λ ⊤ μ) :
    (∀ j, Integrable (fun z ↦ U z j ^ 2 * (τ z + Λ z)) μ) ∧
      (∀ i j, Integrable (fun z ↦ (U z j * U z j) * U z i * G z i) μ) ∧
      (∀ i, Integrable (fun z ↦ (p z * U z i) * G z i) μ) ∧
      (∀ i, Integrable (fun z ↦ (F z i * U z i) * ψ z) μ) := by
  let : ENNReal.HolderTriple 3 3 (ENNReal.ofReal (3 / 2 : ℝ)) :=
    localEnergy_holder_three_three
  let : ENNReal.HolderTriple (ENNReal.ofReal (3 / 2 : ℝ)) 3 1 :=
    localEnergy_holder_threeHalves_three
  have hUU (j : Fin 3) : MemLp (fun z ↦ U z j * U z j)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := (hU j).mul (hU j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    have h := ((hUU j).mul (r := ENNReal.ofReal (3 / 2 : ℝ)) (hτ.add hΛ)).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ))
    simp only [sq]
    change Integrable ((fun z ↦ U z j * U z j) * (τ + Λ)) μ
    exact h
  · intro i j
    exact (((hUU j).mul (r := 1) (hU i)).mul (r := 1) (hG i)).integrable (by norm_num)
  · intro i
    exact ((hp.mul (r := 1) (hU i)).mul (r := 1) (hG i)).integrable (by norm_num)
  · intro i
    exact (((hF i).mul (r := 1) (hU i)).mul (r := 1) hψ).integrable (by norm_num)

/-- The integral of the actual energy density is the finite sum of its
integrable coordinate monomials. -/
theorem integral_frameEnergyPolynomial_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {U F G : α → Vec3} {p ψ τ Λ : α → ℝ}
    (hU : ∀ i, MemLp (fun z ↦ U z i) 3 μ)
    (hF : ∀ i, MemLp (fun z ↦ F z i) (ENNReal.ofReal (3 / 2 : ℝ)) μ)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) μ)
    (hG : ∀ i, MemLp (fun z ↦ G z i) ⊤ μ)
    (hψ : MemLp ψ ⊤ μ) (hτ : MemLp τ ⊤ μ) (hΛ : MemLp Λ ⊤ μ) :
    (∫ z, frameEnergyPolynomial (U z) (F z) (G z) (p z) (ψ z) (τ z) (Λ z) ∂μ) =
      (∑ j : Fin 3, ∫ z, U z j ^ 2 * (τ z + Λ z) ∂μ) +
        (∑ i : Fin 3, ∑ j : Fin 3, ∫ z, (U z j * U z j) * U z i * G z i ∂μ) +
          2 * (∑ i : Fin 3, ∫ z, (p z * U z i) * G z i ∂μ) +
            2 * (∑ i : Fin 3, ∫ z, (F z i * U z i) * ψ z ∂μ) := by
  obtain ⟨hA, hB, hC, hD⟩ := localEnergy_monomials_integrable hU hF hp hG hψ hτ hΛ
  have hAS : Integrable (fun z ↦ ∑ j : Fin 3, U z j ^ 2 * (τ z + Λ z)) μ :=
    integrable_finsetSum Finset.univ (fun j _ ↦ hA j)
  have hBS : Integrable
      (fun z ↦ ∑ i : Fin 3, ∑ j : Fin 3, (U z j * U z j) * U z i * G z i) μ :=
    integrable_finsetSum Finset.univ (fun i _ ↦
      integrable_finsetSum Finset.univ (fun j _ ↦ hB i j))
  have hCS : Integrable (fun z ↦ ∑ i : Fin 3, (p z * U z i) * G z i) μ :=
    integrable_finsetSum Finset.univ (fun i _ ↦ hC i)
  have hDS : Integrable (fun z ↦ ∑ i : Fin 3, (F z i * U z i) * ψ z) μ :=
    integrable_finsetSum Finset.univ (fun i _ ↦ hD i)
  simp_rw [frameEnergyPolynomial_eq_monomials]
  rw [integral_add
    (f := fun z ↦ (∑ j : Fin 3, U z j ^ 2 * (τ z + Λ z)) +
      (∑ i : Fin 3, ∑ j : Fin 3, (U z j * U z j) * U z i * G z i) +
        2 * (∑ i : Fin 3, (p z * U z i) * G z i))
    (g := fun z ↦ 2 * (∑ i : Fin 3, (F z i * U z i) * ψ z))
    ((hAS.add hBS).add (hCS.const_mul 2)) (hDS.const_mul 2),
    integral_add
      (f := fun z ↦ (∑ j : Fin 3, U z j ^ 2 * (τ z + Λ z)) +
        (∑ i : Fin 3, ∑ j : Fin 3, (U z j * U z j) * U z i * G z i))
      (g := fun z ↦ 2 * (∑ i : Fin 3, (p z * U z i) * G z i))
      (hAS.add hBS) (hCS.const_mul 2),
    integral_add (f := fun z ↦ ∑ j : Fin 3, U z j ^ 2 * (τ z + Λ z))
      (g := fun z ↦ ∑ i : Fin 3, ∑ j : Fin 3, (U z j * U z j) * U z i * G z i)
      hAS hBS, integral_const_mul, integral_const_mul]
  rw [integral_finsetSum Finset.univ (fun j _ ↦ hA j),
    integral_finsetSum Finset.univ (fun i _ ↦
      integrable_finsetSum Finset.univ (fun j _ ↦ hB i j)),
    integral_finsetSum Finset.univ (fun i _ ↦ hC i),
    integral_finsetSum Finset.univ (fun i _ ↦ hD i)]
  simp_rw [integral_finsetSum Finset.univ (fun j _ ↦ hB _ j)]

/-- Strong cubic velocity and three-halves pressure and force convergence
preserve the genuine local-energy polynomial integral. -/
theorem tendsto_integral_frameEnergyPolynomial
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {U F G : α → Vec3} {p ψ τ Λ : α → ℝ}
    {Us Fs : ℕ → α → Vec3} {ps : ℕ → α → ℝ}
    (hU : ∀ i, MemLp (fun z ↦ U z i) 3 μ)
    (hF : ∀ i, MemLp (fun z ↦ F z i) (ENNReal.ofReal (3 / 2 : ℝ)) μ)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) μ)
    (hUs : ∀ n i, MemLp (fun z ↦ Us n z i) 3 μ)
    (hFs : ∀ n i, MemLp (fun z ↦ Fs n z i) (ENNReal.ofReal (3 / 2 : ℝ)) μ)
    (hps : ∀ n, MemLp (ps n) (ENNReal.ofReal (3 / 2 : ℝ)) μ)
    (hG : ∀ i, MemLp (fun z ↦ G z i) ⊤ μ)
    (hψ : MemLp ψ ⊤ μ) (hτ : MemLp τ ⊤ μ) (hΛ : MemLp Λ ⊤ μ)
    (hUc : ∀ i, Tendsto (fun n ↦ eLpNorm (fun z ↦ Us n z i - U z i) 3 μ)
      atTop (𝓝 0))
    (hFc : ∀ i, Tendsto (fun n ↦ eLpNorm
      (fun z ↦ Fs n z i - F z i) (ENNReal.ofReal (3 / 2 : ℝ)) μ) atTop (𝓝 0))
    (hpc : Tendsto (fun n ↦ eLpNorm (ps n - p)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z,
      frameEnergyPolynomial (Us n z) (Fs n z) (G z) (ps n z) (ψ z) (τ z) (Λ z) ∂μ)
      atTop (𝓝 (∫ z,
        frameEnergyPolynomial (U z) (F z) (G z) (p z) (ψ z) (τ z) (Λ z) ∂μ)) := by
  let r : ℝ≥0∞ := ENNReal.ofReal (3 / 2 : ℝ)
  let : ENNReal.HolderTriple 3 3 r := localEnergy_holder_three_three
  let : ENNReal.HolderTriple r 3 1 := localEnergy_holder_threeHalves_three
  have hr : 1 ≤ r := by norm_num [r]
  have hrfin : r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hA (j : Fin 3) : Tendsto
      (fun n ↦ ∫ z, Us n z j ^ 2 * (τ z + Λ z) ∂μ) atTop
      (𝓝 (∫ z, U z j ^ 2 * (τ z + Λ z) ∂μ)) := by
    simp only [sq]
    change Tendsto (fun n ↦ ∫ z, (Us n z j * Us n z j) * (τ + Λ) z ∂μ)
      atTop (𝓝 (∫ z, (U z j * U z j) * (τ + Λ) z ∂μ))
    exact tendsto_integral_mul_mul_bounded
      (p := 3) (q := 3) (r := r) (by norm_num) (by norm_num) hr hrfin
      (hU j) (hU j) (fun n ↦ hUs n j) (fun n ↦ hUs n j) (hτ.add hΛ)
      (hUc j) (hUc j)
  have hB (i j : Fin 3) : Tendsto
      (fun n ↦ ∫ z, (Us n z j * Us n z j) * Us n z i * G z i ∂μ) atTop
      (𝓝 (∫ z, (U z j * U z j) * U z i * G z i ∂μ)) :=
    tendsto_integral_mul_mul_mul_bounded
      (p := 3) (q := 3) (s := 3) (r := r) (t := 1)
      (by norm_num) (by norm_num) (by norm_num) hr (by norm_num) (by norm_num)
      (hU j) (hU j) (hU i) (fun n ↦ hUs n j) (fun n ↦ hUs n j)
      (fun n ↦ hUs n i) (hG i) (hUc j) (hUc j) (hUc i)
  have hC (i : Fin 3) : Tendsto
      (fun n ↦ ∫ z, (ps n z * Us n z i) * G z i ∂μ) atTop
      (𝓝 (∫ z, (p z * U z i) * G z i ∂μ)) :=
    tendsto_integral_mul_mul_bounded
      (p := r) (q := 3) (r := 1) hr (by norm_num) (by norm_num) (by norm_num)
      hp (hU i) hps (fun n ↦ hUs n i) (hG i) hpc (hUc i)
  have hD (i : Fin 3) : Tendsto
      (fun n ↦ ∫ z, (Fs n z i * Us n z i) * ψ z ∂μ) atTop
      (𝓝 (∫ z, (F z i * U z i) * ψ z ∂μ)) :=
    tendsto_integral_mul_mul_bounded
      (p := r) (q := 3) (r := 1) hr (by norm_num) (by norm_num) (by norm_num)
      (hF i) (hU i) (fun n ↦ hFs n i) (fun n ↦ hUs n i) hψ (hFc i) (hUc i)
  simp_rw [integral_frameEnergyPolynomial_eq hU hF hp hG hψ hτ hΛ,
    integral_frameEnergyPolynomial_eq (hUs _) (hFs _) (hps _) hG hψ hτ hΛ]
  exact (((tendsto_finsetSum Finset.univ (fun j _ ↦ hA j)).add
    (tendsto_finsetSum Finset.univ (fun i _ ↦
      tendsto_finsetSum Finset.univ (fun j _ ↦ hB i j)))).add
        ((tendsto_finsetSum Finset.univ (fun i _ ↦ hC i)).const_mul 2)).add
          ((tendsto_finsetSum Finset.univ (fun i _ ↦ hD i)).const_mul 2)

/-- Strong quadratic gradient convergence preserves the actual tested
Frobenius dissipation integral. -/
theorem tendsto_integral_spatialGradientSq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {D : α → Fin 3 → Vec3}
    {Ds : ℕ → α → Fin 3 → Vec3} {ψ : α → ℝ}
    (hD : ∀ i j, MemLp (fun z ↦ D z i j) 2 μ)
    (hDs : ∀ n i j, MemLp (fun z ↦ Ds n z i j) 2 μ)
    (hψ : MemLp ψ ⊤ μ)
    (hDc : ∀ i j, Tendsto (fun n ↦ eLpNorm
      (fun z ↦ Ds n z i j - D z i j) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z, (∑ i : Fin 3, ∑ j : Fin 3, (Ds n z i j) ^ 2) * ψ z ∂μ)
      atTop (𝓝 (∫ z, (∑ i : Fin 3, ∑ j : Fin 3, (D z i j) ^ 2) * ψ z ∂μ)) := by
  let : ENNReal.HolderTriple 2 2 1 := by
    have h : Real.HolderTriple 2 2 1 := by constructor <;> norm_num
    simpa using h.ennrealOfReal
  have hterms (i j : Fin 3) : Tendsto
      (fun n ↦ ∫ z, (Ds n z i j) ^ 2 * ψ z ∂μ) atTop
      (𝓝 (∫ z, (D z i j) ^ 2 * ψ z ∂μ)) := by
    simpa only [sq] using tendsto_integral_mul_mul_bounded
      (p := 2) (q := 2) (r := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (hD i j) (hD i j)
      (fun n ↦ hDs n i j) (fun n ↦ hDs n i j) hψ (hDc i j) (hDc i j)
  have hInt (i j : Fin 3) : Integrable (fun z ↦ (D z i j) ^ 2 * ψ z) μ := by
    simp only [sq]
    change Integrable (((fun z ↦ D z i j) * (fun z ↦ D z i j)) * ψ) μ
    exact (((hD i j).mul (r := 1) (hD i j)).mul
      (r := 1) hψ).integrable (by norm_num)
  have hInts (n : ℕ) (i j : Fin 3) :
      Integrable (fun z ↦ (Ds n z i j) ^ 2 * ψ z) μ := by
    simp only [sq]
    change Integrable (((fun z ↦ Ds n z i j) * (fun z ↦ Ds n z i j)) * ψ) μ
    exact (((hDs n i j).mul (r := 1) (hDs n i j)).mul
      (r := 1) hψ).integrable (by norm_num)
  simp_rw [Finset.sum_mul,
    integral_finsetSum Finset.univ (fun i _ ↦
      integrable_finsetSum Finset.univ (fun j _ ↦ hInts _ i j)),
    integral_finsetSum Finset.univ (fun i _ ↦
      integrable_finsetSum Finset.univ (fun j _ ↦ hInt i j)),
    integral_finsetSum Finset.univ (fun j _ ↦ hInts _ _ j),
    integral_finsetSum Finset.univ (fun j _ ↦ hInt _ j)]
  exact tendsto_finsetSum Finset.univ (fun i _ ↦
    tendsto_finsetSum Finset.univ (fun j _ ↦ hterms i j))

/-- The true local energy inequality is closed under strong local field
limits. Both limit integrands are integrable from the actual data before
any integral inequality is consumed. -/
theorem suitable_localEnergy_of_strongLp
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {us : ℕ → ParabolicPoint → Vec3} {Ds : ℕ → ParabolicPoint → Fin 3 → Vec3}
    {ps : ℕ → ParabolicPoint → ℝ} {fs : ℕ → ParabolicPoint → Vec3}
    (hsols : ∀ n, IsSuitableWeakSolutionIntegrable Ω I q (us n) (Ds n) (ps n) (fs n))
    (hconv : ∀ K : Set ParabolicPoint, IsCompact K → K ⊆ spaceTimeSet Ω I →
      Tendsto (fun n ↦ eLpNorm (us n - u) 3 (volume.restrict K)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (Ds n - Du) 2 (volume.restrict K)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (ps n - p) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict K)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (fs n - f) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict K)) atTop (𝓝 0))
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hψnonneg : ∀ z, 0 ≤ ψ z) :
    IntegrableOn (fun z : ParabolicPoint ↦ spatialGradientSq u Du z * ψ z)
      (tsupport ψ) volume ∧
    IntegrableOn (fun z : ParabolicPoint ↦
      frameEnergyPolynomial (u z) (f z) (fun i ↦ spatialPartial ψ i z)
        (p z) (ψ z) (timePartial ψ z) (∑ i, spatialSecondPartial ψ i i z))
      (tsupport ψ) volume ∧
    2 * (∫ z in spaceTimeSet Ω I, spatialGradientSq u Du z * ψ z) ≤
      ∫ z in spaceTimeSet Ω I,
        frameEnergyPolynomial (u z) (f z) (fun i ↦ spatialPartial ψ i z)
          (p z) (ψ z) (timePartial ψ z) (∑ i, spatialSecondPartial ψ i i z) := by
  let K := tsupport (show ParabolicPoint → ℝ from ψ)
  have hK : IsCompact K := isCompact_tsupport_parabolic hψ.2.1
  have hKsub : K ⊆ spaceTimeSet Ω I := tsupport_parabolic_subset_spaceTimeSet hψ
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let r : ℝ≥0∞ := ENNReal.ofReal (3 / 2 : ℝ)
  have hqr : r ≤ ENNReal.ofReal q :=
    ENNReal.ofReal_le_ofReal (by linarith [hdata.five_halves_lt_exponent])
  have hu : MemLp u 3 (volume.restrict K) := by
    simpa using velocity_memLp_three_on_compact_of_data hdata hK hKsub
  have hus : ∀ n, MemLp (us n) 3 (volume.restrict K) := by
    intro n
    simpa using velocity_memLp_three_on_compact_of_data (hsols n).toData hK hKsub
  have hD := gradient_memLp_two_on_compact_of_data hdata hK hKsub
  have hDs := fun n ↦ gradient_memLp_two_on_compact_of_data (hsols n).toData hK hKsub
  have hp := pressure_memLp_threeHalves_on_compact_of_data hdata hK hKsub
  have hps := fun n ↦ pressure_memLp_threeHalves_on_compact_of_data (hsols n).toData hK hKsub
  have hf : MemLp f r (volume.restrict K) :=
    (force_memLp_on_compact_of_data hdata hK hKsub).mono_exponent hqr
  have hfs : ∀ n, MemLp (fs n) r (volume.restrict K) := fun n ↦
    (force_memLp_on_compact_of_data (hsols n).toData hK hKsub).mono_exponent hqr
  obtain ⟨huconv, hDconv, hpconv, hfconv⟩ := hconv K hK hKsub
  have huc (i : Fin 3) := tendsto_eLpNorm_pi_component_sub hu hus huconv i
  have hDc (i j : Fin 3) := tendsto_eLpNorm_pi_component_sub (memLp_pi_iff.mp hD i)
    (fun n ↦ memLp_pi_iff.mp (hDs n) i)
    (tendsto_eLpNorm_pi_component_sub hD hDs hDconv i) j
  have hfc (i : Fin 3) := tendsto_eLpNorm_pi_component_sub hf hfs hfconv i
  have hvalue : MemLp (fun z : ParabolicPoint ↦ ψ z) ⊤ (volume.restrict K) := by
    obtain ⟨C, hC⟩ := exists_bound_of_mem_spaceTimeTestFunction hψ
    exact MemLp.of_bound hψ.1.continuous.aestronglyMeasurable C (Eventually.of_forall hC)
  have htime : MemLp (fun z : ParabolicPoint ↦ timePartial ψ z) ⊤
      (volume.restrict K) := by
    obtain ⟨C, hC⟩ := exists_bound_timePartial_of_mem_spaceTimeTestFunction hψ
    exact MemLp.of_bound (contDiff_timePartial hψ.1).continuous.aestronglyMeasurable
      C (Eventually.of_forall hC)
  have hspace (i : Fin 3) : MemLp (fun z : ParabolicPoint ↦ spatialPartial ψ i z) ⊤
      (volume.restrict K) := by
    obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hψ i
    exact MemLp.of_bound (spatialPartial_contDiff hψ.1 i).continuous.aestronglyMeasurable
      C (Eventually.of_forall hC)
  have hsecond (i : Fin 3) : MemLp
      (fun z : ParabolicPoint ↦ spatialSecondPartial ψ i i z) ⊤ (volume.restrict K) := by
    obtain ⟨C, hC⟩ := exists_bound_spatialSecondPartial_of_mem_spaceTimeTestFunction hψ i i
    exact MemLp.of_bound
      (spatialPartial_contDiff (spatialPartial_contDiff hψ.1 i) i).continuous.aestronglyMeasurable
      C (Eventually.of_forall hC)
  have hlap : MemLp (fun z : ParabolicPoint ↦ ∑ i, spatialSecondPartial ψ i i z) ⊤
      (volume.restrict K) := memLp_finsetSum _ (fun i _ ↦ hsecond i)
  have hGlim := tendsto_integral_spatialGradientSq
    (fun i j ↦ memLp_pi_iff.mp (memLp_pi_iff.mp hD i) j)
    (fun n i j ↦ memLp_pi_iff.mp (memLp_pi_iff.mp (hDs n) i) j) hvalue hDc
  have hElim := tendsto_integral_frameEnergyPolynomial
    (memLp_pi_iff.mp hu) (memLp_pi_iff.mp hf) hp
    (fun n ↦ memLp_pi_iff.mp (hus n)) (fun n ↦ memLp_pi_iff.mp (hfs n)) hps
    hspace hvalue htime hlap huc hfc hpconv
  have hGoff (w : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
      (z : ParabolicPoint) (hz : z ∉ K) : spatialGradientSq w D z * ψ z = 0 := by
    exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hz)
  have hEoff (w F : ParabolicPoint → Vec3) (P : ParabolicPoint → ℝ)
      (z : ParabolicPoint) (hz : z ∉ K) :
      frameEnergyPolynomial (w z) (F z) (fun i ↦ spatialPartial ψ i z)
        (P z) (ψ z) (timePartial ψ z) (∑ i, spatialSecondPartial ψ i i z) = 0 := by
    change z ∉ tsupport (show ParabolicPoint → ℝ from ψ) at hz
    rw [tsupport_parabolic_eq] at hz
    have hzero := localEnergyRhs_eq_zero_of_not_mem_tsupport_public
      (u := w) (p := P) (f := F) hψ.1 hz
    simpa only [localEnergyRhs, frameEnergyPolynomial, timePartialProd,
      spatialPartialProd, spatialSecondPartialProd, Prod.eta] using hzero
  have hGDom (w : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3) :
      (∫ z in spaceTimeSet Ω I, spatialGradientSq w D z * ψ z) =
        ∫ z in K, spatialGradientSq w D z * ψ z := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz ↦
      hGoff w D z (fun hmem ↦ hz (hKsub hmem))),
      setIntegral_eq_integral_of_forall_compl_eq_zero (hGoff w D)]
  have hEDom (w F : ParabolicPoint → Vec3) (P : ParabolicPoint → ℝ) :
      (∫ z in spaceTimeSet Ω I,
        frameEnergyPolynomial (w z) (F z) (fun i ↦ spatialPartial ψ i z)
          (P z) (ψ z) (timePartial ψ z) (∑ i, spatialSecondPartial ψ i i z)) =
        ∫ z in K,
          frameEnergyPolynomial (w z) (F z) (fun i ↦ spatialPartial ψ i z)
            (P z) (ψ z) (timePartial ψ z) (∑ i, spatialSecondPartial ψ i i z) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz ↦
      hEoff w F P z (fun hmem ↦ hz (hKsub hmem))),
      setIntegral_eq_integral_of_forall_compl_eq_zero (hEoff w F P)]
  have hineqs (n : ℕ) :
      2 * (∫ z in K, spatialGradientSq (us n) (Ds n) z * ψ z) ≤
        ∫ z in K,
          frameEnergyPolynomial (us n z) (fs n z) (fun i ↦ spatialPartial ψ i z)
            (ps n z) (ψ z) (timePartial ψ z) (∑ i, spatialSecondPartial ψ i i z) := by
    rw [← hGDom, ← hEDom]
    exact ((hsols n).2.2.2.2.2.2.2.2 ψ hψ hψnonneg).2.2
  have hineq := le_of_tendsto_of_tendsto' (hGlim.const_mul 2) hElim hineqs
  refine ⟨dissipation_integrand_integrableOn_of_data hdata hψ, ?_, ?_⟩
  · exact localEnergy_integrand_integrableOn_of_data hdata hψ
  · rw [hGDom, hEDom]
    exact hineq

/-- Actual suitable solutions are closed under the strong compact field
limits needed by absolutely continuous accelerating frames. The limit data
are genuine analytic data, and all equations and the energy inequality are
proved here from the actual approximants. -/
theorem suitable_of_strongLp
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {us : ℕ → ParabolicPoint → Vec3} {Ds : ℕ → ParabolicPoint → Fin 3 → Vec3}
    {ps : ℕ → ParabolicPoint → ℝ} {fs : ℕ → ParabolicPoint → Vec3}
    (hsols : ∀ n, IsSuitableWeakSolutionIntegrable Ω I q (us n) (Ds n) (ps n) (fs n))
    (hconv : ∀ K : Set ParabolicPoint, IsCompact K → K ⊆ spaceTimeSet Ω I →
      Tendsto (fun n ↦ eLpNorm (us n - u) 3 (volume.restrict K)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (Ds n - Du) 2 (volume.restrict K)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (ps n - p) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict K)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (fs n - f) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict K)) atTop (𝓝 0)) :
    IsSuitableWeakSolutionIntegrable Ω I q u Du p f := by
  refine ⟨hdata.1, hdata.2.1, hdata.2.2.1, hdata.2.2.2.1, hdata.2.2.2.2.1,
    hdata.2.2.2.2.2, ?_, ?_, ?_⟩
  · intro ψ hψ
    exact suitable_divergence_of_strongLp hdata hsols
      (fun K hK hKsub ↦ (hconv K hK hKsub).1) hψ
  · intro φ hφ
    exact suitable_momentum_of_strongLp hdata hsols hconv hφ
  · intro ψ hψ hψnonneg
    exact suitable_localEnergy_of_strongLp hdata hsols hconv hψ hψnonneg

end FluidSingularSets
