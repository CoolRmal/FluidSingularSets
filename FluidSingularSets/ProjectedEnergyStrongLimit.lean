-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedEnergyAlgebra
public import FluidSingularSets.LocalEnergyLimit
public import FluidSingularSets.MixedSlicePairings

/-!
# Strong limits of the genuine projected energy deficit

The literal projected energy polynomial is an integrable finite sum of velocity,
corrected-gradient, pressure, and bounded-correction monomials. The harmonic
pressure contribution uses actual spatial L² classes with time L¹/L∞ control.
Their genuine mixed convergence preserves that spacetime integral and closes
the projected local energy inequality under the actual strong limits.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Actual jointly measurable scalar fields with genuine spatial L² slices and
an actual time class norm. No spacetime product integral is assumed. -/
structure ProjectedEnergySliceData
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    (μ : Measure A) (ν : Measure T) (b : ℝ≥0∞) (F : A × T → ℝ) : Prop where
  joint : AEStronglyMeasurable F (μ.prod ν)
  slices : ∀ᵐ t ∂ν, MemLp (fun x ↦ F (x, t)) 2 μ
  classMemLp : MemLp (actualSliceLp (μ := μ) (p := 2) F) b ν

/-- Strong convergence of the actual spatial L² class curves in their time norm. -/
structure ProjectedEnergySliceStrong
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    (μ : Measure A) (ν : Measure T) (b : ℝ≥0∞)
    (F : A × T → ℝ) (Fs : ℕ → A × T → ℝ) : Prop where
  limit : ProjectedEnergySliceData μ ν b F
  sequence : ∀ n, ProjectedEnergySliceData μ ν b (Fs n)
  strong : Tendsto (fun n ↦ eLpNorm
    (actualSliceLp (μ := μ) (p := 2) (Fs n) - actualSliceLp (μ := μ) (p := 2) F) b ν)
    atTop (𝓝 0)

/-- The literal tested projected velocity, used in the true mixed pressure pairing. -/
def projectedTestedVelocity {α : Type*} (U H G : α → Vec3) (z : α) : ℝ :=
  ∑ i : Fin 3, (U z i + H z i) * G z i

/-- The actual projected energy deficit is exactly its six monomial families. -/
theorem projectedEnergyDeficitPolynomial_eq_monomials
    (U H G : Vec3) (D B : Fin 3 → Vec3) (p Q ψ τ Λ : ℝ) :
    projectedEnergyDeficitPolynomial U H G D B (p - Q) ψ τ Λ =
      2 * (∑ i : Fin 3, ∑ j : Fin 3, ((D i j + B i j) * (D i j + B i j)) * ψ) -
        (∑ i : Fin 3, ((U i + H i) * (U i + H i)) * (τ + Λ)) -
          (∑ i : Fin 3, ∑ j : Fin 3,
            ((U i + H i) * (U i + H i)) * U j * G j) -
            2 * (∑ i : Fin 3, (p * (U i + H i)) * G i) +
              2 * (Q * ∑ i : Fin 3, (U i + H i) * G i) -
                2 * (∑ i : Fin 3, ∑ j : Fin 3, (U j * B i j) * (U i + H i) * ψ) := by
  have hnorm : vec3EuclideanNorm (U + H) ^ 2 = ∑ i : Fin 3, (U i + H i) ^ 2 := by
    rw [vec3EuclideanNorm, Real.sq_sqrt
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg ((U + H) i))]
    simp only [Pi.add_apply]
  simp only [projectedEnergyDeficitPolynomial, projectedGradientSquare, hnorm,
    Pi.add_apply, Fin.sum_univ_three]
  ring

private theorem projectedEnergy_holder_three_three :
    ENNReal.HolderTriple 3 3 (ENNReal.ofReal (3 / 2 : ℝ)) := by
  have h : Real.HolderTriple 3 3 (3 / 2 : ℝ) := by constructor <;> norm_num
  simpa using h.ennrealOfReal

private theorem projectedEnergy_holder_threeHalves_three :
    ENNReal.HolderTriple (ENNReal.ofReal (3 / 2 : ℝ)) 3 1 := by
  have h : Real.HolderTriple (3 / 2 : ℝ) 3 1 := by constructor <;> norm_num
  simpa using h.ennrealOfReal

private theorem projectedEnergy_holder_two_two : ENNReal.HolderTriple 2 2 1 := by
  have h : Real.HolderTriple 2 2 1 := by constructor <;> norm_num
  simpa using h.ennrealOfReal

/-- All six actual projected energy monomial families are genuinely integrable. -/
theorem projectedEnergy_monomials_integrable
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ : Measure A} {ν : Measure T} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {U H G : A × T → Vec3} {D B : A × T → Fin 3 → Vec3}
    {p Q ψ τ Λ : A × T → ℝ}
    (hU : ∀ i, MemLp (fun z ↦ U z i) 3 (μ.prod ν))
    (hV : ∀ i, MemLp (fun z ↦ U z i + H z i) 3 (μ.prod ν))
    (hW : ∀ i j, MemLp (fun z ↦ D z i j + B z i j) 2 (μ.prod ν))
    (hB : ∀ i j, MemLp (fun z ↦ B z i j) ⊤ (μ.prod ν))
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) (μ.prod ν))
    (hG : ∀ i, MemLp (fun z ↦ G z i) ⊤ (μ.prod ν))
    (hψ : MemLp ψ ⊤ (μ.prod ν)) (hτ : MemLp τ ⊤ (μ.prod ν))
    (hΛ : MemLp Λ ⊤ (μ.prod ν))
    (hQ : ProjectedEnergySliceData μ ν 1 Q)
    (hA : ProjectedEnergySliceData μ ν ⊤ (projectedTestedVelocity U H G)) :
    (∀ i j, Integrable (fun z ↦
      ((D z i j + B z i j) * (D z i j + B z i j)) * ψ z) (μ.prod ν)) ∧
      (∀ i, Integrable (fun z ↦
        ((U z i + H z i) * (U z i + H z i)) * (τ z + Λ z)) (μ.prod ν)) ∧
      (∀ i j, Integrable (fun z ↦
        ((U z i + H z i) * (U z i + H z i)) * U z j * G z j) (μ.prod ν)) ∧
      (∀ i, Integrable (fun z ↦ (p z * (U z i + H z i)) * G z i) (μ.prod ν)) ∧
      Integrable (fun z ↦ Q z * projectedTestedVelocity U H G z) (μ.prod ν) ∧
      ∀ i j, Integrable (fun z ↦
        (U z j * B z i j) * (U z i + H z i) * ψ z) (μ.prod ν) := by
  let r : ℝ≥0∞ := ENNReal.ofReal (3 / 2 : ℝ)
  let : ENNReal.HolderTriple 3 3 r := projectedEnergy_holder_three_three
  let : ENNReal.HolderTriple r 3 1 := projectedEnergy_holder_threeHalves_three
  let : ENNReal.HolderTriple 2 2 1 := projectedEnergy_holder_two_two
  have hVV (i : Fin 3) : MemLp (fun z ↦
      (U z i + H z i) * (U z i + H z i)) r (μ.prod ν) := (hV i).mul (hV i)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact (((hW i j).mul (r := 1) (hW i j)).mul (r := 1) hψ).integrable (by norm_num)
  · intro i
    exact ((hVV i).mul (r := r) (hτ.add hΛ)).integrable (by norm_num [r])
  · intro i j
    exact (((hVV i).mul (r := 1) (hU j)).mul (r := 1) (hG j)).integrable (by norm_num)
  · intro i
    exact ((hp.mul (r := 1) (hV i)).mul (r := 1) (hG i)).integrable (by norm_num)
  · exact integrable_mul_of_actualSliceLp_one_top hQ.joint hA.joint
      hQ.slices hA.slices hQ.classMemLp hA.classMemLp
  · intro i j
    exact ((((hU j).mul (r := 3) (hB i j)).mul (r := r) (hV i)).mul
      (r := r) hψ).integrable (by norm_num [r])

private theorem integral_projected_six_terms
    {α : Type*} [MeasurableSpace α] {ρ : Measure α} {a b c d e f : α → ℝ}
    (ha : Integrable a ρ) (hb : Integrable b ρ) (hc : Integrable c ρ)
    (hd : Integrable d ρ) (he : Integrable e ρ) (hf : Integrable f ρ) :
    (∫ z, 2 * a z - b z - c z - 2 * d z + 2 * e z - 2 * f z ∂ρ) =
      2 * (∫ z, a z ∂ρ) - (∫ z, b z ∂ρ) - (∫ z, c z ∂ρ) -
        2 * (∫ z, d z ∂ρ) + 2 * (∫ z, e z ∂ρ) - 2 * (∫ z, f z ∂ρ) := by
  have ha2 := ha.const_mul 2
  have hd2 := hd.const_mul 2
  have he2 := he.const_mul 2
  have hf2 := hf.const_mul 2
  rw [integral_sub
    (f := fun z ↦ 2 * a z - b z - c z - 2 * d z + 2 * e z)
    (g := fun z ↦ 2 * f z) ((((ha2.sub hb).sub hc).sub hd2).add he2) hf2,
    integral_add (f := fun z ↦ 2 * a z - b z - c z - 2 * d z)
      (g := fun z ↦ 2 * e z) (((ha2.sub hb).sub hc).sub hd2) he2,
    integral_sub (f := fun z ↦ 2 * a z - b z - c z)
      (g := fun z ↦ 2 * d z) ((ha2.sub hb).sub hc) hd2,
    integral_sub (f := fun z ↦ 2 * a z - b z) (g := c) (ha2.sub hb) hc,
    integral_sub (f := fun z ↦ 2 * a z) (g := b) ha2 hb]
  simp only [integral_const_mul]

/-- The genuine projected energy polynomial is integrable, and its actual
integral is the sum of the six integrable coordinate monomial families. -/
theorem integral_projectedEnergyDeficitPolynomial_eq
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ : Measure A} {ν : Measure T} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {U H G : A × T → Vec3} {D B : A × T → Fin 3 → Vec3}
    {p Q ψ τ Λ : A × T → ℝ}
    (hU : ∀ i, MemLp (fun z ↦ U z i) 3 (μ.prod ν))
    (hV : ∀ i, MemLp (fun z ↦ U z i + H z i) 3 (μ.prod ν))
    (hW : ∀ i j, MemLp (fun z ↦ D z i j + B z i j) 2 (μ.prod ν))
    (hB : ∀ i j, MemLp (fun z ↦ B z i j) ⊤ (μ.prod ν))
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) (μ.prod ν))
    (hG : ∀ i, MemLp (fun z ↦ G z i) ⊤ (μ.prod ν))
    (hψ : MemLp ψ ⊤ (μ.prod ν)) (hτ : MemLp τ ⊤ (μ.prod ν))
    (hΛ : MemLp Λ ⊤ (μ.prod ν))
    (hQ : ProjectedEnergySliceData μ ν 1 Q)
    (hA : ProjectedEnergySliceData μ ν ⊤ (projectedTestedVelocity U H G)) :
    Integrable (fun z ↦ projectedEnergyDeficitPolynomial (U z) (H z) (G z)
      (D z) (B z) (p z - Q z) (ψ z) (τ z) (Λ z)) (μ.prod ν) ∧
      (∫ z, projectedEnergyDeficitPolynomial (U z) (H z) (G z)
        (D z) (B z) (p z - Q z) (ψ z) (τ z) (Λ z) ∂μ.prod ν) =
        2 * (∑ i : Fin 3, ∑ j : Fin 3, ∫ z,
          ((D z i j + B z i j) * (D z i j + B z i j)) * ψ z ∂μ.prod ν) -
          (∑ i : Fin 3, ∫ z,
            ((U z i + H z i) * (U z i + H z i)) * (τ z + Λ z) ∂μ.prod ν) -
            (∑ i : Fin 3, ∑ j : Fin 3, ∫ z,
              ((U z i + H z i) * (U z i + H z i)) * U z j * G z j ∂μ.prod ν) -
              2 * (∑ i : Fin 3, ∫ z,
                (p z * (U z i + H z i)) * G z i ∂μ.prod ν) +
                2 * (∫ z, Q z * projectedTestedVelocity U H G z ∂μ.prod ν) -
                  2 * (∑ i : Fin 3, ∑ j : Fin 3, ∫ z,
                    (U z j * B z i j) * (U z i + H z i) * ψ z ∂μ.prod ν) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    projectedEnergy_monomials_integrable hU hV hW hB hp hG hψ hτ hΛ hQ hA
  let a := fun z ↦ ∑ i : Fin 3, ∑ j : Fin 3,
    ((D z i j + B z i j) * (D z i j + B z i j)) * ψ z
  let b := fun z ↦ ∑ i : Fin 3,
    ((U z i + H z i) * (U z i + H z i)) * (τ z + Λ z)
  let c := fun z ↦ ∑ i : Fin 3, ∑ j : Fin 3,
    ((U z i + H z i) * (U z i + H z i)) * U z j * G z j
  let d := fun z ↦ ∑ i : Fin 3, (p z * (U z i + H z i)) * G z i
  let e := fun z ↦ Q z * projectedTestedVelocity U H G z
  let f := fun z ↦ ∑ i : Fin 3, ∑ j : Fin 3,
    (U z j * B z i j) * (U z i + H z i) * ψ z
  have ha : Integrable a (μ.prod ν) := integrable_finsetSum Finset.univ fun i _ ↦
    integrable_finsetSum Finset.univ fun j _ ↦ h1 i j
  have hb : Integrable b (μ.prod ν) := integrable_finsetSum Finset.univ fun i _ ↦ h2 i
  have hc : Integrable c (μ.prod ν) := integrable_finsetSum Finset.univ fun i _ ↦
    integrable_finsetSum Finset.univ fun j _ ↦ h3 i j
  have hd : Integrable d (μ.prod ν) := integrable_finsetSum Finset.univ fun i _ ↦ h4 i
  have he : Integrable e (μ.prod ν) := h5
  have hf : Integrable f (μ.prod ν) := integrable_finsetSum Finset.univ fun i _ ↦
    integrable_finsetSum Finset.univ fun j _ ↦ h6 i j
  have hpoly (z : A × T) : projectedEnergyDeficitPolynomial (U z) (H z) (G z)
      (D z) (B z) (p z - Q z) (ψ z) (τ z) (Λ z) =
        2 * a z - b z - c z - 2 * d z + 2 * e z - 2 * f z :=
    projectedEnergyDeficitPolynomial_eq_monomials (U z) (H z) (G z) (D z) (B z)
      (p z) (Q z) (ψ z) (τ z) (Λ z)
  constructor
  · have hh := ((((ha.const_mul 2).sub hb).sub hc).sub (hd.const_mul 2)).add
      (he.const_mul 2) |>.sub (hf.const_mul 2)
    exact hh.congr (Eventually.of_forall fun z ↦ (hpoly z).symm)
  · simp_rw [hpoly]
    rw [integral_projected_six_terms ha hb hc hd he hf]
    dsimp only [a, b, c, d, e, f]
    rw [integral_finsetSum Finset.univ (fun i _ ↦
        integrable_finsetSum Finset.univ (fun j _ ↦ h1 i j)),
      integral_finsetSum Finset.univ (fun i _ ↦ h2 i),
      integral_finsetSum Finset.univ (fun i _ ↦
        integrable_finsetSum Finset.univ (fun j _ ↦ h3 i j)),
      integral_finsetSum Finset.univ (fun i _ ↦ h4 i),
      integral_finsetSum Finset.univ (fun i _ ↦
        integrable_finsetSum Finset.univ (fun j _ ↦ h6 i j))]
    simp_rw [integral_finsetSum Finset.univ (fun j _ ↦ h1 _ j),
      integral_finsetSum Finset.univ (fun j _ ↦ h3 _ j),
      integral_finsetSum Finset.univ (fun j _ ↦ h6 _ j)]

section StrongLimit

variable {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
  {μ : Measure A} {ν : Measure T} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {U H G : A × T → Vec3} {D B : A × T → Fin 3 → Vec3}
  {p Q ψ τ Λ : A × T → ℝ}
  {Hs : ℕ → A × T → Vec3} {Bs : ℕ → A × T → Fin 3 → Vec3}
  {Qs : ℕ → A × T → ℝ}
  (hU : ∀ i, MemLp (fun z ↦ U z i) 3 (μ.prod ν))
  (hV : ∀ i, MemLp (fun z ↦ U z i + H z i) 3 (μ.prod ν))
  (hW : ∀ i j, MemLp (fun z ↦ D z i j + B z i j) 2 (μ.prod ν))
  (hB : ∀ i j, MemLp (fun z ↦ B z i j) ⊤ (μ.prod ν))
  (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) (μ.prod ν))
  (hVs : ∀ n i, MemLp (fun z ↦ U z i + Hs n z i) 3 (μ.prod ν))
  (hWs : ∀ n i j, MemLp (fun z ↦ D z i j + Bs n z i j) 2 (μ.prod ν))
  (hBs : ∀ n i j, MemLp (fun z ↦ Bs n z i j) ⊤ (μ.prod ν))
  (hG : ∀ i, MemLp (fun z ↦ G z i) ⊤ (μ.prod ν))
  (hψ : MemLp ψ ⊤ (μ.prod ν)) (hτ : MemLp τ ⊤ (μ.prod ν))
  (hΛ : MemLp Λ ⊤ (μ.prod ν))
  (hVc : ∀ i, Tendsto (fun n ↦ eLpNorm
    (fun z ↦ (U z i + Hs n z i) - (U z i + H z i)) 3 (μ.prod ν)) atTop (𝓝 0))
  (hWc : ∀ i j, Tendsto (fun n ↦ eLpNorm
    (fun z ↦ (D z i j + Bs n z i j) - (D z i j + B z i j)) 2 (μ.prod ν)) atTop (𝓝 0))
  (hBc : ∀ i j, Tendsto (fun n ↦ eLpNorm
    (fun z ↦ Bs n z i j - B z i j) ⊤ (μ.prod ν)) atTop (𝓝 0))
  (hQ : ProjectedEnergySliceStrong μ ν 1 Q Qs)
  (hA : ProjectedEnergySliceStrong μ ν ⊤ (projectedTestedVelocity U H G)
    (fun n ↦ projectedTestedVelocity U (Hs n) G))

include hU hV hW hB hp hVs hWs hBs hG hψ hτ hΛ hVc hWc hBc hQ hA

/-- Strong corrected-velocity and corrected-gradient limits, bounded correction
limits, and actual mixed pressure class limits preserve the ordinary integral of
the literal projected energy deficit. -/
theorem tendsto_integral_projectedEnergyDeficitPolynomial :
    Tendsto (fun n ↦ ∫ z,
      projectedEnergyDeficitPolynomial (U z) (Hs n z) (G z) (D z) (Bs n z)
        (p z - Qs n z) (ψ z) (τ z) (Λ z) ∂μ.prod ν) atTop
      (𝓝 (∫ z, projectedEnergyDeficitPolynomial (U z) (H z) (G z) (D z) (B z)
        (p z - Q z) (ψ z) (τ z) (Λ z) ∂μ.prod ν)) := by
  let r : ℝ≥0∞ := ENNReal.ofReal (3 / 2 : ℝ)
  let : ENNReal.HolderTriple 3 3 r := projectedEnergy_holder_three_three
  let : ENNReal.HolderTriple r 3 1 := projectedEnergy_holder_threeHalves_three
  let : ENNReal.HolderTriple 2 2 1 := projectedEnergy_holder_two_two
  have hr : 1 ≤ r := by norm_num [r]
  have hrfin : r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hUc (i : Fin 3) : Tendsto (fun _n : ℕ ↦
      eLpNorm ((fun z ↦ U z i) - (fun z ↦ U z i)) 3 (μ.prod ν)) atTop (𝓝 0) := by
    simp
  have hpc : Tendsto (fun _n : ℕ ↦ eLpNorm (p - p) r (μ.prod ν)) atTop (𝓝 0) := by
    simp
  have h1 (i j : Fin 3) : Tendsto (fun n ↦ ∫ z,
      ((D z i j + Bs n z i j) * (D z i j + Bs n z i j)) * ψ z ∂μ.prod ν) atTop
      (𝓝 (∫ z, ((D z i j + B z i j) * (D z i j + B z i j)) * ψ z ∂μ.prod ν)) :=
    tendsto_integral_mul_mul_bounded (p := 2) (q := 2) (r := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hW i j) (hW i j) (fun n ↦ hWs n i j) (fun n ↦ hWs n i j)
      hψ (hWc i j) (hWc i j)
  have h2 (i : Fin 3) : Tendsto (fun n ↦ ∫ z,
      ((U z i + Hs n z i) * (U z i + Hs n z i)) * (τ z + Λ z) ∂μ.prod ν) atTop
      (𝓝 (∫ z, ((U z i + H z i) * (U z i + H z i)) * (τ z + Λ z) ∂μ.prod ν)) :=
    tendsto_integral_mul_mul_bounded (p := 3) (q := 3) (r := r)
      (by norm_num) (by norm_num) hr hrfin (hV i) (hV i)
      (fun n ↦ hVs n i) (fun n ↦ hVs n i) (hτ.add hΛ) (hVc i) (hVc i)
  have h3 (i j : Fin 3) : Tendsto (fun n ↦ ∫ z,
      ((U z i + Hs n z i) * (U z i + Hs n z i)) * U z j * G z j ∂μ.prod ν) atTop
      (𝓝 (∫ z, ((U z i + H z i) * (U z i + H z i)) * U z j * G z j ∂μ.prod ν)) :=
    tendsto_integral_mul_mul_mul_bounded (p := 3) (q := 3) (s := 3) (r := r) (t := 1)
      (by norm_num) (by norm_num) (by norm_num) hr (by norm_num) (by norm_num)
      (hV i) (hV i) (hU j) (fun n ↦ hVs n i) (fun n ↦ hVs n i) (fun _ ↦ hU j)
      (hG j) (hVc i) (hVc i) (hUc j)
  have h4 (i : Fin 3) : Tendsto (fun n ↦ ∫ z,
      (p z * (U z i + Hs n z i)) * G z i ∂μ.prod ν) atTop
      (𝓝 (∫ z, (p z * (U z i + H z i)) * G z i ∂μ.prod ν)) :=
    tendsto_integral_mul_mul_bounded (p := r) (q := 3) (r := 1)
      hr (by norm_num) (by norm_num) (by norm_num) hp (hV i)
      (fun _ ↦ hp) (fun n ↦ hVs n i) (hG i) hpc (hVc i)
  have h5 : Tendsto (fun n ↦ ∫ z,
      Qs n z * projectedTestedVelocity U (Hs n) G z ∂μ.prod ν) atTop
      (𝓝 (∫ z, Q z * projectedTestedVelocity U H G z ∂μ.prod ν)) :=
    tendsto_integral_mul_actualSliceLp_one_top hQ.limit.joint hA.limit.joint
      hQ.limit.slices hA.limit.slices hQ.limit.classMemLp hA.limit.classMemLp
      (fun n ↦ (hQ.sequence n).joint) (fun n ↦ (hA.sequence n).joint)
      (fun n ↦ (hQ.sequence n).slices) (fun n ↦ (hA.sequence n).slices)
      (fun n ↦ (hQ.sequence n).classMemLp) (fun n ↦ (hA.sequence n).classMemLp)
      hQ.strong hA.strong
  have h6 (i j : Fin 3) : Tendsto (fun n ↦ ∫ z,
      (U z j * Bs n z i j) * (U z i + Hs n z i) * ψ z ∂μ.prod ν) atTop
      (𝓝 (∫ z, (U z j * B z i j) * (U z i + H z i) * ψ z ∂μ.prod ν)) :=
    tendsto_integral_mul_mul_mul_bounded (p := 3) (q := ⊤) (s := 3) (r := 3) (t := r)
      (by norm_num) (by simp) (by norm_num) (by norm_num) hr hrfin
      (hU j) (hB i j) (hV i) (fun _ ↦ hU j) (fun n ↦ hBs n i j)
      (fun n ↦ hVs n i) hψ (hUc j) (hBc i j) (hVc i)
  have hn (n : ℕ) := (integral_projectedEnergyDeficitPolynomial_eq hU (hVs n) (hWs n)
    (hBs n) hp hG hψ hτ hΛ (hQ.sequence n) (hA.sequence n)).2
  have hlim := (integral_projectedEnergyDeficitPolynomial_eq hU hV hW hB hp hG hψ hτ hΛ
    hQ.limit hA.limit).2
  simp_rw [hn, hlim]
  exact (((((tendsto_finsetSum Finset.univ (fun i _ ↦
    tendsto_finsetSum Finset.univ (fun j _ ↦ h1 i j))).const_mul 2).sub
      (tendsto_finsetSum Finset.univ (fun i _ ↦ h2 i))).sub
        (tendsto_finsetSum Finset.univ (fun i _ ↦
          tendsto_finsetSum Finset.univ (fun j _ ↦ h3 i j)))).sub
            ((tendsto_finsetSum Finset.univ (fun i _ ↦ h4 i)).const_mul 2)).add
              (h5.const_mul 2) |>.sub
                ((tendsto_finsetSum Finset.univ (fun i _ ↦
                  tendsto_finsetSum Finset.univ (fun j _ ↦ h6 i j))).const_mul 2)

/-- The actual projected local energy deficit remains nonpositive under the true
strong limits. Integrability of the limit is proved before taking the inequality. -/
theorem projectedEnergy_inequality_of_strongLp
    (hLEI : ∀ᶠ n in atTop,
      (∫ z, projectedEnergyDeficitPolynomial (U z) (Hs n z) (G z) (D z) (Bs n z)
        (p z - Qs n z) (ψ z) (τ z) (Λ z) ∂μ.prod ν) ≤ 0) :
    Integrable (fun z ↦ projectedEnergyDeficitPolynomial (U z) (H z) (G z)
      (D z) (B z) (p z - Q z) (ψ z) (τ z) (Λ z)) (μ.prod ν) ∧
      (∫ z, projectedEnergyDeficitPolynomial (U z) (H z) (G z) (D z) (B z)
        (p z - Q z) (ψ z) (τ z) (Λ z) ∂μ.prod ν) ≤ 0 := by
  have hconv := tendsto_integral_projectedEnergyDeficitPolynomial hU hV hW hB hp
    hVs hWs hBs hG hψ hτ hΛ hVc hWc hBc hQ hA
  refine ⟨(integral_projectedEnergyDeficitPolynomial_eq hU hV hW hB hp hG hψ hτ hΛ
    hQ.limit hA.limit).1, ?_⟩
  exact le_of_tendsto_of_tendsto hconv tendsto_const_nhds hLEI

end StrongLimit

end FluidSingularSets
