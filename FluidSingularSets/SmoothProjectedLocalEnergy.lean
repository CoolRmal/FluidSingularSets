-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.HarmonicScalarEnergyCancellation

/-!
# Genuine projected local energy for smooth harmonic corrections

The original suitable weak momentum, divergence, gradient and energy equations
imply the projected compact-test energy inequality. The correction is smooth,
harmonic and divergence free on the support of the test, and its true time
derivative is the gradient of the smooth pressure correction there. Every
cancelling density is proved integrable using the original suitable solution.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The literal scalar weak-gradient spatial correction. -/
def projectedScalarSpatialCorrection (U H G : Vec3) (D B : Fin 3 → Vec3)
    (ψ Λ : ℝ) (i : Fin 3) : ℝ :=
  2 * (∑ j, D i j * B i j) * ψ - 2 * U i * H i * Λ -
    2 * (∑ j, D i j * H i * G j)

/-- The literal scalar harmonic square correction, including its time derivative. -/
def projectedScalarSquareCorrection (H A : Vec3) (B : Fin 3 → Vec3)
    (ψ τ Λ : ℝ) (i : Fin 3) : ℝ :=
  2 * (∑ j, B i j ^ 2) * ψ - H i ^ 2 * τ - H i ^ 2 * Λ -
    2 * H i * A i * ψ

/-- The literal scalar divergence cancellation in the correction convection. -/
def projectedScalarConvectionCorrection (U H G : Vec3) (B : Fin 3 → Vec3)
    (ψ : ℝ) (i : Fin 3) : ℝ :=
  2 * (∑ j, U j * H i * B i j) * ψ + H i ^ 2 * (∑ j, U j * G j)

/-- The exact energy expansion grouped into the genuine scalar cancellation densities. -/
theorem projected_energy_scalar_decomposition (U H A G : Vec3)
    (D B : Fin 3 → Vec3) (p Q ψ τ Λ : ℝ) :
    projectedEnergyDeficitPolynomial U H G D B (p - Q) ψ τ Λ -
      originalEnergyDeficitPolynomial U G D p ψ τ Λ -
        2 * harmonicCorrectionMomentumPolynomial U H A G D B p ψ τ =
      (∑ i, (projectedScalarSpatialCorrection U H G D B ψ Λ i +
        projectedScalarSquareCorrection H A B ψ τ Λ i -
          projectedScalarConvectionCorrection U H G B ψ i)) +
        2 * ((∑ i, (U i + H i) * A i) * ψ +
          Q * (∑ i, (U i + H i) * G i)) + 2 * p * (∑ i, B i i) * ψ := by
  refine (projected_relative_energy_expansion U H A G D B p (p - Q) ψ τ Λ).trans ?_
  have hnorm : vec3EuclideanNorm H ^ 2 = ∑ i, H i ^ 2 := by
    rw [vec3EuclideanNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  simp only [projectedScalarSpatialCorrection, projectedScalarSquareCorrection,
    projectedScalarConvectionCorrection, projectedGradientSquare, hnorm, Fin.sum_univ_three]
  ring

/-- The actual grouped correction density for smooth harmonic pressure data. -/
def smoothProjectedEnergyCorrection
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (H : Vec3 × ℝ → Vec3) (Q ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  (∑ i, (projectedScalarSpatialCorrection (u z) (H z)
    (fun j ↦ spatialPartial ψ j z) (Du z)
    (fun i j ↦ spatialPartial (fun w ↦ H w i) j z) (ψ z)
    (∑ j, spatialSecondPartial ψ j j z) i +
      projectedScalarSquareCorrection (H z) (fun i ↦ timePartial (fun w ↦ H w i) z)
        (fun i j ↦ spatialPartial (fun w ↦ H w i) j z) (ψ z) (timePartial ψ z)
        (∑ j, spatialSecondPartial ψ j j z) i -
          projectedScalarConvectionCorrection (u z) (H z)
            (fun j ↦ spatialPartial ψ j z)
            (fun i j ↦ spatialPartial (fun w ↦ H w i) j z) (ψ z) i)) +
    2 * ((∑ i, (u z i + H z i) * spatialPartial Q i z) * ψ z +
      Q z * (∑ i, (u z i + H z i) * spatialPartial ψ i z))

/-- Actual suitable equations annihilate the grouped harmonic energy correction. -/
theorem suitable_smooth_projected_energy_correction_zero
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {H : Vec3 × ℝ → Vec3} {Q ψ : Vec3 × ℝ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hh : ∀ i z, z ∈ tsupport ψ →
      (∑ j : Fin 3, spatialSecondPartial (fun w ↦ H w i) j j z) = 0)
    (hdiv : ∀ z ∈ tsupport ψ,
      (∑ i : Fin 3, spatialPartial (fun w ↦ H w i) i z) = 0) :
    Integrable (smoothProjectedEnergyCorrection u Du H Q ψ) volume ∧
      (∫ z, smoothProjectedEnergyCorrection u Du H Q ψ z) = 0 := by
  let S : Fin 3 → Vec3 × ℝ → ℝ := fun i z ↦
    projectedScalarSpatialCorrection (u z) (H z) (fun j ↦ spatialPartial ψ j z)
      (Du z) (fun i j ↦ spatialPartial (fun w ↦ H w i) j z) (ψ z)
      (∑ j, spatialSecondPartial ψ j j z) i
  let T : Fin 3 → Vec3 × ℝ → ℝ := fun i z ↦
    projectedScalarSquareCorrection (H z) (fun i ↦ timePartial (fun w ↦ H w i) z)
      (fun i j ↦ spatialPartial (fun w ↦ H w i) j z) (ψ z) (timePartial ψ z)
      (∑ j, spatialSecondPartial ψ j j z) i
  let C : Fin 3 → Vec3 × ℝ → ℝ := fun i z ↦
    projectedScalarConvectionCorrection (u z) (H z) (fun j ↦ spatialPartial ψ j z)
      (fun i j ↦ spatialPartial (fun w ↦ H w i) j z) (ψ z) i
  let P : Vec3 × ℝ → ℝ := fun z ↦
    (∑ i, (u z i + H z i) * spatialPartial Q i z) * ψ z +
      Q z * (∑ i, (u z i + H z i) * spatialPartial ψ i z)
  have hHi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ ↦ H z i) :=
    (contDiff_apply ℝ ℝ i).comp hH
  have hS (i : Fin 3) : Integrable (S i) volume ∧ (∫ z, S i z) = 0 :=
    suitable_harmonic_spatial_energy_correction_zero hsol (hHi i) hψ (hh i) i
  have hT (i : Fin 3) : Integrable (T i) volume ∧ (∫ z, T i z) = 0 :=
    smooth_harmonic_square_energy_correction_zero (hHi i) hψ.1 hψ.2.1 (hh i)
  have hC (i : Fin 3) : Integrable (C i) volume ∧ (∫ z, C i z) = 0 :=
    suitable_smooth_square_convection_pairing hsol (hHi i) hψ
  have hP : Integrable P volume ∧ (∫ z, P z) = 0 :=
    suitable_smooth_projected_pressure_pairing hsol hH hQ hψ hdiv
  have hsum : Integrable (fun z : Vec3 × ℝ ↦ ∑ i, (S i z + T i z - C i z)) volume :=
    integrable_finsetSum _ fun i _ ↦ ((hS i).1.add (hT i).1).sub (hC i).1
  have hzsum : (∫ z : Vec3 × ℝ, ∑ i, (S i z + T i z - C i z)) = 0 := by
    calc
      _ = ∑ i : Fin 3, ∫ z : Vec3 × ℝ, S i z + T i z - C i z :=
        integral_finsetSum _ fun i _ ↦ ((hS i).1.add (hT i).1).sub (hC i).1
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hST : (∫ z, S i z + T i z) = (∫ z, S i z) + (∫ z, T i z) :=
          integral_add (hS i).1 (hT i).1
        calc
          _ = (∫ z, S i z + T i z) - (∫ z, C i z) :=
            integral_sub ((hS i).1.add (hT i).1) (hC i).1
          _ = 0 := by rw [hST, (hS i).2, (hT i).2, (hC i).2]; ring
  change Integrable (fun z ↦ (∑ i, (S i z + T i z - C i z)) + 2 * P z) volume ∧ _
  refine ⟨hsum.add (hP.1.const_mul 2), ?_⟩
  change (∫ z : Vec3 × ℝ, (∑ i, (S i z + T i z - C i z)) + 2 * P z) = 0
  calc
    _ = (∫ z : Vec3 × ℝ, ∑ i, (S i z + T i z - C i z)) +
        (∫ z : Vec3 × ℝ, 2 * P z) := integral_add hsum (hP.1.const_mul 2)
    _ = 0 := by rw [hzsum, integral_const_mul, hP.2]; ring

/-- The original unforced suitable compact-test energy deficit is integrable and nonpositive. -/
theorem suitable_original_energy_deficit
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z) :
    Integrable (fun z : Vec3 × ℝ ↦ originalEnergyDeficitPolynomial (u z)
      (fun j ↦ spatialPartial ψ j z) (Du z) (p z) (ψ z) (timePartial ψ z)
      (∑ j, spatialSecondPartial ψ j j z)) volume ∧
      (∫ z : Vec3 × ℝ, originalEnergyDeficitPolynomial (u z)
        (fun j ↦ spatialPartial ψ j z) (Du z) (p z) (ψ z) (timePartial ψ z)
        (∑ j, spatialSecondPartial ψ j j z)) ≤ 0 := by
  have hs := suitable_global_energy hsol hψ hnψ
  have heq : (fun z : Vec3 × ℝ ↦ originalEnergyDeficitPolynomial (u z)
      (fun j ↦ spatialPartial ψ j z) (Du z) (p z) (ψ z) (timePartial ψ z)
      (∑ j, spatialSecondPartial ψ j j z)) =
        fun z ↦ 2 * (spatialGradientSq u Du z * ψ z) -
          localEnergyRhs u p (fun _ ↦ 0) ψ z := by
    funext z
    simp only [originalEnergyDeficitPolynomial, projectedGradientSquare,
      frameEnergyPolynomial, localEnergyRhs, spatialGradientSq, timePartialProd,
      spatialPartialProd, spatialSecondPartialProd, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero]
    ring
  refine ⟨((hs.1.const_mul 2).sub hs.2.1).congr
    (ae_of_all _ fun z ↦ (congrFun heq z).symm), ?_⟩
  have hint : (∫ z : Vec3 × ℝ,
      2 * (spatialGradientSq u Du z * ψ z) - localEnergyRhs u p (fun _ ↦ 0) ψ z) =
        2 * (∫ z : Vec3 × ℝ, spatialGradientSq u Du z * ψ z) -
          (∫ z : Vec3 × ℝ, localEnergyRhs u p (fun _ ↦ 0) ψ z) := by
    calc
      _ = (∫ z : Vec3 × ℝ, 2 * (spatialGradientSq u Du z * ψ z)) -
          (∫ z : Vec3 × ℝ, localEnergyRhs u p (fun _ ↦ 0) ψ z) :=
        integral_sub (hs.1.const_mul 2) hs.2.1
      _ = _ := by rw [integral_const_mul]
  have hInt := congrArg (fun g : Vec3 × ℝ → ℝ ↦ ∫ z, g z) heq
  refine hInt.trans_le (hint.trans_le ?_)
  exact sub_nonpos.mpr hs.2.2

/-- Smooth harmonic correction data give the actual projected local energy inequality. -/
theorem suitable_smooth_projected_local_energy
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {H : Vec3 × ℝ → Vec3} {Q ψ : Vec3 × ℝ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) (hnψ : ∀ z, 0 ≤ ψ z)
    (hh : ∀ i z, z ∈ tsupport ψ →
      (∑ j : Fin 3, spatialSecondPartial (fun w ↦ H w i) j j z) = 0)
    (hdiv : ∀ z ∈ tsupport ψ,
      (∑ i : Fin 3, spatialPartial (fun w ↦ H w i) i z) = 0)
    (hgrad : ∀ i z, z ∈ tsupport ψ →
      timePartial (fun w ↦ H w i) z = spatialPartial Q i z) :
    Integrable (fun z : Vec3 × ℝ ↦ projectedEnergyDeficitPolynomial (u z) (H z)
      (fun j ↦ spatialPartial ψ j z) (Du z)
      (fun i j ↦ spatialPartial (fun w ↦ H w i) j z)
      (p z - Q z) (ψ z) (timePartial ψ z) (∑ j, spatialSecondPartial ψ j j z)) volume ∧
      (∫ z : Vec3 × ℝ, projectedEnergyDeficitPolynomial (u z) (H z)
        (fun j ↦ spatialPartial ψ j z) (Du z)
        (fun i j ↦ spatialPartial (fun w ↦ H w i) j z)
        (p z - Q z) (ψ z) (timePartial ψ z) (∑ j, spatialSecondPartial ψ j j z)) ≤ 0 := by
  let E : Vec3 × ℝ → ℝ := fun z ↦ originalEnergyDeficitPolynomial (u z)
    (fun j ↦ spatialPartial ψ j z) (Du z) (p z) (ψ z) (timePartial ψ z)
    (∑ j, spatialSecondPartial ψ j j z)
  let M : Vec3 × ℝ → ℝ := fun z ↦ harmonicCorrectionMomentumPolynomial (u z) (H z)
    (fun i ↦ timePartial (fun w ↦ H w i) z) (fun j ↦ spatialPartial ψ j z)
    (Du z) (fun i j ↦ spatialPartial (fun w ↦ H w i) j z)
    (p z) (ψ z) (timePartial ψ z)
  let Z : Vec3 × ℝ → ℝ := smoothProjectedEnergyCorrection u Du H Q ψ
  have hE : Integrable E volume ∧ (∫ z, E z) ≤ 0 :=
    suitable_original_energy_deficit hsol hψ hnψ
  have hM : Integrable M volume ∧ (∫ z, M z) = 0 :=
    suitable_smooth_correction_momentum_pairing hsol hH hψ
  have hZ : Integrable Z volume ∧ (∫ z, Z z) = 0 :=
    suitable_smooth_projected_energy_correction_zero hsol hH hQ hψ hh hdiv
  have heq : (fun z : Vec3 × ℝ ↦ projectedEnergyDeficitPolynomial (u z) (H z)
      (fun j ↦ spatialPartial ψ j z) (Du z)
      (fun i j ↦ spatialPartial (fun w ↦ H w i) j z)
      (p z - Q z) (ψ z) (timePartial ψ z) (∑ j, spatialSecondPartial ψ j j z)) =
        fun z ↦ E z + 2 * M z + Z z := by
    funext z
    have hexp := projected_energy_scalar_decomposition (u z) (H z)
      (fun i ↦ timePartial (fun w ↦ H w i) z) (fun j ↦ spatialPartial ψ j z)
      (Du z) (fun i j ↦ spatialPartial (fun w ↦ H w i) j z)
      (p z) (Q z) (ψ z) (timePartial ψ z) (∑ j, spatialSecondPartial ψ j j z)
    have hA : (∑ i : Fin 3,
        (u z i + H z i) * timePartial (fun w ↦ H w i) z) * ψ z =
          (∑ i : Fin 3, (u z i + H z i) * spatialPartial Q i z) * ψ z := by
      by_cases hz : z ∈ tsupport ψ
      · exact congrArg (fun a : ℝ ↦ a * ψ z)
          (Finset.sum_congr rfl fun i _ ↦
            congrArg (fun a : ℝ ↦ (u z i + H z i) * a) (hgrad i z hz))
      · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
    have hD : 2 * p z * (∑ i : Fin 3, spatialPartial (fun w ↦ H w i) i z) * ψ z = 0 := by
      by_cases hz : z ∈ tsupport ψ
      · rw [hdiv z hz, mul_zero, zero_mul]
      · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
    rw [hA, hD, add_zero] at hexp
    change _ - E z - 2 * M z = Z z at hexp
    linarith only [hexp]
  rw [heq]
  refine ⟨(hE.1.add (hM.1.const_mul 2)).add hZ.1, ?_⟩
  have hEM : (∫ z, E z + 2 * M z) = (∫ z, E z) + 2 * (∫ z, M z) := by
    calc
      _ = (∫ z, E z) + (∫ z, 2 * M z) := integral_add hE.1 (hM.1.const_mul 2)
      _ = _ := by rw [integral_const_mul]
  calc
    _ = (∫ z, E z + 2 * M z) + (∫ z, Z z) :=
      integral_add (hE.1.add (hM.1.const_mul 2)) hZ.1
    _ = ∫ z, E z := by rw [hEM, hM.2, hZ.2]; ring
    _ ≤ 0 := hE.2

end FluidSingularSets
