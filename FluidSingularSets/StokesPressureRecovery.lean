-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.LocalStokesEnergy
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Genuine Hilbert pressure recovery from bounded divergence lifts

The actual variational Stokes residual already factors through divergence.
A norm bound for genuine preimages makes this factor continuous. Hahn--Banach
and Riesz representation then construct an actual spatial L² pressure and its
quantitative norm estimate. Applying this theorem on a ball additionally
requires the genuine ball divergence preimage bound.
-/

@[expose] public section

open MeasureTheory Set CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Bounded genuine divergence lifts recover the actual Stokes pressure in L².
The statement applies to any spatial domain with such lifts and introduces no
pressure existence assumption. -/
theorem exists_stokesPressure_of_bounded_lifts
    {U : Set Vec3} {C : ℝ} (hC : 0 ≤ C)
    (hlift : ∀ g : (stokesEnergyDivergence U).range,
      ∃ v : stokesGradientEnergySpace U,
        stokesEnergyDivergence U v = g.1 ∧ ‖v‖ ≤ C * ‖g‖)
    (F : StokesEnergyForce U) :
    ∃ p : Lp ℝ 2 (volume.restrict U), ‖p‖ ≤ 2 * C * ‖F‖ ∧
      ∀ v : stokesGradientEnergySpace U,
        -(inner ℝ p (stokesEnergyDivergence U v)) = stokesEnergyResidual F v := by
  obtain ⟨q, hq⟩ := exists_stokesPressureRangeFunctional F
  have hbound (g : (stokesEnergyDivergence U).range) :
      ‖q g‖ ≤ (2 * C * ‖F‖) * ‖g‖ := by
    obtain ⟨v, hv, hvnorm⟩ := hlift g
    have heq : (⟨stokesEnergyDivergence U v,
        (stokesEnergyDivergence U).toLinearMap.mem_range_self v⟩ :
          (stokesEnergyDivergence U).range) = g := Subtype.ext hv
    have hqg : q g = stokesEnergyResidual F v := by rw [← heq, hq]
    rw [hqg]
    calc
      ‖stokesEnergyResidual F v‖ ≤ ‖stokesEnergyResidual F‖ * ‖v‖ :=
        (stokesEnergyResidual F).le_opNorm v
      _ ≤ (2 * ‖F‖) * (C * ‖g‖) :=
        mul_le_mul (stokesEnergyResidual_norm_le F) hvnorm
          (norm_nonneg v) (by positivity)
      _ = (2 * C * ‖F‖) * ‖g‖ := by ring
  let qc : (stokesEnergyDivergence U).range →L[ℝ] ℝ :=
    q.mkContinuous (2 * C * ‖F‖) hbound
  have hqnorm : ‖qc‖ ≤ 2 * C * ‖F‖ :=
    q.mkContinuous_norm_le (by positivity) hbound
  obtain ⟨Q, hQ, hQnorm⟩ := exists_extension_norm_eq
    (stokesEnergyDivergence U).range qc
  let p : Lp ℝ 2 (volume.restrict U) :=
    -((InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume.restrict U))).symm Q)
  refine ⟨p, ?_, ?_⟩
  · calc
      ‖p‖ = ‖Q‖ := by
        dsimp [p]
        rw [norm_neg, (InnerProductSpace.toDual ℝ
          (Lp ℝ 2 (volume.restrict U))).symm.norm_map]
      _ = ‖qc‖ := hQnorm
      _ ≤ 2 * C * ‖F‖ := hqnorm
  · intro v
    change -(inner ℝ (-((InnerProductSpace.toDual ℝ
      (Lp ℝ 2 (volume.restrict U))).symm Q)) (stokesEnergyDivergence U v)) = _
    rw [inner_neg_left, neg_neg, InnerProductSpace.toDual_symm_apply]
    exact (hQ ⟨stokesEnergyDivergence U v,
      (stokesEnergyDivergence U).toLinearMap.mem_range_self v⟩).trans (hq v)

/-- The recovered pressure satisfies the literal actual weak Stokes equation
against every compact smooth vector test, with a genuine integrable pressure
pairing. -/
theorem exists_stokesPressure_test_of_bounded_lifts
    {U : Set Vec3} {C : ℝ} (hC : 0 ≤ C)
    (hlift : ∀ g : (stokesEnergyDivergence U).range,
      ∃ v : stokesGradientEnergySpace U,
        stokesEnergyDivergence U v = g.1 ∧ ‖v‖ ≤ C * ‖g‖)
    (F : StokesEnergyForce U) :
    ∃ p : Lp ℝ 2 (volume.restrict U), ‖p‖ ≤ 2 * C * ‖F‖ ∧
      ∀ φ : StokesVectorTest U,
        Integrable (fun x ↦ p x * ∑ i : Fin 3, (φ i).partialDeriv i x)
          (volume.restrict U) ∧
        (∫ x in U, p x * ∑ i : Fin 3, (φ i).partialDeriv i x) =
          inner ℝ (stokesEnergySolution F : stokesGradientEnergySpace U)
            (stokesEnergyTest φ) - F (stokesEnergyTest φ) := by
  obtain ⟨p, hp, heq⟩ := exists_stokesPressure_of_bounded_lifts hC hlift F
  refine ⟨p, hp, ?_⟩
  intro φ
  have hdiv := stokesEnergyDivergence_test_ae φ
  have hprod : (fun x ↦ inner ℝ (p x)
      (stokesEnergyDivergence U (stokesEnergyTest φ) x)) =ᵐ[volume.restrict U]
        (fun x ↦ p x * ∑ i : Fin 3, (φ i).partialDeriv i x) := by
    filter_upwards [hdiv] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hInt := (L2.integrable_inner (𝕜 := ℝ) p
    (stokesEnergyDivergence U (stokesEnergyTest φ))).congr hprod
  refine ⟨hInt, ?_⟩
  calc
    _ = inner ℝ p (stokesEnergyDivergence U (stokesEnergyTest φ)) := by
      rw [L2.inner_def]
      exact (integral_congr_ae hprod).symm
    _ = -stokesEnergyResidual F (stokesEnergyTest φ) := neg_eq_iff_eq_neg.mp (heq _)
    _ = _ := by
      change -(F (stokesEnergyTest φ) -
        inner ℝ (stokesEnergySolution F : stokesGradientEnergySpace U)
          (stokesEnergyTest φ)) = _
      ring

end FluidSingularSets
