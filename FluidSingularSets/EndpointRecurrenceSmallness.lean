-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.EndpointShrinkingIteration

/-!
# Genuine source and trap selection for the endpoint recurrence

The shrink ratio contracts the geometric pressure term. A separately chosen
source threshold controls its square-root coefficient, the initial energy,
and the genuine full-gradient forcing. The nonlinear trap is kept below the
shrink ratio times the final CKN interpolation budget.
-/

@[expose] public section

open Filter Set
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The actual doubled source powers and full-gradient polynomial have one linear small bound. -/
theorem endpoint_doubled_source_forcing_le {X Cd : ℝ}
    (hX : 0 ≤ X) (hXone : X ≤ 1) (hCd : 0 ≤ Cd) :
    (2 * X) ^ (3 / 2 : ℝ) + (2 * X) ^ 2 + Cd * (X + X ^ 2 + X ^ 4) ≤
      ((2 : ℝ) ^ (3 / 2 : ℝ) + 4 + 4 * Cd) * X := by
  have hp := endpoint_small_source_polynomial_le hX hXone
  have hxpow : 0 ≤ X ^ (3 / 2 : ℝ) := Real.rpow_nonneg hX _
  have hpoly : X + X ^ 2 + X ^ 4 ≤ 4 * X := by linarith
  have hhalf := Real.rpow_le_self_of_le_one hX hXone (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have h₁ : (2 * X) ^ (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * X := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hX]
    exact mul_le_mul_of_nonneg_left hhalf (Real.rpow_nonneg (by norm_num) _)
  have h₂ : (2 * X) ^ 2 ≤ 4 * X := by
    nlinarith [mul_nonneg hX (sub_nonneg.mpr hXone)]
  calc
    _ ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * X + 4 * X + Cd * (4 * X) :=
      add_le_add (add_le_add h₁ h₂) (mul_le_mul_of_nonneg_left hpoly hCd)
    _ = _ := by ring

/-- True positive source smallness makes the complete scalar endpoint recurrence stay trapped. -/
theorem exists_endpoint_recurrence_smallness {C K₀ Cd H : ℝ}
    (hC : 0 ≤ C) (hK₀ : 0 ≤ K₀) (hCd : 0 ≤ Cd) (hH : 0 < H) :
    ∃ θ T ε : ℝ, 0 < θ ∧ θ < 1 / 4 ∧ 0 < T ∧ T ≤ θ * H ∧ 0 < ε ∧ ε ≤ 1 ∧
      ∀ X : ℝ, 0 ≤ X → X ≤ ε → ∀ F : ℕ → ℝ, (∀ n, 0 ≤ F n) →
        F 0 ≤ K₀ * (X + X ^ 2 + X ^ 4 + X ^ (3 / 2 : ℝ)) →
        (∀ n, F (n + 1) ≤
          (1 / 8 + C * θ ^ (3 / 2 : ℝ) + C * Real.sqrt (2 * X) * (θ⁻¹) ^ 2) * F n +
          C * (θ⁻¹) ^ 6 * (F n ^ (3 / 2 : ℝ) + (2 * X) ^ (3 / 2 : ℝ) +
            (2 * X) ^ 2 + Cd * (X + X ^ 2 + X ^ 4))) → ∀ n, F n ≤ T := by
  obtain ⟨θ, hθ, hθsmall, hdec⟩ := exists_endpoint_shrink_ratio
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC)
  have hgeo : C * θ ^ (3 / 2 : ℝ) ≤ 1 / 16 := by
    have hh := hdec (3 / 2) (by norm_num)
    nlinarith
  let B : ℝ := C * (θ⁻¹) ^ 6
  have hB : 0 ≤ B := mul_nonneg hC (by positivity)
  obtain ⟨T, hT, hTH, hBT⟩ := exists_endpoint_nonlinear_trap hB (mul_pos hθ hH)
  let Cs : ℝ := B * ((2 : ℝ) ^ (3 / 2 : ℝ) + 4 + 4 * Cd)
  have hCs : 0 ≤ Cs := mul_nonneg hB (by positivity)
  let K := max K₀ Cs
  have hK : 0 ≤ K := hK₀.trans (le_max_left _ _)
  obtain ⟨ε₀, hε₀, hε₀one, hsource⟩ := exists_endpoint_source_threshold hK hT
  let Y : ℝ := θ ^ 2 / (16 * (C + 1))
  have hY : 0 < Y := by dsimp only [Y]; positivity
  let ε := min ε₀ (Y ^ 2 / 2)
  have hε : 0 < ε := lt_min hε₀ (div_pos (sq_pos_of_pos hY) (by norm_num))
  refine ⟨θ, T, ε, hθ, hθsmall, hT, hTH, hε,
    (min_le_left _ _).trans hε₀one, ?_⟩
  intro X hX hXε F hF h₀ hstep
  have hXε₀ : X ≤ ε₀ := hXε.trans (min_le_left _ _)
  have hXone : X ≤ 1 := hXε₀.trans hε₀one
  have hs := hsource X hX hXε₀
  have hpoly : 0 ≤ X + X ^ 2 + X ^ 4 + X ^ (3 / 2 : ℝ) := by positivity
  have hinit : F 0 ≤ T := by
    have hh := mul_le_mul_of_nonneg_right (le_max_left K₀ Cs) hpoly
    linarith
  have hXsq : 2 * X ≤ Y ^ 2 := by
    have hh := hXε.trans (min_le_right ε₀ (Y ^ 2 / 2))
    linarith
  have hsqrt : Real.sqrt (2 * X) ≤ Y := Real.sqrt_le_iff.mpr ⟨hY.le, hXsq⟩
  have hcoeff : C * Real.sqrt (2 * X) * (θ⁻¹) ^ 2 ≤ 1 / 16 := by
    calc
      _ ≤ C * Y * (θ⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hC) (by positivity)
      _ = C / (16 * (C + 1)) := by
        dsimp only [Y]
        calc
          _ = C / (16 * (C + 1)) * (θ ^ 2 * (θ⁻¹) ^ 2) := by ring
          _ = _ := by rw [← mul_pow, mul_inv_cancel₀ hθ.ne', one_pow, mul_one]
      _ ≤ _ := by
        apply (div_le_iff₀ (by positivity : 0 < 16 * (C + 1))).mpr
        nlinarith
  let a : ℝ := 1 / 8 + C * θ ^ (3 / 2 : ℝ) + C * Real.sqrt (2 * X) * (θ⁻¹) ^ 2
  have ha : a ≤ 1 / 4 := by dsimp only [a]; linarith
  let d : ℝ := B * ((2 * X) ^ (3 / 2 : ℝ) + (2 * X) ^ 2 +
    Cd * (X + X ^ 2 + X ^ 4))
  have hd : d ≤ T / 2 := by
    have hXp : X ≤ X + X ^ 2 + X ^ 4 + X ^ (3 / 2 : ℝ) := by
      have hXpow := Real.rpow_nonneg hX (3 / 2 : ℝ)
      have hXfour : 0 ≤ X ^ 4 := by positivity
      nlinarith [sq_nonneg X]
    have hh : d ≤ K * (X + X ^ 2 + X ^ 4 + X ^ (3 / 2 : ℝ)) := by
      calc
        _ ≤ Cs * X := (mul_le_mul_of_nonneg_left
          (endpoint_doubled_source_forcing_le hX hXone hCd) hB).trans_eq (by dsimp [Cs]; ring)
        _ ≤ Cs * (X + X ^ 2 + X ^ 4 + X ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hXp hCs
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right K₀ Cs) hpoly
    linarith
  apply endpoint_shrinking_sequence_le_trap hF hinit ha hB hBT hd
  intro n
  exact (hstep n).trans_eq (by dsimp only [a, B, d]; ring)

end FluidSingularSets
