-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Nonlinear shrinking-scale energy iteration

These scalar lemmas select genuine positive contraction, trapping, and source
thresholds for the three-halves endpoint recurrence. The quantitative PDE
recurrence itself is separate and must be proved for the actual energy.
-/

@[expose] public section

set_option autoImplicit false

namespace FluidSingularSets

/-- The actual three-halves power is linear with a square-root coefficient on a trap. -/
theorem endpoint_threeHalves_le_trap_linear {x T : ℝ} (hx : 0 ≤ x) (hxT : x ≤ T) :
    x ^ (3 / 2 : ℝ) ≤ x * Real.sqrt T := by
  calc
    _ = x * Real.sqrt x := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num), Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxT) hx

/-- A genuinely small nonlinear endpoint recurrence stays inside its initial trap. -/
theorem endpoint_shrinking_sequence_le_trap {F : ℕ → ℝ} {a b d T : ℝ}
    (hF : ∀ n, 0 ≤ F n) (h₀ : F 0 ≤ T) (ha : a ≤ 1 / 4) (hb : 0 ≤ b)
    (hbT : b * Real.sqrt T ≤ 1 / 4) (hd : d ≤ T / 2)
    (hstep : ∀ n, F (n + 1) ≤ a * F n + b * F n ^ (3 / 2 : ℝ) + d) :
    ∀ n, F n ≤ T := by
  intro n
  induction n with
  | zero => exact h₀
  | succ n ih =>
    have hp := endpoint_threeHalves_le_trap_linear (hF n) ih
    have hlin : b * F n ^ (3 / 2 : ℝ) ≤ (1 / 4) * F n := by
      calc
        _ ≤ b * (F n * Real.sqrt T) := mul_le_mul_of_nonneg_left hp hb
        _ = (b * Real.sqrt T) * F n := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hbT (hF n)
    have haF := mul_le_mul_of_nonneg_right ha (hF n)
    have hs := hstep n
    nlinarith

/-- The trapped genuine recurrence has an explicit affine geometric envelope. -/
theorem endpoint_shrinking_sequence_affine_bound {F : ℕ → ℝ} {a b d T : ℝ}
    (hF : ∀ n, 0 ≤ F n) (h₀ : F 0 ≤ T) (ha : a ≤ 1 / 4) (hb : 0 ≤ b)
    (hbT : b * Real.sqrt T ≤ 1 / 4) (hd : d ≤ T / 2)
    (hstep : ∀ n, F (n + 1) ≤ a * F n + b * F n ^ (3 / 2 : ℝ) + d) :
    ∀ n, F n ≤ (1 / 2 : ℝ) ^ n * F 0 + 2 * d * (1 - (1 / 2 : ℝ) ^ n) := by
  have htrap := endpoint_shrinking_sequence_le_trap hF h₀ ha hb hbT hd hstep
  have hlinear (n : ℕ) : F (n + 1) ≤ (1 / 2) * F n + d := by
    have hp := endpoint_threeHalves_le_trap_linear (hF n) (htrap n)
    have hlin : b * F n ^ (3 / 2 : ℝ) ≤ (1 / 4) * F n := by
      calc
        _ ≤ b * (F n * Real.sqrt T) := mul_le_mul_of_nonneg_left hp hb
        _ = (b * Real.sqrt T) * F n := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hbT (hF n)
    have haF := mul_le_mul_of_nonneg_right ha (hF n)
    have hs := hstep n
    linarith
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ (1 / 2) * F n + d := hlinear n
      _ ≤ (1 / 2) * ((1 / 2 : ℝ) ^ n * F 0 + 2 * d * (1 - (1 / 2 : ℝ) ^ n)) + d :=
        add_le_add (mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 2)) le_rfl
      _ = _ := by rw [pow_succ]; ring

/-- One positive geometric ratio contracts every true decay power at least one. -/
theorem exists_endpoint_shrink_ratio {C : ℝ} (hC : 0 ≤ C) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 / 4 ∧ ∀ α : ℝ, 1 ≤ α → C * θ ^ α ≤ 1 / 4 := by
  let θ : ℝ := 1 / (16 * (C + 1))
  have hp : 0 < 16 * (C + 1) := by positivity
  have hθ : 0 < θ := div_pos (by norm_num) hp
  have hθsmall : θ < 1 / 4 := by
    apply (div_lt_iff₀ hp).mpr
    nlinarith
  refine ⟨θ, hθ, hθsmall, ?_⟩
  intro α hα
  have ht := Real.rpow_le_self_of_le_one hθ.le (by linarith) hα
  calc
    _ ≤ C * θ := mul_le_mul_of_nonneg_left ht hC
    _ ≤ _ := by
      dsimp only [θ]
      rw [mul_one_div]
      apply (div_le_iff₀ hp).mpr
      nlinarith

/-- A positive nonlinear trap can be chosen below any true interpolation budget. -/
theorem exists_endpoint_nonlinear_trap {b H : ℝ} (hb : 0 ≤ b) (hH : 0 < H) :
    ∃ T : ℝ, 0 < T ∧ T ≤ H ∧ b * Real.sqrt T ≤ 1 / 4 := by
  let c : ℝ := 1 / (4 * (b + 1))
  have hc : 0 < c := by dsimp only [c]; positivity
  let T := min H (c ^ 2)
  have hT : 0 < T := lt_min hH (sq_pos_of_pos hc)
  have hsqrt : Real.sqrt T ≤ c := Real.sqrt_le_iff.mpr ⟨hc.le, min_le_right _ _⟩
  refine ⟨T, hT, min_le_left _ _, ?_⟩
  calc
    _ ≤ b * c := mul_le_mul_of_nonneg_left hsqrt hb
    _ ≤ _ := by
      dsimp only [c]
      rw [mul_one_div]
      apply (div_le_iff₀ (by positivity : 0 < 4 * (b + 1))).mpr
      nlinarith

/-- Every actual endpoint source power has a linear small-data bound. -/
theorem endpoint_small_source_polynomial_le {X : ℝ} (hX : 0 ≤ X) (hXone : X ≤ 1) :
    X + X ^ 2 + X ^ 4 + X ^ (3 / 2 : ℝ) ≤ 4 * X := by
  have h₂ : X ^ 2 ≤ X := by nlinarith
  have h₄ : X ^ 4 ≤ X := by
    calc
      _ = (X ^ 2) ^ 2 := by ring
      _ ≤ X ^ 2 := pow_le_pow_left₀ (sq_nonneg X) h₂ 2
      _ ≤ _ := h₂
  have hhalf := Real.rpow_le_self_of_le_one hX hXone (by norm_num : (1 : ℝ) ≤ 3 / 2)
  linarith

/-- A genuine positive source threshold simultaneously controls all endpoint source powers. -/
theorem exists_endpoint_source_threshold {K T : ℝ} (hK : 0 ≤ K) (hT : 0 < T) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ X : ℝ, 0 ≤ X → X ≤ ε →
      K * (X + X ^ 2 + X ^ 4 + X ^ (3 / 2 : ℝ)) ≤ T / 4 := by
  let ε := min 1 (T / (16 * (K + 1)))
  have hd : 0 < 16 * (K + 1) := by positivity
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hT hd)
  refine ⟨ε, hε, min_le_left _ _, ?_⟩
  intro X hX hXε
  have hXone : X ≤ 1 := hXε.trans (min_le_left _ _)
  calc
    _ ≤ K * (4 * X) := mul_le_mul_of_nonneg_left
      (endpoint_small_source_polynomial_le hX hXone) hK
    _ ≤ K * (4 * (T / (16 * (K + 1)))) := by
      gcongr
      exact hXε.trans (min_le_right _ _)
    _ = (T / 4) * (K / (K + 1)) := by
      field_simp [show K + 1 ≠ 0 by positivity]
      norm_num
    _ ≤ _ := mul_le_of_le_one_right (by linarith) ((div_le_one (by positivity)).mpr (by linarith))

end FluidSingularSets
