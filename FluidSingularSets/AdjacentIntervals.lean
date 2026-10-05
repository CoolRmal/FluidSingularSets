module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

/-!
# Containment in adjacent interval grids

A closed interval of length less than one third of a grid cell fits in either the
unshifted grid or a grid with a shift between one and two thirds. This is the
one-dimensional containment step for adjacent parabolic product grids.
-/

@[expose] public section

open Set

namespace FluidSingularSets

/-- Two separated grids suffice to contain a closed interval shorter than one third of a cell.
The strict length inequality keeps the upper endpoint inside the half-open cell. -/
theorem exists_adjacent_interval_cell {a b ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hσ₁ : 1 / 3 ≤ σ) (hσ₂ : σ ≤ 2 / 3) (hwidth : b - a < ℓ / 3) :
    ∃ θ ∈ ({0, σ} : Set ℝ), ∃ m : ℤ,
      Icc a b ⊆ Ico (((m : ℝ) + θ) * ℓ) (((m : ℝ) + θ + 1) * ℓ) := by
  let m : ℤ := ⌊a / ℓ⌋
  have hleft : (m : ℝ) * ℓ ≤ a := (le_div_iff₀ hℓ).1 (Int.floor_le _)
  have hright : a < ((m : ℝ) + 1) * ℓ :=
    (div_lt_iff₀ hℓ).1 (Int.lt_floor_add_one _)
  by_cases hnear : a ≤ ((m : ℝ) + 2 / 3) * ℓ
  · refine ⟨0, by simp, m, ?_⟩
    intro x hx
    simp only [mem_Icc, mem_Ico, add_zero] at *
    constructor <;> nlinarith
  · refine ⟨σ, by simp, m, ?_⟩
    intro x hx
    simp only [mem_Icc, mem_Ico] at *
    have hσlo := mul_le_mul_of_nonneg_right hσ₁ hℓ.le
    have hσhi := mul_le_mul_of_nonneg_right hσ₂ hℓ.le
    constructor <;> nlinarith

/-- The spatial interval of a radius-r cylinder fits into adjacent cells of side length 16r. -/
theorem exists_adjacent_spatial_interval {c r σ : ℝ} (hr : 0 < r)
    (hσ₁ : 1 / 3 ≤ σ) (hσ₂ : σ ≤ 2 / 3) :
    ∃ θ ∈ ({0, σ} : Set ℝ), ∃ m : ℤ,
      Icc (c - r) (c + r) ⊆
        Ico (((m : ℝ) + θ) * (16 * r)) (((m : ℝ) + θ + 1) * (16 * r)) := by
  apply exists_adjacent_interval_cell (by positivity) hσ₁ hσ₂
  linarith

/-- The symmetric time interval fits into adjacent cells of temporal length (16r)². -/
theorem exists_adjacent_time_interval {t r σ : ℝ} (hr : 0 < r)
    (hσ₁ : 1 / 3 ≤ σ) (hσ₂ : σ ≤ 2 / 3) :
    ∃ θ ∈ ({0, σ} : Set ℝ), ∃ m : ℤ,
      Icc (t - r ^ 2) (t + r ^ 2) ⊆
        Ico (((m : ℝ) + θ) * (16 * r) ^ 2)
          (((m : ℝ) + θ + 1) * (16 * r) ^ 2) := by
  apply exists_adjacent_interval_cell (by positivity) hσ₁ hσ₂
  nlinarith [sq_pos_of_pos hr]

end FluidSingularSets
