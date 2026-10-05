module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Arithmetic for the cylinder following the outer mean

These are scalar consequences of an explicitly assumed mean bound. They do not prove the
mean estimate, preservation of suitability under moving frames, or a regularity criterion.

For an outer radius `R`, choose an inner radius `c * R ^ s`. The displacement exponent is
`2 * s + 3 * s / 10 - 3 / 2`. Requiring it to be at least one is exactly `25 / 23 ≤ s`.
-/

@[expose] public section

namespace FluidSingularSets

/-- The moving-cylinder displacement exponent reaches one precisely at `25/23`. -/
theorem moving_displacement_exponent_iff (s : ℝ) :
    1 ≤ 2 * s + (3 * s / 10 - 3 / 2) ↔ 25 / 23 ≤ s := by
  constructor <;> intro h <;> linarith

/-- At the endpoint the mean exponent is `-27/23`. -/
theorem endpoint_mean_exponent :
    3 * (25 / 23 : ℝ) / 10 - 3 / 2 = -(27 / 23 : ℝ) := by
  norm_num

/-- At the endpoint the displacement exponent is exactly one. -/
theorem endpoint_displacement_exponent :
    2 * (25 / 23 : ℝ) + (3 * (25 / 23 : ℝ) / 10 - 3 / 2) = 1 := by
  norm_num

/-- The two-radius exponent constraints from this argument are compatible exactly above
`25/23`. This does not assert sharpness of the singular-set dimension itself. -/
theorem moving_scale_constraints_iff (s : ℝ) :
    (∃ β : ℝ, 1 / 4 - 3 * s / 20 ≤ β ∧ β ≤ s - 1) ↔ 25 / 23 ≤ s := by
  constructor
  · rintro ⟨β, hlower, hupper⟩
    linarith
  · intro hs
    exact ⟨s - 1, by linarith, le_rfl⟩

/-- Raising a radius at most one to an exponent at least one shrinks the selected inner
radius. The multiplier `c` is any nonnegative constant. -/
theorem moving_radius_le_outer {R c s : ℝ}
    (hR₀ : 0 ≤ R) (hR₁ : R ≤ 1) (hc : 0 ≤ c) (hs : 1 ≤ s) :
    c * R ^ s ≤ c * R :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_le_one hR₀ hR₁ hs) hc

/-- A positive outer radius and positive coefficient give a positive inner radius. -/
theorem moving_radius_pos {R c s : ℝ} (hR : 0 < R) (hc : 0 < c) :
    0 < c * R ^ s :=
  mul_pos hc (Real.rpow_pos_of_pos hR s)

/-- The conventional choice `c ≤ 1/16` keeps the inner radius below `R/16`. -/
theorem moving_radius_le_sixteenth {R c s : ℝ}
    (hR₀ : 0 ≤ R) (hR₁ : R ≤ 1) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1 / 16)
    (hs : 1 ≤ s) : c * R ^ s ≤ R / 16 := by
  calc
    c * R ^ s ≤ c * R := moving_radius_le_outer hR₀ hR₁ hc₀ hs
    _ ≤ (1 / 16) * R := mul_le_mul_of_nonneg_right hc₁ hR₀
    _ = R / 16 := by ring

/-- An assumed outer-mean estimate gives a radius-independent bound on normalized
displacement when `s ≥ 25/23`. All constants and sign assumptions are explicit. -/
theorem normalized_moving_displacement_le {R c s C η M : ℝ}
    (hR₀ : 0 < R) (hR₁ : R ≤ 1) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hs : 25 / 23 ≤ s)
    (hM : M ≤ C * η ^ (3 / 10 : ℝ) * R ^ (3 * s / 10 - 3 / 2)) :
    (c * R ^ s) ^ 2 * M / R ≤ C * c ^ 2 * η ^ (3 / 10 : ℝ) := by
  have hpower : (R ^ s) ^ 2 = R ^ (2 * s) := by
    simpa [mul_comm] using (Real.rpow_mul_natCast hR₀.le s 2).symm
  have hcoeff : 0 ≤ C * c ^ 2 * η ^ (3 / 10 : ℝ) :=
    mul_nonneg (mul_nonneg hC (sq_nonneg c)) (Real.rpow_nonneg hη _)
  have hradius : R ^ (2 * s + (3 * s / 10 - 3 / 2)) ≤ R :=
    Real.rpow_le_self_of_le_one hR₀.le hR₁ ((moving_displacement_exponent_iff s).2 hs)
  calc
    (c * R ^ s) ^ 2 * M / R
        ≤ (c * R ^ s) ^ 2 *
            (C * η ^ (3 / 10 : ℝ) * R ^ (3 * s / 10 - 3 / 2)) / R :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hM (sq_nonneg _)) hR₀.le
    _ = (C * c ^ 2 * η ^ (3 / 10 : ℝ)) *
        R ^ (2 * s + (3 * s / 10 - 3 / 2)) / R := by
      rw [mul_pow, hpower, Real.rpow_add hR₀]
      ring
    _ ≤ (C * c ^ 2 * η ^ (3 / 10 : ℝ)) * R / R :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hradius hcoeff) hR₀.le
    _ = C * c ^ 2 * η ^ (3 / 10 : ℝ) := by field_simp

/-- Explicit smallness of the scalar coefficient limits the displacement to `R/4`. -/
theorem moving_displacement_le_quarter {R c s C η M : ℝ}
    (hR₀ : 0 < R) (hR₁ : R ≤ 1) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hs : 25 / 23 ≤ s)
    (hM : M ≤ C * η ^ (3 / 10 : ℝ) * R ^ (3 * s / 10 - 3 / 2))
    (hsmall : C * c ^ 2 * η ^ (3 / 10 : ℝ) ≤ 1 / 4) :
    (c * R ^ s) ^ 2 * M ≤ R / 4 := by
  have hnormalized := normalized_moving_displacement_le (c := c) hR₀ hR₁ hC hη hs hM
  have hdisplacement := (div_le_iff₀ hR₀).1 (hnormalized.trans hsmall)
  nlinarith

end FluidSingularSets
