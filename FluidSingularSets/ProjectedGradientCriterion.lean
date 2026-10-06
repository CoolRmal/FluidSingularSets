-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedGradientLimit

/-!
# A genuine CKN regularity budget for projected energy

The vanishing actual harmonic correction transfers an eventual projected
energy budget to the original gradient criterion. The same positive budget
is expressed on geometric radii with the true reciprocal interpolation
factor, so a proved nonlinear iteration can be connected directly to CKN.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Actual CKN gradient regularity supplies a positive universal projected-energy budget. -/
theorem exists_projected_energy_regularity_budget (q : ℝ) (hq : 5 / 2 < q) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (D : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ),
        IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0) →
        localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) →
        (∀ᶠ r : ℝ in 𝓝[>] 0,
          fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 (-(1 / 2)) r 0 ≤
            ENNReal.ofReal K) → IsRegularPoint Ω I u (0, 0) := by
  obtain ⟨ε, hε, hreg⟩ := CKN.Main.epsilonRegularityGradient q hq
  let K : ℝ := ε ^ 2 / 4
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro Ω I u D p hsol hbox hE
  have hz : (0, 0) ∈ spaceTimeSet Ω I := by
    refine ⟨hbox.2.2.1 (subset_closure ?_), hbox.2.2.2.2.2 ?_⟩
    · simp [vec3Ball, vec3EuclideanNorm_zero]
    · rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]
      norm_num
  apply hreg Ω I u D p (fun _ ↦ 0) hsol (0, 0) hz
  have hh := suitable_fullBall_original_gradient_limsup_le_projected_bound hsol hbox hK.le hE
  apply hh.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hε)).2
  dsimp only [K]
  nlinarith [sq_pos_of_pos hε]

/-- A sufficiently small genuine geometric projected-energy bound gives actual regularity. -/
theorem exists_projected_geometric_regularity_budget
    (q : ℝ) (hq : 5 / 2 < q) {θ : ℝ} (hθ : 0 < θ) (hθone : θ < 1) :
    ∃ T : ℝ, 0 < T ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (D : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ),
        IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0) →
        localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) →
        ∀ r₀ : ℝ, 0 < r₀ →
          (∀ n : ℕ, fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 (-(1 / 2))
            (r₀ * θ ^ n) 0 ≤ ENNReal.ofReal T) → IsRegularPoint Ω I u (0, 0) := by
  obtain ⟨K, hK, hreg⟩ := exists_projected_energy_regularity_budget q hq
  refine ⟨θ * K, mul_pos hθ hK, ?_⟩
  intro Ω I u D p hsol hbox r₀ hr₀ hbound
  apply hreg Ω I u D p hsol hbox
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hr₀).filter_mono inf_le_left] with r hr hrr₀
  have hh := fullBallNormalizedProjectedIterationEnergy_le_of_geometric_bounds
    u D p (-1) 0 (-(1 / 2)) hθ hθone hr₀ hbound hr hrr₀.le
  have he : θ⁻¹ * (θ * K) = K := by field_simp [hθ.ne']
  simpa only [he] using hh

end FluidSingularSets
