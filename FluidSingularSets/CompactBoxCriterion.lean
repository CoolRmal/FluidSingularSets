-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.BoxChargeReduction
public import FluidSingularSets.BoxFromCharge
public import FluidSingularSets.RawSingularPersistence

/-!
# Actual compact box dimension from the velocity-only criterion

The genuine compact pressure-gradient patches give one finite charge measure
and one common radius. The true singular reverse charge, transported by the
exact parabolic isometry, bounds the independently stated covering dimension.
The analytic velocity-only criterion is the sole explicit input to this reduction.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- An actual universal velocity-only criterion gives the requested compact singular box bound. -/
theorem suitable_compact_singularSet_upperBoxDimension_le_of_velocity_criterion
    {κ : ℝ} (hκ : 0 < κ) (hcriterion : UniformVelocityOnlyInteriorCriterion 3 κ)
    {Ω : Set Space} {I : Set ℝ}
    (sol : CKNChallenge.LocalWeakNSESolution Ω I 3) (hf : sol.f = 0)
    {K : Set SpaceTime} (hK : IsCompact K) (hKsub : K ⊆ Ω ×ˢ I) :
    upperParabolicBoxDimension (CKNChallenge.singularSet Ω I sol.u ∩ K) ≤
      ENNReal.ofReal (25 / 23 : ℝ) := by
  let E := rawCompactSingularSet Ω I sol.u K
  let u := CKNChallenge.pullVelocity sol.u
  let D := CKNChallenge.pullGradient sol.Dxu
  let p := CKNChallenge.pullScalar sol.p
  have hsol := raw_unforced_suitableWeakSolutionIntegrable (by norm_num) sol hf
  have hE : IsCompact E := isCompact_rawCompactSingularSet sol.u hK hKsub
  have hEdom : E ⊆ spaceTimeSet (CKNChallenge.rawSpace Ω) I :=
    rawCompactSingularSet_subset_domain sol.u K
  obtain ⟨ε, hε, hreverse⟩ := exists_uniform_reverse_compact_box_charge hκ hcriterion
  obtain ⟨S, P, t, R, hS, _, hSdom, hR, hfinite, hpatch⟩ :=
    exists_suitable_compact_box_measure hsol hE hEdom
  let μ := compactBoxMeasure S u D P t
  let e := CKNChallenge.rawParabolicIsometry
  let ν := Measure.map e μ
  let η : ℝ := ε / (4 : ℝ) ^ (25 / 23 : ℝ)
  let r₀ : ℝ := min 1 (R / 2)
  have hη : 0 < η := div_pos hε (Real.rpow_pos_of_pos (by norm_num) _)
  have hr₀ : 0 < r₀ := lt_min (by norm_num) (by positivity)
  let : IsFiniteMeasure μ := hfinite
  have hν : ν univ ≠ ⊤ := by
    rw [Measure.map_apply e.continuous.measurable MeasurableSet.univ]
    simpa only [preimage_univ] using (measure_lt_top μ univ).ne
  apply upperParabolicBoxDimension_le_of_uniform_ball_charge ν
    (CKNChallenge.singularSet Ω I sol.u ∩ K) η (25 / 23) r₀
    hν hη (by norm_num) hr₀
  intro r hr hrr₀ z hz
  obtain ⟨w, hw, rfl⟩ := hz
  let a := CKNChallenge.parabolicToEuclideanHomeomorph.symm w
  have ha : a ∈ E := ⟨w, hw, rfl⟩
  have hasing : ¬ IsRegularPoint (CKNChallenge.rawSpace Ω) I u a := by
    intro hreg
    have hh := CKNChallenge.isHolderRegularPoint_of_rawRegular hreg
    exact hw.1.2 (by simpa only [a, Homeomorph.apply_symm_apply] using hh)
  have hrR : 2 * r ≤ R := by
    have hh := hrr₀.trans_le (min_le_right _ _)
    linarith
  have hsmall : r < 1 := hrr₀.trans_le (min_le_left _ _)
  obtain ⟨i, hi, hballs⟩ := hpatch a ha
  obtain ⟨hBS, hBP, _, _⟩ := hballs (r / 2) (by positivity) (by linarith)
  have hdom : Metric.ball a (8 * (r / 4)) ⊆ spaceTimeSet (CKNChallenge.rawSpace Ω) I := by
    have hh := (hballs (2 * r) (by positivity) hrR).1
    simpa only [show (8 * (r / 4) : ℝ) = 2 * r by ring] using hh.trans hSdom
  have hcharge := hreverse hsol hS hSdom P t hi a (by positivity : 0 < r / 4)
    (by linarith : r / 4 ≤ 1) hdom
    (by simpa only [show 2 * (r / 4) = r / 2 by ring] using hBS)
    (by simpa only [show 2 * (r / 4) = r / 2 by ring] using hBP) hasing
  have hmap : e a = toParabolic w := by
    change toParabolic (CKNChallenge.parabolicToEuclideanHomeomorph a) = toParabolic w
    rw [Homeomorph.apply_symm_apply]
  have hνball : ν (Metric.ball (toParabolic w) (r / 2)) = μ (Metric.ball a (r / 2)) := by
    rw [Measure.map_apply e.continuous.measurable measurableSet_ball,
      e.preimage_ball, ← hmap, e.symm_apply_apply]
  rw [hνball]
  have hpower : ε * (r / 4) ^ (25 / 23 : ℝ) = η * r ^ (25 / 23 : ℝ) := by
    rw [Real.div_rpow hr.le (by norm_num : (0 : ℝ) ≤ 4)]
    dsimp only [η]
    ring
  simpa only [show 2 * (r / 4) = r / 2 by ring, hpower] using hcharge.le

end FluidSingularSets
