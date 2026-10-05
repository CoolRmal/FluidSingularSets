-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.PolynomialBallEnergy
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Genuine polynomial density in the ball `L²` space

Actual coordinate polynomials separate the points of the compact closed ball.
Stone-Weierstrass gives uniform approximation there, and bounded continuous
functions are dense in the actual ball-restricted `L²` space.
-/

@[expose] public section

open CKN MvPolynomial MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal Topology BoundedContinuousFunction

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

instance unitBallVolume_isFinite : IsFiniteMeasure (volume.restrict (vec3Ball (0 : Vec3) 1)) :=
  isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne

instance unitBallVolume_weaklyRegular :
    Measure.WeaklyRegular (volume.restrict (vec3Ball (0 : Vec3) 1)) :=
  Measure.WeaklyRegular.restrict_of_measure_ne_top volume_vec3Ball_lt_top.ne

instance weightedClosedUnitBall_compactSpace : CompactSpace weightedClosedUnitBall :=
  isCompact_iff_compactSpace.mp weightedClosedUnitBall_isCompact

/-- The literal polynomial functions on the actual compact closed ball. -/
def unitBallPolynomialContinuousHom :
    BallPolynomial →ₐ[ℝ] C(weightedClosedUnitBall, ℝ) where
  toFun p := ⟨fun x ↦ ballPolynomialEval p x.1,
    (ballPolynomialEval_contDiff p).continuous.comp continuous_subtype_val⟩
  map_zero' := by ext x; simp [ballPolynomialEval]
  map_one' := by ext x; simp [ballPolynomialEval]
  map_add' p q := by ext x; simp [ballPolynomialEval]
  map_mul' p q := by ext x; simp [ballPolynomialEval]
  commutes' c := by ext x; simp [ballPolynomialEval, algebraMap_eq]

theorem unitBallPolynomialContinuousHom_apply (p : BallPolynomial)
    (x : weightedClosedUnitBall) :
    unitBallPolynomialContinuousHom p x = ballPolynomialEval p x := rfl

/-- Actual coordinate polynomials separate distinct points of the closed ball. -/
theorem unitBallPolynomialContinuous_separatesPoints :
    unitBallPolynomialContinuousHom.range.SeparatesPoints := by
  intro x y hxy
  have hval : x.1 ≠ y.1 := fun h ↦ hxy (Subtype.ext h)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hval
  refine ⟨unitBallPolynomialContinuousHom (X i), ⟨_, ⟨X i, rfl⟩, rfl⟩, ?_⟩
  simpa [unitBallPolynomialContinuousHom_apply, ballPolynomialEval] using hi

/-- Continuous functions admit actual uniform polynomial approximation on the closed ball. -/
theorem exists_polynomial_uniform_unitBall {g : Vec3 → ℝ} (hg : Continuous g)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : BallPolynomial,
      ∀ x ∈ weightedClosedUnitBall, |ballPolynomialEval p x - g x| < δ := by
  obtain ⟨q, hq⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    unitBallPolynomialContinuousHom.range unitBallPolynomialContinuous_separatesPoints
    (fun x : weightedClosedUnitBall ↦ g x.1) (hg.comp continuous_subtype_val) δ hδ
  obtain ⟨p, hp⟩ := q.property
  refine ⟨p, ?_⟩
  intro x hx
  have h := hq ⟨x, hx⟩
  rw [← hp] at h
  exact h

/-- The actual polynomial restriction is a linear map into the actual ball `L²` space. -/
def unitBallPolynomialL2Linear :
    BallPolynomial →ₗ[ℝ] Lp ℝ 2 (volume.restrict (vec3Ball 0 1)) where
  toFun := unitBallPolynomialL2
  map_add' p q := by
    apply Lp.ext
    have hp := (unitBallPolynomial_memLp p).coeFn_toLp
    have hq := (unitBallPolynomial_memLp q).coeFn_toLp
    have hpq := (unitBallPolynomial_memLp (p + q)).coeFn_toLp
    filter_upwards [hp, hq, hpq, Lp.coeFn_add (unitBallPolynomialL2 p) (unitBallPolynomialL2 q)]
      with x hx hy hxy hadd
    change unitBallPolynomialL2 p x = _ at hx
    change unitBallPolynomialL2 q x = _ at hy
    change unitBallPolynomialL2 (p + q) x = _ at hxy
    rw [hadd, hxy]
    simp [ballPolynomialEval, hx, hy]
  map_smul' c p := by
    apply Lp.ext
    have hp := (unitBallPolynomial_memLp p).coeFn_toLp
    have hcp := (unitBallPolynomial_memLp (c • p)).coeFn_toLp
    filter_upwards [hp, hcp, Lp.coeFn_smul c (unitBallPolynomialL2 p)] with x hx hcx hsmul
    change unitBallPolynomialL2 p x = _ at hx
    change unitBallPolynomialL2 (c • p) x = _ at hcx
    change unitBallPolynomialL2 (c • p) x = (c • unitBallPolynomialL2 p) x
    rw [hsmul, hcx]
    simp [ballPolynomialEval, hx]

/-- Uniform approximation gives approximation in the actual Hilbert norm. -/
theorem exists_polynomial_L2_approx_boundedContinuous (g : Vec3 →ᵇ ℝ)
    (hg : MemLp (g : Vec3 → ℝ) 2 (volume.restrict (vec3Ball 0 1)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : BallPolynomial, ‖unitBallPolynomialL2 p - hg.toLp g‖ < ε := by
  let M : ℝ := (measureUnivNNReal (volume.restrict (vec3Ball (0 : Vec3) 1)) : ℝ) ^
    (2 : ℝ≥0∞).toReal⁻¹
  have hM : 0 ≤ M := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  let δ : ℝ := ε / (M + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p, hp⟩ := exists_polynomial_uniform_unitBall g.continuous hδ
  refine ⟨p, ?_⟩
  have hb : ∀ᵐ x ∂volume.restrict (vec3Ball 0 1),
      ‖(unitBallPolynomialL2 p - hg.toLp g) x‖ ≤ δ := by
    filter_upwards [ae_restrict_mem (vec3Ball_measurable 0 1),
      (unitBallPolynomial_memLp p).coeFn_toLp, hg.coeFn_toLp,
      Lp.coeFn_sub (unitBallPolynomialL2 p) (hg.toLp g)] with x hx hpx hgx hsub
    change unitBallPolynomialL2 p x = _ at hpx
    rw [hsub]
    simpa [Pi.sub_apply, hpx, hgx] using
      (hp x (ballBoundaryWeight_pos_of_mem_unitBall hx).le).le
  have hn := Lp.norm_le_of_ae_bound hδ.le hb
  change ‖unitBallPolynomialL2 p - hg.toLp g‖ ≤ M * δ at hn
  have heq : δ * (M + 1) = ε := by
    dsimp [δ]
    field_simp
  exact hn.trans_lt (by nlinarith)

/-- Actual polynomial restrictions have dense range in the actual ball `L²` space. -/
theorem unitBallPolynomialL2_denseRange : DenseRange unitBallPolynomialL2 := by
  let S := (unitBallPolynomialL2Linear.range).topologicalClosure
  have hS : ∀ g : Vec3 →ᵇ ℝ,
      ∀ hg : MemLp (g : Vec3 → ℝ) 2 (volume.restrict (vec3Ball 0 1)), hg.toLp g ∈ S := by
    intro g hg
    change hg.toLp g ∈ closure (range unitBallPolynomialL2)
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_L2_approx_boundedContinuous g hg hε
    refine ⟨unitBallPolynomialL2 p, ⟨p, rfl⟩, ?_⟩
    simpa only [dist_eq_norm, norm_sub_rev] using hp
  have hd := BoundedContinuousFunction.toLp_denseRange ℝ
    (volume.restrict (vec3Ball (0 : Vec3) 1)) ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have hsubset : range (BoundedContinuousFunction.toLp (E := ℝ) 2
      (volume.restrict (vec3Ball (0 : Vec3) 1)) ℝ) ⊆ (S : Set _) := by
    intro f hf
    rcases hf with ⟨g, rfl⟩
    have hg : MemLp (g : Vec3 → ℝ) 2 (volume.restrict (vec3Ball 0 1)) :=
      g.memLp_top.mono_exponent (by norm_num)
    have heq : hg.toLp g = BoundedContinuousFunction.toLp 2
        (volume.restrict (vec3Ball 0 1)) ℝ g := by
      apply Lp.ext
      exact (hg.coeFn_toLp).trans (BoundedContinuousFunction.coeFn_toLp 2
        (volume.restrict (vec3Ball 0 1)) ℝ g).symm
    rw [← heq]
    exact hS g hg
  have hclosure : closure (range (BoundedContinuousFunction.toLp (E := ℝ) 2
      (volume.restrict (vec3Ball (0 : Vec3) 1)) ℝ)) ⊆ (S : Set _) :=
    closure_minimal hsubset unitBallPolynomialL2Linear.range.isClosed_topologicalClosure
  rw [hd.closure_range] at hclosure
  intro f
  exact hclosure (mem_univ f)

end FluidSingularSets
