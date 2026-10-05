-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.PolynomialBallDivergence
public import FluidSingularSets.LocalStokesEnergy
public import CKN.Foundation.Euclidean.SmoothIBP
public import CKN.Foundation.Parabolic.Vec3Norm
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Interior test approximations for the weighted ball fields

Actual smooth cutoff functions remove a shrinking boundary layer. Multiplying
by the vanishing ball weight gives compact tests supported strictly inside the
ball. Uniform gradient majorants and dominated convergence prove that the
actual derivative of the weighted smooth field has zero ball integral.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The fixed closed unit ball, described by its polynomial boundary weight. -/
def weightedClosedUnitBall : Set Vec3 := {x | 0 ≤ ballBoundaryWeight 0 1 x}

theorem weightedClosedUnitBall_isCompact : IsCompact weightedClosedUnitBall := by
  have hc : IsClosed weightedClosedUnitBall :=
    isClosed_le continuous_const (ballBoundaryWeight_contDiff 0 1).continuous
  apply (isCompact_closedBall (0 : Vec3) 1).of_isClosed_subset hc
  intro x hx
  have hs : (∑ i : Fin 3, x i ^ 2) ≤ 1 := by
    simpa [weightedClosedUnitBall, ballBoundaryWeight] using hx
  have he : vec3EuclideanNorm x ≤ 1 := by
    unfold vec3EuclideanNorm
    exact (Real.sqrt_le_sqrt hs).trans (by norm_num)
  simpa using (norm_le_vec3EuclideanNorm x).trans he

theorem ballBoundaryWeight_pos_of_mem_unitBall {x : Vec3} (hx : x ∈ vec3Ball 0 1) :
    0 < ballBoundaryWeight 0 1 x := by
  have hn : 0 ≤ ∑ i : Fin 3, x i ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hs := Real.sq_sqrt hn
  have hx' : Real.sqrt (∑ i : Fin 3, x i ^ 2) < 1 := by
    simpa [vec3EuclideanNorm] using mem_vec3Ball.mp hx
  simp only [ballBoundaryWeight, Pi.zero_apply, sub_zero, one_pow]
  nlinarith [Real.sqrt_nonneg (∑ i : Fin 3, x i ^ 2)]

theorem mem_unitBall_of_ballBoundaryWeight_pos {x : Vec3}
    (hx : 0 < ballBoundaryWeight 0 1 x) : x ∈ vec3Ball 0 1 := by
  have hn : 0 ≤ ∑ i : Fin 3, x i ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hs := Real.sq_sqrt hn
  have hw : 0 < 1 - ∑ i : Fin 3, x i ^ 2 := by simpa [ballBoundaryWeight] using hx
  apply mem_vec3Ball.mpr
  simp only [sub_zero, vec3EuclideanNorm]
  nlinarith [Real.sqrt_nonneg (∑ i : Fin 3, x i ^ 2)]

/-- A smooth cutoff equal to one away from a boundary layer of thickness `δ`. -/
def ballBoundaryCutoff (δ : ℝ) (x : Vec3) : ℝ :=
  Real.smoothTransition (2 * ballBoundaryWeight 0 1 x / δ - 1)

theorem ballBoundaryCutoff_contDiff (δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (ballBoundaryCutoff δ) := by
  apply Real.smoothTransition.contDiff.comp
  exact ((contDiff_const.mul (ballBoundaryWeight_contDiff 0 1)).div_const δ).sub
    contDiff_const

theorem ballBoundaryCutoff_nonneg (δ : ℝ) (x : Vec3) : 0 ≤ ballBoundaryCutoff δ x :=
  Real.smoothTransition.nonneg _

theorem ballBoundaryCutoff_le_one (δ : ℝ) (x : Vec3) : ballBoundaryCutoff δ x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem ballBoundaryCutoff_eq_zero {δ : ℝ} (hδ : 0 < δ) (x : Vec3)
    (hx : ballBoundaryWeight 0 1 x ≤ δ / 2) : ballBoundaryCutoff δ x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hdiv : 2 * ballBoundaryWeight 0 1 x / δ ≤ 1 := (div_le_one hδ).mpr (by linarith)
  linarith

theorem ballBoundaryCutoff_eq_one {δ : ℝ} (hδ : 0 < δ) (x : Vec3)
    (hx : δ ≤ ballBoundaryWeight 0 1 x) : ballBoundaryCutoff δ x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hdiv : 2 ≤ 2 * ballBoundaryWeight 0 1 x / δ :=
    (le_div_iff₀ hδ).mpr (by linarith)
  linarith

/-- The cutoff support is separated from the actual boundary of the ball. -/
theorem ballBoundaryCutoff_tsupport_subset {δ : ℝ} (hδ : 0 < δ) :
    tsupport (ballBoundaryCutoff δ) ⊆ {x | δ / 2 ≤ ballBoundaryWeight 0 1 x} := by
  apply closure_minimal
  · intro x hx
    by_contra h
    exact hx (ballBoundaryCutoff_eq_zero hδ x (le_of_lt (lt_of_not_ge h)))
  · exact isClosed_le continuous_const (ballBoundaryWeight_contDiff 0 1).continuous

theorem ballBoundaryCutoff_hasCompactSupport {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (ballBoundaryCutoff δ) := by
  apply weightedClosedUnitBall_isCompact.of_isClosed_subset isClosed_closure
  intro x hx
  have h := ballBoundaryCutoff_tsupport_subset hδ hx
  exact le_trans (by positivity : (0 : ℝ) ≤ δ / 2) h

theorem ballBoundaryCutoff_tsupport_subset_unitBall {δ : ℝ} (hδ : 0 < δ) :
    tsupport (ballBoundaryCutoff δ) ⊆ vec3Ball 0 1 := by
  intro x hx
  apply mem_unitBall_of_ballBoundaryWeight_pos
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < δ / 2)
    (ballBoundaryCutoff_tsupport_subset hδ hx)

/-- The actual interior smooth test approximating a weighted scalar field. -/
def weightedBallBoundaryTest (a : Vec3 → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (δ : ℝ) (hδ : 0 < δ) : WeakTestFunction (vec3Ball 0 1) where
  toFun := fun x ↦ ballBoundaryCutoff δ x * (ballBoundaryWeight 0 1 x * a x)
  contDiff := (ballBoundaryCutoff_contDiff δ).mul ((ballBoundaryWeight_contDiff 0 1).mul ha)
  hasCompactSupport := (ballBoundaryCutoff_hasCompactSupport hδ).mul_right
  tsupport_subset := tsupport_mul_subset_left.trans
    (ballBoundaryCutoff_tsupport_subset_unitBall hδ)

/-- The cutoff equals one in a whole neighborhood of any point off the removed layer. -/
theorem ballBoundaryCutoff_eventually_one {δ : ℝ} (hδ : 0 < δ) {x : Vec3}
    (hx : δ < ballBoundaryWeight 0 1 x) : ballBoundaryCutoff δ =ᶠ[𝓝 x] fun _ ↦ 1 := by
  have hn : ∀ᶠ y in 𝓝 x, δ < ballBoundaryWeight 0 1 y :=
    (isOpen_lt continuous_const (ballBoundaryWeight_contDiff 0 1).continuous).mem_nhds hx
  filter_upwards [hn] with y hy
  exact ballBoundaryCutoff_eq_one hδ y hy.le

/-- In the interior the actual test derivatives are eventually the original derivatives. -/
theorem weightedBallBoundaryTest_partialDeriv_eq {a : Vec3 → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) {δ : ℝ} (hδ : 0 < δ) {x : Vec3}
    (hx : δ < ballBoundaryWeight 0 1 x) (i : Fin 3) :
    (weightedBallBoundaryTest a ha δ hδ).partialDeriv i x =
      spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a y) i x := by
  change (fderiv ℝ (weightedBallBoundaryTest a ha δ hδ).toFun x) (basisVec i) = _
  have heq : (weightedBallBoundaryTest a ha δ hδ).toFun =ᶠ[𝓝 x]
      fun y ↦ ballBoundaryWeight 0 1 y * a y := by
    filter_upwards [ballBoundaryCutoff_eventually_one hδ hx] with y hy
    change ballBoundaryCutoff δ y * _ = _
    rw [hy, one_mul]
  rw [heq.fderiv_eq]
  rfl

/-- The genuine smooth transition derivative has a finite global bound. -/
theorem exists_smoothTransition_deriv_bound :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ T := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨|M|, abs_nonneg M, ?_⟩
  intro t
  by_cases ht0 : t ≤ 0
  · have hmin : IsLocalMin Real.smoothTransition t := by
      change ∀ᶠ s in 𝓝 t, Real.smoothTransition t ≤ Real.smoothTransition s
      rw [Real.smoothTransition.zero_of_nonpos ht0]
      exact .of_forall Real.smoothTransition.nonneg
    rw [hmin.deriv_eq_zero]
    simp
  · by_cases ht1 : 1 ≤ t
    · have hmax : IsLocalMax Real.smoothTransition t := by
        change ∀ᶠ s in 𝓝 t, Real.smoothTransition s ≤ Real.smoothTransition t
        rw [Real.smoothTransition.one_of_one_le ht1]
        exact .of_forall Real.smoothTransition.le_one
      rw [hmax.deriv_eq_zero]
      simp
    · exact (hM t ⟨(lt_of_not_ge ht0).le, (lt_of_not_ge ht1).le⟩).trans (le_abs_self M)

/-- The cutoff derivative is an actual chain-rule identity. -/
theorem spatialDeriv_ballBoundaryCutoff (δ : ℝ) (i : Fin 3) (x : Vec3) :
    spatialDeriv (ballBoundaryCutoff δ) i x =
      deriv Real.smoothTransition (2 * ballBoundaryWeight 0 1 x / δ - 1) *
        (2 * spatialDeriv (ballBoundaryWeight 0 1) i x / δ) := by
  have hw := ((ballBoundaryWeight_contDiff 0 1).differentiable (by simp) x).hasFDerivAt
  have ha : HasFDerivAt (fun y ↦ 2 * ballBoundaryWeight 0 1 y / δ - 1)
      ((2 / δ) • fderiv ℝ (ballBoundaryWeight 0 1) x) x := by
    have heq : (fun y ↦ 2 * ballBoundaryWeight 0 1 y / δ - 1) =
        fun y ↦ (2 / δ) * ballBoundaryWeight 0 1 y - 1 := by
      funext y
      ring
    rw [heq]
    exact (hw.const_mul (2 / δ)).sub_const 1
  have ht := ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
    (2 * ballBoundaryWeight 0 1 x / δ - 1)).hasDerivAt
  have hh := ht.comp_hasFDerivAt x ha
  change (fderiv ℝ (ballBoundaryCutoff δ) x) (basisVec i) = _
  rw [show ballBoundaryCutoff δ = Real.smoothTransition ∘
    (fun y ↦ 2 * ballBoundaryWeight 0 1 y / δ - 1) from rfl, hh.fderiv]
  simp only [smul_apply, smul_eq_mul, spatialDeriv]
  ring

/-- Multiplication by the vanishing weight cancels the shrinking cutoff derivative. -/
theorem ballBoundaryWeight_mul_spatialDeriv_cutoff_le {δ T : ℝ} (hδ : 0 < δ)
    (hT : 0 ≤ T) (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ T)
    {x : Vec3} (hx : x ∈ vec3Ball 0 1) (i : Fin 3) :
    |ballBoundaryWeight 0 1 x * spatialDeriv (ballBoundaryCutoff δ) i x| ≤
      2 * T * |spatialDeriv (ballBoundaryWeight 0 1) i x| := by
  have hw : 0 < ballBoundaryWeight 0 1 x := ballBoundaryWeight_pos_of_mem_unitBall hx
  by_cases hd : δ ≤ ballBoundaryWeight 0 1 x
  · have hmax : IsLocalMax (ballBoundaryCutoff δ) x := by
      change ∀ᶠ y in 𝓝 x, ballBoundaryCutoff δ y ≤ ballBoundaryCutoff δ x
      rw [ballBoundaryCutoff_eq_one hδ x hd]
      exact .of_forall (ballBoundaryCutoff_le_one δ)
    rw [spatialDeriv, hmax.fderiv_eq_zero]
    simp only [zero_apply, mul_zero, abs_zero]
    positivity
  · rw [spatialDeriv_ballBoundaryCutoff, abs_mul, abs_mul, abs_div, abs_mul,
      abs_of_pos hw, abs_of_pos hδ]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hwδ : ballBoundaryWeight 0 1 x ≤ δ := (lt_of_not_ge hd).le
    calc
      ballBoundaryWeight 0 1 x *
          (|deriv Real.smoothTransition (2 * ballBoundaryWeight 0 1 x / δ - 1)| *
            (2 * |spatialDeriv (ballBoundaryWeight 0 1) i x| / δ))
          ≤ δ * (T * (2 * |spatialDeriv (ballBoundaryWeight 0 1) i x| / δ)) := by
            gcongr
            exact hb _
      _ = 2 * T * |spatialDeriv (ballBoundaryWeight 0 1) i x| := by
        field_simp

/-- The weighted test derivative has a uniform bound by fixed smooth data. -/
theorem weightedBallBoundaryTest_partialDeriv_le {a : Vec3 → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ T)
    {x : Vec3} (hx : x ∈ vec3Ball 0 1) (i : Fin 3) :
    |(weightedBallBoundaryTest a ha δ hδ).partialDeriv i x| ≤
      |spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a y) i x| +
        2 * T * |spatialDeriv (ballBoundaryWeight 0 1) i x| * |a x| := by
  change |spatialDeriv (fun y ↦ ballBoundaryCutoff δ y *
    (ballBoundaryWeight 0 1 y * a y)) i x| ≤ _
  rw [spatialDeriv_mul ((ballBoundaryCutoff_contDiff δ).differentiable (by simp) x)
    (((ballBoundaryWeight_contDiff 0 1).mul ha).differentiable (by simp) x)]
  calc
    _ ≤ |spatialDeriv (ballBoundaryCutoff δ) i x * (ballBoundaryWeight 0 1 x * a x)| +
        |ballBoundaryCutoff δ x * spatialDeriv
          (fun y ↦ ballBoundaryWeight 0 1 y * a y) i x| := abs_add_le _ _
    _ ≤ 2 * T * |spatialDeriv (ballBoundaryWeight 0 1) i x| * |a x| +
        |spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a y) i x| := by
      apply add_le_add
      · rw [← mul_assoc, mul_comm (spatialDeriv (ballBoundaryCutoff δ) i x), abs_mul]
        exact mul_le_mul_of_nonneg_right
          (ballBoundaryWeight_mul_spatialDeriv_cutoff_le hδ hT hb hx i) (abs_nonneg _)
      · rw [abs_mul, abs_of_nonneg (ballBoundaryCutoff_nonneg δ x)]
        exact mul_le_of_le_one_left (abs_nonneg _) (ballBoundaryCutoff_le_one δ x)
    _ = _ := add_comm _ _

/-- A positive boundary-layer width tending to zero. -/
def ballBoundaryWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem ballBoundaryWidth_pos (n : ℕ) : 0 < ballBoundaryWidth n := by
  unfold ballBoundaryWidth
  positivity

theorem ballBoundaryWidth_tendsto_zero : Tendsto ballBoundaryWidth atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The canonical sequence of actual interior compact tests. -/
def weightedBallBoundaryTestSeq (a : Vec3 → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (n : ℕ) : WeakTestFunction (vec3Ball 0 1) :=
  weightedBallBoundaryTest a ha (ballBoundaryWidth n) (ballBoundaryWidth_pos n)

/-- At every interior point the test gradients eventually agree with the original gradient. -/
theorem weightedBallBoundaryTestSeq_partialDeriv_eventually {a : Vec3 → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) {x : Vec3} (hx : x ∈ vec3Ball 0 1) (i : Fin 3) :
    (fun n ↦ (weightedBallBoundaryTestSeq a ha n).partialDeriv i x) =ᶠ[atTop]
      fun _ ↦ spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a y) i x := by
  have hn : ∀ᶠ n in atTop, ballBoundaryWidth n < ballBoundaryWeight 0 1 x :=
    (tendsto_order.mp ballBoundaryWidth_tendsto_zero).2 _
      (ballBoundaryWeight_pos_of_mem_unitBall hx)
  filter_upwards [hn] with n hn
  exact weightedBallBoundaryTest_partialDeriv_eq ha (ballBoundaryWidth_pos n) hn i

/-- A fixed smooth-data majorant for the entire sequence of test derivatives. -/
def weightedBoundaryDerivativeMajorant (a : Vec3 → ℝ) (T : ℝ) (i : Fin 3) (x : Vec3) : ℝ :=
  |spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a y) i x| +
    2 * T * |spatialDeriv (ballBoundaryWeight 0 1) i x| * |a x|

theorem weightedBoundaryDerivativeMajorant_continuous {a : Vec3 → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (T : ℝ) (i : Fin 3) :
    Continuous (weightedBoundaryDerivativeMajorant a T i) := by
  exact ((contDiff_spatialDeriv_smooth
    ((ballBoundaryWeight_contDiff 0 1).mul ha) i).continuous.abs).add
    (((continuous_const.mul
      (contDiff_spatialDeriv_smooth (ballBoundaryWeight_contDiff 0 1) i).continuous.abs)).mul
        ha.continuous.abs)

theorem weightedBoundaryDerivativeMajorant_integrable {a : Vec3 → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (T : ℝ) (i : Fin 3) :
    Integrable (weightedBoundaryDerivativeMajorant a T i) (volume.restrict (vec3Ball 0 1)) := by
  apply ((weightedBoundaryDerivativeMajorant_continuous ha T i).continuousOn.integrableOn_compact
    weightedClosedUnitBall_isCompact).mono_set
  intro x hx
  exact (ballBoundaryWeight_pos_of_mem_unitBall hx).le

/-- Genuine dominated convergence for the compact-test derivatives. -/
theorem weightedBallBoundaryTestSeq_partialDeriv_integral_tendsto {a : Vec3 → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (i : Fin 3) :
    Tendsto (fun n ↦ ∫ x in vec3Ball 0 1, (weightedBallBoundaryTestSeq a ha n).partialDeriv i x)
      atTop (𝓝 (∫ x in vec3Ball 0 1,
        spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a y) i x)) := by
  obtain ⟨T, hT, hb⟩ := exists_smoothTransition_deriv_bound
  apply tendsto_integral_of_dominated_convergence (weightedBoundaryDerivativeMajorant a T i)
  · intro n
    exact ((contDiff_spatialDeriv_smooth
      (weightedBallBoundaryTestSeq a ha n).contDiff i).continuous).aestronglyMeasurable
  · exact weightedBoundaryDerivativeMajorant_integrable ha T i
  · intro n
    filter_upwards [ae_restrict_mem (vec3Ball_measurable 0 1)] with x hx
    exact weightedBallBoundaryTest_partialDeriv_le ha (ballBoundaryWidth_pos n) hT hb hx i
  · filter_upwards [ae_restrict_mem (vec3Ball_measurable 0 1)] with x hx
    exact tendsto_const_nhds.congr'
      (weightedBallBoundaryTestSeq_partialDeriv_eventually ha hx i).symm

/-- Every actual compact interior test derivative has zero integral on the ball. -/
theorem weakTest_partialDeriv_integral_eq_zero (φ : WeakTestFunction (vec3Ball 0 1))
    (i : Fin 3) : (∫ x in vec3Ball 0 1, φ.partialDeriv i x) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · have h := integral_mul_spatialDeriv_eq_neg_integral_spatialDeriv_mul
      (u := fun _ : Vec3 ↦ (1 : ℝ)) contDiff_const φ.contDiff φ.hasCompactSupport i
    simpa [spatialDeriv, WeakTestFunction.partialDeriv] using h
  · intro x hx
    have hout : x ∉ tsupport φ.toFun := fun h ↦ hx (φ.tsupport_subset h)
    change (fderiv ℝ φ.toFun x) (basisVec i) = 0
    rw [fderiv_of_notMem_tsupport ℝ hout]
    rfl

/-- The actual derivative of the weighted smooth field has zero integral on the ball. -/
theorem weightedBallBoundary_derivative_integral_eq_zero {a : Vec3 → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (i : Fin 3) :
    (∫ x in vec3Ball 0 1, spatialDeriv (fun y ↦ ballBoundaryWeight 0 1 y * a y) i x) = 0 := by
  have hlim := weightedBallBoundaryTestSeq_partialDeriv_integral_tendsto ha i
  have hzero : (fun n ↦ ∫ x in vec3Ball 0 1,
      (weightedBallBoundaryTestSeq a ha n).partialDeriv i x) = fun _ ↦ (0 : ℝ) := by
    funext n
    exact weakTest_partialDeriv_integral_eq_zero _ i
  rw [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end FluidSingularSets
