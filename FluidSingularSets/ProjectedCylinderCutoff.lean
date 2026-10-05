-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedCutoffMixedEnergy
public import FluidSingularSets.TestedTimeEnergy

/-!
# Genuine projected time cutoffs with an arbitrary future cap

The future ramp has nonpositive derivative. The upper bound for the time
derivative therefore depends only on the lower ramp width, independently of
the available future time margin.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped Topology ContDiff

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The literal lower and upper smooth time ramps. -/
def projectedCylinderTimeCutoff (a b ε δ s : ℝ) : ℝ :=
  (1 - backwardTimeCutoff (a + ε) ε s) * backwardTimeCutoff b δ s

/-- Both actual time ramps are smooth. -/
theorem projectedCylinderTimeCutoff_smooth (a b ε δ : ℝ) :
    ContDiff ℝ ∞ (projectedCylinderTimeCutoff a b ε δ) :=
  (contDiff_const.sub backwardTimeCutoff_smooth).mul backwardTimeCutoff_smooth

/-- The true time cutoff is nonnegative. -/
theorem projectedCylinderTimeCutoff_nonneg (a b ε δ s : ℝ) :
    0 ≤ projectedCylinderTimeCutoff a b ε δ s :=
  mul_nonneg (sub_nonneg.mpr backwardTimeCutoff_le_one) backwardTimeCutoff_nonneg

/-- The true time cutoff is bounded by one. -/
theorem projectedCylinderTimeCutoff_le_one (a b ε δ s : ℝ) :
    projectedCylinderTimeCutoff a b ε δ s ≤ 1 := by
  have hb := backwardTimeCutoff_nonneg (t := a + ε) (h := ε) (s := s)
  have ht := backwardTimeCutoff_le_one (t := b) (h := δ) (s := s)
  exact (mul_le_mul_of_nonneg_left ht
    (sub_nonneg.mpr backwardTimeCutoff_le_one)).trans (by linarith)

/-- The actual ramp is exactly one throughout its common plateau. -/
theorem projectedCylinderTimeCutoff_eq_one {a b ε δ s : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hs : a + ε ≤ s) (hsb : s ≤ b - δ) :
    projectedCylinderTimeCutoff a b ε δ s = 1 := by
  simp only [projectedCylinderTimeCutoff,
    backwardTimeCutoff_eq_zero_of_ge hε hs,
    backwardTimeCutoff_eq_one_of_le hδ hsb, sub_zero, one_mul]

/-- The literal cutoff vanishes outside its actual closed time interval. -/
theorem projectedCylinderTimeCutoff_eq_zero_off {a b ε δ s : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hs : s ∉ Icc a b) :
    projectedCylinderTimeCutoff a b ε δ s = 0 := by
  by_cases ha : s < a
  · have hb : s ≤ a + ε - ε := by linarith only [ha]
    simp only [projectedCylinderTimeCutoff, backwardTimeCutoff_eq_one_of_le hε hb,
      sub_self, zero_mul]
  · have hb : b < s := by
      by_contra! hh
      exact hs ⟨le_of_not_gt ha, hh⟩
    simp only [projectedCylinderTimeCutoff,
      backwardTimeCutoff_eq_zero_of_ge hδ hb.le, mul_zero]

/-- The topological support lies in the actual closed time interval. -/
theorem projectedCylinderTimeCutoff_tsupport {a b ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    tsupport (projectedCylinderTimeCutoff a b ε δ) ⊆ Icc a b := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  by_contra ht
  exact hs (projectedCylinderTimeCutoff_eq_zero_off hε hδ ht)

/-- The actual time cutoff has compact support. -/
theorem projectedCylinderTimeCutoff_hasCompactSupport {a b ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    HasCompactSupport (projectedCylinderTimeCutoff a b ε δ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (projectedCylinderTimeCutoff_tsupport hε hδ)

/-- The actual time derivative bound is independent of the future ramp width. -/
theorem projectedCylinderTimeCutoff_deriv_le {a b ε δ s : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    deriv (projectedCylinderTimeCutoff a b ε δ) s ≤ 16 / ε := by
  have hb : HasDerivAt (backwardTimeCutoff (a + ε) ε)
      (deriv (backwardTimeCutoff (a + ε) ε) s) s :=
    (backwardTimeCutoff_smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have ht : HasDerivAt (backwardTimeCutoff b δ)
      (deriv (backwardTimeCutoff b δ) s) s :=
    (backwardTimeCutoff_smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have hd := ((hasDerivAt_const s (1 : ℝ)).sub hb).mul ht
  change deriv (fun s ↦ (1 - backwardTimeCutoff (a + ε) ε s) *
    backwardTimeCutoff b δ s) s ≤ 16 / ε
  change HasDerivAt (fun s ↦ (1 - backwardTimeCutoff (a + ε) ε s) *
    backwardTimeCutoff b δ s)
    ((0 - deriv (backwardTimeCutoff (a + ε) ε) s) * backwardTimeCutoff b δ s +
      (1 - backwardTimeCutoff (a + ε) ε s) * deriv (backwardTimeCutoff b δ) s) s at hd
  rw [hd.deriv]
  have hb0 := backwardTimeCutoff_deriv_nonpos (t := a + ε) (s := s) hε
  have ht0 := backwardTimeCutoff_deriv_nonpos (t := b) (s := s) hδ
  have hbu := backwardTimeCutoff_le_one (t := a + ε) (h := ε) (s := s)
  have htu := backwardTimeCutoff_le_one (t := b) (h := δ) (s := s)
  have hfirst := mul_le_mul_of_nonneg_left htu (neg_nonneg.mpr hb0)
  have hsecond := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hbu) ht0
  have hbound := backwardTimeCutoff_abs_deriv_le (t := a + ε) (s := s) hε
  rw [abs_of_nonpos hb0] at hbound
  linarith

/-- The actual sixth-power spatial cutoff times the true time cutoff. -/
def projectedCylinderTest (φ : Vec3 → ℝ) (a b ε δ : ℝ) (z : Vec3 × ℝ) : ℝ :=
  φ z.1 ^ 6 * projectedCylinderTimeCutoff a b ε δ z.2

/-- The literal projected test is nonnegative at every spacetime point. -/
theorem projectedCylinderTest_nonneg (φ : Vec3 → ℝ) (a b ε δ : ℝ) (z : Vec3 × ℝ) :
    0 ≤ projectedCylinderTest φ a b ε δ z :=
  mul_nonneg (pow_nonneg (by positivity : 0 ≤ φ z.1 ^ 2) 3 |>.trans_eq (by ring))
    (projectedCylinderTimeCutoff_nonneg a b ε δ z.2)

/-- The actual projected test has the precise compact product support. -/
theorem projectedCylinderTest_tsupport {φ : Vec3 → ℝ} {a b ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    tsupport (projectedCylinderTest φ a b ε δ) ⊆ tsupport φ ×ˢ Icc a b := by
  apply closure_minimal _ ((isClosed_tsupport φ).prod isClosed_Icc)
  intro z hz
  constructor
  · by_contra hx
    exact hz (by simp only [projectedCylinderTest, image_eq_zero_of_notMem_tsupport hx,
      zero_pow (by norm_num : (6 : ℕ) ≠ 0), zero_mul])
  · by_contra ht
    exact hz (by rw [projectedCylinderTest,
      projectedCylinderTimeCutoff_eq_zero_off hε hδ ht, mul_zero])

/-- Genuine spatial compact support and an interior closed time interval give
an actual admissible space-time test, for every positive future cap width. -/
theorem projectedCylinderTest_mem_spaceTimeTestFunction
    {Ω : Set Vec3} {I : Set ℝ} {φ : Vec3 → ℝ} {a b ε δ : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) (hI : Icc a b ⊆ I)
    (hε : 0 < ε) (hδ : 0 < δ) :
    projectedCylinderTest φ a b ε δ ∈ spaceTimeTestFunction (V := ℝ) Ω I := by
  have hs := projectedCylinderTest_tsupport (φ := φ) (a := a) (b := b) hε hδ
  refine ⟨((hφ.comp contDiff_fst).pow 6).mul
    ((projectedCylinderTimeCutoff_smooth a b ε δ).comp contDiff_snd), ?_, ?_⟩
  · exact (hφc.isCompact.prod isCompact_Icc).of_isClosed_subset (isClosed_tsupport _) hs
  · exact hs.trans (prod_mono hφs hI)

/-- The actual space-time test has precisely the real time-ramp derivative. -/
theorem projectedCylinderTest_timePartial (φ : Vec3 → ℝ) (a b ε δ : ℝ) (z : Vec3 × ℝ) :
    timePartial (projectedCylinderTest φ a b ε δ) z =
      φ z.1 ^ 6 * deriv (projectedCylinderTimeCutoff a b ε δ) z.2 := by
  have hd : HasDerivAt (fun s ↦ φ z.1 ^ 6 * projectedCylinderTimeCutoff a b ε δ s)
      (φ z.1 ^ 6 * deriv (projectedCylinderTimeCutoff a b ε δ) z.2) z.2 :=
    ((projectedCylinderTimeCutoff_smooth a b ε δ).differentiable
      (by simp)).differentiableAt.hasDerivAt.const_mul (φ z.1 ^ 6)
  exact hd.deriv

/-- The actual test's upper time derivative estimate has no future-cap constant. -/
theorem projectedCylinderTest_timePartial_le (φ : Vec3 → ℝ) {a b ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (z : Vec3 × ℝ) :
    timePartial (projectedCylinderTest φ a b ε δ) z ≤ φ z.1 ^ 6 * (16 / ε) := by
  rw [projectedCylinderTest_timePartial]
  exact mul_le_mul_of_nonneg_left (projectedCylinderTimeCutoff_deriv_le hε hδ)
    (by positivity)

end FluidSingularSets
