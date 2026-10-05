-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import CKN.Foundation.Sobolev.Cutoff.Ball
public import CKN.Pressure.SpatialDerivSupport
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic

/-!
# Actual canonical cutoff second derivatives

The canonical transition profile has a genuinely bounded second derivative:
its first derivative has compact support and its second derivative is continuous.
The actual quadratic ball argument and the chain rule then give uniform inverse
square gap bounds for the sixth-power spatial cutoff used in projected energy.
-/

@[expose] public section

open CKN Set Filter
open CKN.Foundation.Parabolic
open scoped Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual transition derivative vanishes outside its closed transition interval. -/
theorem smoothTransitionProfile_deriv_zero_off {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) :
    deriv smoothTransitionProfile t = 0 := by
  by_cases ht0 : t < 0
  · have he : smoothTransitionProfile =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht0] with s hs
      exact smoothTransitionProfile.zero_of_nonpos hs.le
    simpa only [deriv_const] using he.deriv_eq
  · have ht1 : 1 < t := by
      by_contra! hh
      exact ht ⟨le_of_not_gt ht0, hh⟩
    have he : smoothTransitionProfile =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds ht1] with s hs
      exact smoothTransitionProfile.one_of_one_le hs.le
    simpa only [deriv_const] using he.deriv_eq

/-- The actual transition derivative has genuine compact support. -/
theorem smoothTransitionProfile_deriv_hasCompactSupport :
    HasCompactSupport (deriv smoothTransitionProfile) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro t ht
  by_contra hh
  exact ht (smoothTransitionProfile_deriv_zero_off hh)

/-- Smoothness and actual compact derivative support give a universal second-derivative bound. -/
theorem exists_smoothTransitionProfile_second_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |deriv (deriv smoothTransitionProfile) t| ≤ B := by
  have hD : ContDiff ℝ (⊤ : ℕ∞) (deriv smoothTransitionProfile) :=
    (contDiff_infty_iff_deriv.mp smoothTransitionProfile.smooth).2
  have hDD : Continuous (deriv (deriv smoothTransitionProfile)) :=
    (contDiff_infty_iff_deriv.mp hD).2.continuous
  obtain ⟨B, hB⟩ := (smoothTransitionProfile_deriv_hasCompactSupport.deriv
    ).exists_bound_of_continuous hDD
  refine ⟨max B 0, le_max_right _ _, fun t ↦ ?_⟩
  have hb : |deriv (deriv smoothTransitionProfile) t| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB t
  exact hb.trans (le_max_left _ _)

/-- A genuine finite bound for the second derivative of the actual transition profile. -/
def canonicalTransitionSecondBound : ℝ :=
  exists_smoothTransitionProfile_second_bound.choose

theorem canonicalTransitionSecondBound_nonneg : 0 ≤ canonicalTransitionSecondBound :=
  exists_smoothTransitionProfile_second_bound.choose_spec.1

theorem smoothTransitionProfile_abs_second_le (t : ℝ) :
    |deriv (deriv smoothTransitionProfile) t| ≤ canonicalTransitionSecondBound :=
  exists_smoothTransitionProfile_second_bound.choose_spec.2 t

private theorem ballArgument_smooth (r s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (ballCutoffArgument (0 : Vec3) r s) := by
  unfold ballCutoffArgument
  simp only [div_eq_mul_inv]
  exact (contDiff_const.sub (contDiff_euclideanSqDist_left (0 : Vec3))).mul contDiff_const

private theorem spatialDeriv_coordinate (i j : Fin 3) (x : Vec3) :
    spatialDeriv (fun y : Vec3 ↦ y j) i x = if i = j then 1 else 0 := by
  change (fderiv ℝ (⇑(ContinuousLinearMap.proj (R := ℝ) j)) x) (basisVec i) = _
  rw [ContinuousLinearMap.fderiv]
  simp [basisVec_apply, eq_comm]

private theorem spatialDeriv_squared_distance (i : Fin 3) (x : Vec3) :
    spatialDeriv (fun y : Vec3 ↦ euclideanSqDist y 0) i x = 2 * x i := by
  have he : (fun y : Vec3 ↦ euclideanSqDist y 0) =
      fun y : Vec3 ↦ ∑ j : Fin 3, y j ^ 2 := by
    funext y
    simp only [euclideanSqDist, sub_zero, vecNormSq_eq_sum_sq]
  rw [he]
  simp only [spatialDeriv]
  rw [fderiv_fun_sum]
  · simp only [sum_apply]
    have hcoord (j : Fin 3) :
        (fderiv ℝ (fun y : Vec3 ↦ y j ^ 2) x) (basisVec i) =
          2 * x j * (if i = j then 1 else 0) := by
      rw [fderiv_fun_pow]
      · simp only [Nat.reduceSub, pow_one, smul_apply, smul_eq_mul, nsmul_eq_mul,
          Nat.cast_ofNat]
        rw [show (fderiv ℝ (fun y : Vec3 ↦ y j) x) (basisVec i) =
          if i = j then 1 else 0 from spatialDeriv_coordinate i j x]
      · fun_prop
    simp only [hcoord]
    simp
  · intro j _
    fun_prop

/-- The actual quadratic cutoff argument has its literal first spatial derivative. -/
theorem ballCutoffArgument_zero_spatialDeriv (r s : ℝ) (i : Fin 3) (x : Vec3) :
    spatialDeriv (ballCutoffArgument (0 : Vec3) r s) i x =
      -(2 * x i) / (s ^ 2 - r ^ 2) := by
  unfold ballCutoffArgument spatialDeriv
  simp only [div_eq_mul_inv]
  rw [fderiv_mul_const, fderiv_const_sub]
  · simp only [smul_apply, smul_eq_mul, neg_apply]
    rw [show (fderiv ℝ (fun y : Vec3 ↦ euclideanSqDist y 0) x) (basisVec i) =
      2 * x i from spatialDeriv_squared_distance i x]
    ring
  · exact ((contDiff_const.sub (contDiff_euclideanSqDist_left (0 : Vec3))).differentiable
      (by simp)) x

/-- The literal diagonal second derivative of the quadratic cutoff argument is constant. -/
theorem ballCutoffArgument_zero_diagonal_second (r s : ℝ) (i : Fin 3) (x : Vec3) :
    mixedSecond (ballCutoffArgument (0 : Vec3) r s) i i x =
      -(2 : ℝ) / (s ^ 2 - r ^ 2) := by
  have he : spatialDeriv (ballCutoffArgument (0 : Vec3) r s) i =
      fun y : Vec3 ↦ (-(2 : ℝ) / (s ^ 2 - r ^ 2)) * y i := by
    funext y
    exact (ballCutoffArgument_zero_spatialDeriv r s i y).trans (by ring)
  rw [mixedSecond, he]
  simp only [spatialDeriv]
  rw [fderiv_const_mul]
  · simp only [smul_apply, smul_eq_mul]
    rw [show (fderiv ℝ (fun y : Vec3 ↦ y i) x) (basisVec i) = 1 from
      by simpa only [spatialDeriv, ite_true] using spatialDeriv_coordinate i i x]
    ring
  · fun_prop

private theorem spatialDeriv_scalar_comp {F : ℝ → ℝ} {g : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin 3) (x : Vec3) :
    spatialDeriv (F ∘ g) i x = deriv F (g x) * spatialDeriv g i x := by
  unfold spatialDeriv
  rw [fderiv_comp x ((hF.differentiable (by simp)) (g x))
    ((hg.differentiable (by simp)) x)]
  simp only [ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul]

/-- The actual canonical cutoff has the literal quadratic-argument derivative. -/
theorem canonicalBallCutoff_zero_spatialDeriv (r R : ℝ) (i : Fin 3) (x : Vec3) :
    spatialDeriv (canonicalBallCutoff (0 : Vec3) r R) i x =
      deriv smoothTransitionProfile (ballCutoffArgument 0 r (ballCutoffMidRadius r R) x) *
        (-(2 * x i) / ((ballCutoffMidRadius r R) ^ 2 - r ^ 2)) := by
  rw [canonicalBallCutoff,
    spatialDeriv_scalar_comp smoothTransitionProfile.smooth (ballArgument_smooth r _),
    ballCutoffArgument_zero_spatialDeriv]

/-- The actual canonical cutoff diagonal Hessian is the genuine second-order chain rule. -/
theorem canonicalBallCutoff_zero_diagonal_second (r R : ℝ) (i : Fin 3) (x : Vec3) :
    mixedSecond (canonicalBallCutoff (0 : Vec3) r R) i i x =
      deriv (deriv smoothTransitionProfile)
          (ballCutoffArgument 0 r (ballCutoffMidRadius r R) x) *
        (-(2 * x i) / ((ballCutoffMidRadius r R) ^ 2 - r ^ 2)) ^ 2 +
      deriv smoothTransitionProfile (ballCutoffArgument 0 r (ballCutoffMidRadius r R) x) *
        (-(2 : ℝ) / ((ballCutoffMidRadius r R) ^ 2 - r ^ 2)) := by
  let g := ballCutoffArgument (0 : Vec3) r (ballCutoffMidRadius r R)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := ballArgument_smooth r _
  have hP : ContDiff ℝ (⊤ : ℕ∞) (deriv smoothTransitionProfile) :=
    (contDiff_infty_iff_deriv.mp smoothTransitionProfile.smooth).2
  have he : spatialDeriv (canonicalBallCutoff (0 : Vec3) r R) i =
      fun y ↦ (deriv smoothTransitionProfile ∘ g) y * spatialDeriv g i y := by
    funext y
    exact spatialDeriv_scalar_comp smoothTransitionProfile.smooth hg i y
  rw [mixedSecond, he, spatialDeriv_mul
    ((hP.comp hg).differentiable (by simp) x)
    ((contDiff_spatialDeriv_smooth hg i).differentiable (by simp) x),
    spatialDeriv_scalar_comp hP hg]
  change deriv (deriv smoothTransitionProfile) (g x) * spatialDeriv g i x *
      spatialDeriv g i x + deriv smoothTransitionProfile (g x) * mixedSecond g i i x = _
  rw [ballCutoffArgument_zero_spatialDeriv, ballCutoffArgument_zero_diagonal_second]
  ring

private theorem cutoff_quadratic_den_lower {r R : ℝ} (hr : (3 / 4 : ℝ) ≤ r)
    (hrR : r < R) :
    (R - r) / 2 ≤ (ballCutoffMidRadius r R) ^ 2 - r ^ 2 := by
  have hs : 1 ≤ ballCutoffMidRadius r R + r := by
    unfold ballCutoffMidRadius
    linarith
  have hgap : 0 < ballCutoffMidRadius r R - r := by
    unfold ballCutoffMidRadius
    linarith
  have hh := mul_nonneg hgap.le (sub_nonneg.mpr hs)
  unfold ballCutoffMidRadius at hh ⊢
  nlinarith

/-- The actual quadratic argument has a uniform first derivative on the support ball. -/
theorem canonicalBallCutoff_argument_first_bound {r R : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrR : r < R) (hR : R ≤ 1)
    (i : Fin 3) {x : Vec3} (hx : x ∈ euclideanBall 0 R) :
    |spatialDeriv (ballCutoffArgument 0 r (ballCutoffMidRadius r R)) i x| ≤
      4 / (R - r) := by
  have hd : 0 < R - r := sub_pos.mpr hrR
  have hdenlow := cutoff_quadratic_den_lower hr hrR
  have hden : 0 < (ballCutoffMidRadius r R) ^ 2 - r ^ 2 := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hxi : |x i| ≤ 1 := by
    have hh := sq_coord_sub_le_euclideanSqDist x (0 : Vec3) i
    simp only [Pi.zero_apply, sub_zero] at hh
    change euclideanSqDist x 0 < R ^ 2 at hx
    exact (abs_le_of_sq_le_sq (hh.trans hx.le) hR0).trans hR
  rw [ballCutoffArgument_zero_spatialDeriv, abs_div, abs_neg, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hden]
  calc
    _ ≤ 2 / ((ballCutoffMidRadius r R) ^ 2 - r ^ 2) := by
      apply div_le_div_of_nonneg_right _ hden.le
      linarith
    _ ≤ _ := (div_le_div_iff₀ hden hd).mpr (by nlinarith)

/-- The actual quadratic argument has a uniform second derivative on the unit-radius interval. -/
theorem canonicalBallCutoff_argument_second_bound {r R : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrR : r < R) (hR : R ≤ 1)
    (i : Fin 3) (x : Vec3) :
    |mixedSecond (ballCutoffArgument 0 r (ballCutoffMidRadius r R)) i i x| ≤
      4 / (R - r) ^ 2 := by
  have hd : 0 < R - r := sub_pos.mpr hrR
  have hd1 : R - r ≤ 1 := by linarith
  have hdenlow := cutoff_quadratic_den_lower hr hrR
  have hden : 0 < (ballCutoffMidRadius r R) ^ 2 - r ^ 2 := by linarith
  rw [ballCutoffArgument_zero_diagonal_second, abs_div, abs_neg,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hden]
  have hh : 2 / ((ballCutoffMidRadius r R) ^ 2 - r ^ 2) ≤ 4 / (R - r) :=
    (div_le_div_iff₀ hden hd).mpr (by nlinarith)
  exact hh.trans (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hd)
    (by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd1)]))

/-- The true canonical cutoff Hessian has a genuine universal inverse square gap bound. -/
theorem canonicalBallCutoff_zero_second_bound {r R : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrR : r < R) (hR : R ≤ 1) (i : Fin 3) (x : Vec3) :
    |mixedSecond (canonicalBallCutoff (0 : Vec3) r R) i i x| ≤
      (16 * canonicalTransitionSecondBound + 32) / (R - r) ^ 2 := by
  have hB := canonicalTransitionSecondBound_nonneg
  have hd : 0 < R - r := sub_pos.mpr hrR
  by_cases hx : x ∈ tsupport (canonicalBallCutoff (0 : Vec3) r R)
  · have hball := canonicalBallCutoff_tsupport_subset_outer (by linarith : 0 ≤ r) hrR hx
    have hfirst := canonicalBallCutoff_argument_first_bound hr hrR hR i hball
    have hsecond := canonicalBallCutoff_argument_second_bound hr hrR hR i x
    rw [ballCutoffArgument_zero_spatialDeriv] at hfirst
    rw [ballCutoffArgument_zero_diagonal_second] at hsecond
    rw [canonicalBallCutoff_zero_diagonal_second]
    calc
      _ ≤ |deriv (deriv smoothTransitionProfile)
          (ballCutoffArgument 0 r (ballCutoffMidRadius r R) x)| *
            |-(2 * x i) / ((ballCutoffMidRadius r R) ^ 2 - r ^ 2)| ^ 2 +
          |deriv smoothTransitionProfile
            (ballCutoffArgument 0 r (ballCutoffMidRadius r R) x)| *
              |-(2 : ℝ) / ((ballCutoffMidRadius r R) ^ 2 - r ^ 2)| := by
        calc
          _ ≤ |deriv (deriv smoothTransitionProfile)
                (ballCutoffArgument 0 r (ballCutoffMidRadius r R) x) *
                  (-(2 * x i) / ((ballCutoffMidRadius r R) ^ 2 - r ^ 2)) ^ 2| +
              |deriv smoothTransitionProfile
                (ballCutoffArgument 0 r (ballCutoffMidRadius r R) x) *
                  (-(2 : ℝ) / ((ballCutoffMidRadius r R) ^ 2 - r ^ 2))| :=
            abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_pow, abs_mul]
      _ ≤ canonicalTransitionSecondBound * (4 / (R - r)) ^ 2 +
          8 * (4 / (R - r) ^ 2) := by
        gcongr
        · exact smoothTransitionProfile_abs_second_le _
        · exact smoothTransitionProfile.abs_deriv_le_eight _
      _ = _ := by field_simp; ring
  · have hn : x ∉ tsupport (mixedSecond (canonicalBallCutoff (0 : Vec3) r R) i i) :=
      fun hh ↦ hx (tsupport_mixedSecond_subset i i hh)
    rw [image_eq_zero_of_notMem_tsupport hn, abs_zero]
    positivity

private theorem spatialDeriv_power {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (n : ℕ) (i : Fin 3) (x : Vec3) :
    spatialDeriv (fun y ↦ φ y ^ n) i x =
      (n : ℝ) * φ x ^ (n - 1) * spatialDeriv φ i x := by
  simp only [spatialDeriv, fderiv_fun_pow n
    (hφ.differentiable (by simp)).differentiableAt, nsmul_eq_mul, smul_apply, smul_eq_mul]

/-- The true sixth-power cutoff has its literal second spatial derivative. -/
theorem mixedSecond_cutoff_sixth {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin 3) (x : Vec3) :
    mixedSecond (fun y ↦ φ y ^ 6) i i x =
      30 * φ x ^ 4 * spatialDeriv φ i x ^ 2 + 6 * φ x ^ 5 * mixedSecond φ i i x := by
  have he : spatialDeriv (fun y ↦ φ y ^ 6) i =
      fun y ↦ 6 * φ y ^ 5 * spatialDeriv φ i y := by
    funext y
    simpa only [Nat.cast_ofNat, Nat.reduceSub] using spatialDeriv_power hφ 6 i y
  have hd := hφ.differentiable (by simp)
  have hpd := (contDiff_spatialDeriv_smooth hφ i).differentiable (by simp)
  rw [mixedSecond, he]
  rw [spatialDeriv_mul (f := fun y ↦ 6 * φ y ^ 5) (g := spatialDeriv φ i)
    ((hd x).pow 5 |>.const_mul 6) (hpd x) i]
  have hc : spatialDeriv (fun y ↦ 6 * φ y ^ 5) i x =
      6 * spatialDeriv (fun y ↦ φ y ^ 5) i x := by
    unfold spatialDeriv
    rw [fderiv_const_mul (a := fun y : Vec3 ↦ φ y ^ 5) ((hd x).fun_pow 5) 6]
    simp only [smul_apply, smul_eq_mul]
  rw [hc, spatialDeriv_power hφ 5]
  simp only [Nat.cast_ofNat, Nat.reduceSub, mixedSecond]
  ring

/-- A genuine universal coefficient for the sixth-power canonical spatial Laplacian. -/
def canonicalBallCutoffSixthLaplacianConstant : ℝ :=
  288 * canonicalTransitionSecondBound + 92736

theorem canonicalBallCutoffSixthLaplacianConstant_nonneg :
    0 ≤ canonicalBallCutoffSixthLaplacianConstant := by
  unfold canonicalBallCutoffSixthLaplacianConstant
  positivity [canonicalTransitionSecondBound_nonneg]

/-- The true sixth-power canonical cutoff retains the fourth-power diffusion weight. -/
theorem canonicalBallCutoff_zero_sixth_laplacian_weighted_bound {r R : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrR : r < R) (hR : R ≤ 1) (x : Vec3) :
    |spatialLaplacian (fun y ↦ canonicalBallCutoff (0 : Vec3) r R y ^ 6) x| ≤
      canonicalBallCutoffSixthLaplacianConstant *
        canonicalBallCutoff (0 : Vec3) r R x ^ 4 / (R - r) ^ 2 := by
  let φ := canonicalBallCutoff (0 : Vec3) r R
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    canonicalBallCutoff_smooth 0 (by linarith : 0 ≤ r) hrR
  have hφ0 : 0 ≤ φ x := canonicalBallCutoff_nonneg 0 r R x
  have hφ1 : φ x ≤ 1 := canonicalBallCutoff_le_one 0 r R x
  have hB := canonicalTransitionSecondBound_nonneg
  have hd : 0 < R - r := sub_pos.mpr hrR
  have hfirst (i : Fin 3) : |spatialDeriv φ i x| ≤ 32 / (R - r) :=
    (abs_apply_le_vecEuclideanNorm (classicalGradient φ x) i).trans
      (canonicalBallCutoff_gradient_bound (by linarith : 0 ≤ r) hrR x)
  have hsecond (i : Fin 3) : |mixedSecond φ i i x| ≤
      (16 * canonicalTransitionSecondBound + 32) / (R - r) ^ 2 :=
    canonicalBallCutoff_zero_second_bound hr hrR hR i x
  have hpoint (i : Fin 3) : |mixedSecond (fun y ↦ φ y ^ 6) i i x| ≤
      (96 * canonicalTransitionSecondBound + 30912) * φ x ^ 4 / (R - r) ^ 2 := by
    rw [mixedSecond_cutoff_sixth hφ]
    calc
      _ ≤ 30 * φ x ^ 4 * |spatialDeriv φ i x| ^ 2 +
          6 * φ x ^ 5 * |mixedSecond φ i i x| := by
        calc
          _ ≤ |30 * φ x ^ 4 * spatialDeriv φ i x ^ 2| +
              |6 * φ x ^ 5 * mixedSecond φ i i x| := abs_add_le _ _
          _ = _ := by
            simp only [abs_mul, abs_pow, abs_of_nonneg hφ0,
              abs_of_pos (by norm_num : (0 : ℝ) < 30),
              abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      _ ≤ 30 * φ x ^ 4 * (32 / (R - r)) ^ 2 +
          6 * φ x ^ 4 * ((16 * canonicalTransitionSecondBound + 32) / (R - r) ^ 2) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) (hfirst i) 2) (by positivity)
        · have hp : φ x ^ 5 ≤ φ x ^ 4 :=
            pow_le_pow_of_le_one hφ0 hφ1 (by norm_num : (4 : ℕ) ≤ 5)
          have hh := mul_le_mul hp (hsecond i) (abs_nonneg _) (by positivity)
          nlinarith
      _ = _ := by field_simp; ring
  calc
    _ ≤ ∑ i : Fin 3, |mixedSecond (fun y ↦ φ y ^ 6) i i x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3,
        (96 * canonicalTransitionSecondBound + 30912) * φ x ^ 4 / (R - r) ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ hpoint i
    _ = _ := by
      simp only [Fin.sum_univ_three, canonicalBallCutoffSixthLaplacianConstant]
      dsimp only [φ]
      ring

/-- The actual sixth-power cutoff has a universal plain inverse square gap diffusion bound. -/
theorem canonicalBallCutoff_zero_sixth_laplacian_bound {r R : ℝ}
    (hr : (3 / 4 : ℝ) ≤ r) (hrR : r < R) (hR : R ≤ 1) (x : Vec3) :
    |spatialLaplacian (fun y ↦ canonicalBallCutoff (0 : Vec3) r R y ^ 6) x| ≤
      canonicalBallCutoffSixthLaplacianConstant / (R - r) ^ 2 := by
  apply (canonicalBallCutoff_zero_sixth_laplacian_weighted_bound hr hrR hR x).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact (mul_le_mul_of_nonneg_left
    (pow_le_one₀ (canonicalBallCutoff_nonneg 0 r R x) (canonicalBallCutoff_le_one 0 r R x))
    canonicalBallCutoffSixthLaplacianConstant_nonneg).trans_eq (mul_one _)

end FluidSingularSets
