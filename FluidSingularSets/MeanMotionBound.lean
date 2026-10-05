-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.WeightedMeanMotion
public import FluidSingularSets.MovingScale
public import CKN.Foundation.Parabolic.BallDisplays

/-!
# Quantitative motion of suitable weighted velocity means

Hölder estimates applied to the genuine weak-gradient acceleration formula control
the total variation of a weighted mean. Its continuous representative is bounded
by its time average plus that variation. All powers of the radius are explicit.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Core.Step4 CKN.Leray
open CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The three charge powers in the mean estimate all reduce to the endpoint
scale when the genuine charge is at most `ε * R^(25/23)`. -/
theorem mean_motion_endpoint_powers
    {R ε A : ℝ} (hR : 0 < R) (hRone : R ≤ 1)
    (hε : 0 < ε) (hεone : ε ≤ 1) (hA : 0 ≤ A)
    (hsmall : A ≤ ε * R ^ (25 / 23 : ℝ)) :
    R ^ (-(3 / 2 : ℝ)) * A ^ (3 / 10 : ℝ) +
        R ^ (-(3 / 2 : ℝ)) * A ^ (1 / 2 : ℝ) +
        R ^ (-2 : ℝ) * A ^ (4 / 5 : ℝ) ≤
      3 * (ε ^ (3 / 10 : ℝ) * R ^ (-(27 / 23 : ℝ))) := by
  have hfirst : R ^ (-(3 / 2 : ℝ)) * A ^ (3 / 10 : ℝ) ≤
      ε ^ (3 / 10 : ℝ) * R ^ (-(27 / 23 : ℝ)) := by
    calc
      _ ≤ R ^ (-(3 / 2 : ℝ)) * (ε * R ^ (25 / 23 : ℝ)) ^ (3 / 10 : ℝ) := by
        gcongr
      _ = _ := by
        rw [Real.mul_rpow hε.le (Real.rpow_nonneg hR.le _), ← Real.rpow_mul hR.le]
        rw [mul_left_comm, ← Real.rpow_add hR]
        norm_num
  have hsecond : R ^ (-(3 / 2 : ℝ)) * A ^ (1 / 2 : ℝ) ≤
      ε ^ (3 / 10 : ℝ) * R ^ (-(27 / 23 : ℝ)) := by
    calc
      _ ≤ R ^ (-(3 / 2 : ℝ)) * (ε * R ^ (25 / 23 : ℝ)) ^ (1 / 2 : ℝ) := by
        gcongr
      _ = ε ^ (1 / 2 : ℝ) * R ^ (-(22 / 23 : ℝ)) := by
        rw [Real.mul_rpow hε.le (Real.rpow_nonneg hR.le _), ← Real.rpow_mul hR.le]
        rw [mul_left_comm, ← Real.rpow_add hR]
        norm_num
      _ ≤ _ := mul_le_mul
        (Real.rpow_le_rpow_of_exponent_ge hε hεone (by norm_num))
        (Real.rpow_le_rpow_of_exponent_ge hR hRone (by norm_num))
        (by positivity) (by positivity)
  have hthird : R ^ (-2 : ℝ) * A ^ (4 / 5 : ℝ) ≤
      ε ^ (3 / 10 : ℝ) * R ^ (-(27 / 23 : ℝ)) := by
    calc
      _ ≤ R ^ (-2 : ℝ) * (ε * R ^ (25 / 23 : ℝ)) ^ (4 / 5 : ℝ) := by
        gcongr
      _ = ε ^ (4 / 5 : ℝ) * R ^ (-(26 / 23 : ℝ)) := by
        rw [Real.mul_rpow hε.le (Real.rpow_nonneg hR.le _), ← Real.rpow_mul hR.le]
        rw [mul_left_comm, ← Real.rpow_add hR]
        norm_num
      _ ≤ _ := mul_le_mul
        (Real.rpow_le_rpow_of_exponent_ge hε hεone (by norm_num))
        (Real.rpow_le_rpow_of_exponent_ge hR hRone (by norm_num))
        (by positivity) (by positivity)
  linarith

/-- Finite-volume Hölder controls the first moment by a higher moment. -/
theorem integral_norm_le_moment_mul_volume
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} [IsFiniteMeasure μ] {v : X → E} {a c : ℝ}
    (hac : a.HolderConjugate c) (hv : MemLp v (ENNReal.ofReal a) μ) :
    (∫ x, ‖v x‖ ∂μ) ≤
      (∫ x, ‖v x‖ ^ a ∂μ) ^ (1 / a) * (μ univ).toReal ^ (1 / c) := by
  have hnorm : MemLp (fun x ↦ ‖v x‖) (ENNReal.ofReal a) μ := hv.norm
  have hone : MemLp (fun _ : X ↦ (1 : ℝ)) (ENNReal.ofReal c) μ := memLp_const 1
  have hh := integral_mul_norm_le_Lp_mul_Lq hac hnorm hone
  simpa only [Real.norm_eq_abs, abs_norm, norm_one, mul_one,
    integral_const, smul_eq_mul, mul_one, Real.one_rpow, measureReal_def] using hh

/-- The unused volume exponent in the velocity-gradient Hölder estimate is `1/5`. -/
theorem integral_norm_mul_norm_le_three_tenths_half
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {v D : X → ℝ} (hv : MemLp v (ENNReal.ofReal (10 / 3 : ℝ)) μ)
    (hD : MemLp D 2 μ) :
    (∫ x, ‖v x‖ * ‖D x‖ ∂μ) ≤
      (∫ x, ‖v x‖ ^ (10 / 3 : ℝ) ∂μ) ^ (3 / 10 : ℝ) *
        (∫ x, ‖D x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (μ univ).toReal ^ (1 / 5 : ℝ) := by
  let : ENNReal.HolderTriple (ENNReal.ofReal (10 / 3 : ℝ)) 2
      (ENNReal.ofReal (5 / 4 : ℝ)) :=
    by
      convert (show Real.HolderTriple (10 / 3 : ℝ) 2 (5 / 4 : ℝ) by
        constructor <;> norm_num).ennrealOfReal using 1
      norm_num
  have hprod : MemLp (v * D) (ENNReal.ofReal (5 / 4 : ℝ)) μ := hv.mul hD
  have hnorm := eLpNorm_smul_le_mul_eLpNorm hv.aestronglyMeasurable hD.aestronglyMeasurable
    (p := ENNReal.ofReal (10 / 3 : ℝ)) (q := 2) (r := ENNReal.ofReal (5 / 4 : ℝ))
  have hfirst := integral_norm_le_moment_mul_volume
    (show (5 / 4 : ℝ).HolderConjugate 5 by constructor <;> norm_num) hprod
  have hmoment : (∫ x, ‖v x * D x‖ ^ (5 / 4 : ℝ) ∂μ) ^ (4 / 5 : ℝ) ≤
      (∫ x, ‖v x‖ ^ (10 / 3 : ℝ) ∂μ) ^ (3 / 10 : ℝ) *
        (∫ x, ‖D x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
    have hnon (f : X → ℝ) (p : ℝ) : 0 ≤ ∫ x, ‖f x‖ ^ p ∂μ :=
      integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
      hprod.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofReal_ne_top,
      hv.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofReal_ne_top,
      hD.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 5 / 4),
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 10 / 3),
      ENNReal.toReal_ofNat, show (5 / 4 : ℝ)⁻¹ = 4 / 5 by norm_num,
      show (10 / 3 : ℝ)⁻¹ = 3 / 10 by norm_num,
      show (2 : ℝ)⁻¹ = 1 / 2 by norm_num,
      ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (hnon (v * D) _) _),
      ENNReal.toReal_ofReal (Real.rpow_nonneg (hnon (fun x ↦ v x * D x) _) _),
      ENNReal.toReal_ofReal (Real.rpow_nonneg (hnon v _) _),
      ENNReal.toReal_ofReal (Real.rpow_nonneg (hnon D _) _)] using
      (ENNReal.toReal_mono (ENNReal.mul_ne_top hv.eLpNorm_ne_top hD.eLpNorm_ne_top) hnorm)
  calc
    _ ≤ (∫ x, ‖v x * D x‖ ^ (5 / 4 : ℝ) ∂μ) ^ (4 / 5 : ℝ) *
        (μ univ).toReal ^ (1 / 5 : ℝ) := by
      simpa only [Pi.mul_apply, norm_mul, show 1 / (5 / 4 : ℝ) = 4 / 5 by norm_num]
        using hfirst
    _ ≤ _ := mul_le_mul_of_nonneg_right hmoment (by positivity)

/-- A continuous primitive is bounded everywhere by its average on a nonempty
interval plus the total variation supplied by its genuine integrable derivative. -/
theorem norm_primitive_le_average_add_variation
    {a b : ℝ} (hab : a < b) {m g : ℝ → ℝ} (hm : Continuous m)
    (hg : IntegrableOn g (Ioo a b))
    (hinc : ∀ s t : ℝ, m t - m s = ∫ τ in s..t, (Ioo a b).indicator g τ)
    (t : ℝ) :
    ‖m t‖ ≤ (b - a)⁻¹ * (∫ s in Ioo a b, ‖m s‖) + ∫ s in Ioo a b, ‖g s‖ := by
  let g₀ := (Ioo a b).indicator g
  have hg₀ : Integrable g₀ volume := hg.integrable_indicator measurableSet_Ioo
  have hgnorm : (∫ s, ‖g₀ s‖) = ∫ s in Ioo a b, ‖g s‖ := by
    rw [show (fun s ↦ ‖g₀ s‖) = (Ioo a b).indicator (fun s ↦ ‖g s‖) from by
      funext s
      by_cases hs : s ∈ Ioo a b <;> simp [g₀, hs]]
    exact integral_indicator measurableSet_Ioo
  have hpoint (s : ℝ) : ‖m t‖ ≤ ‖m s‖ + ∫ τ in Ioo a b, ‖g τ‖ := by
    have hdiff : ‖m t - m s‖ ≤ ∫ τ in Ioo a b, ‖g τ‖ := by
      rw [hinc s t]
      calc
        _ ≤ ∫ τ in Set.uIoc s t, ‖g₀ τ‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
        _ ≤ ∫ τ, ‖g₀ τ‖ := integral_mono_measure Measure.restrict_le_self
          (Eventually.of_forall fun τ ↦ norm_nonneg _) hg₀.norm
        _ = _ := hgnorm
    have htri := norm_add_le (m t - m s) (m s)
    simp only [sub_add_cancel] at htri
    linarith
  have hmint : IntegrableOn (fun s ↦ ‖m s‖) (Ioo a b) :=
    hm.norm.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hfinite : volume (Ioo a b) < ∞ := by simp only [Real.volume_Ioo]; finiteness
  let : IsFiniteMeasure (volume.restrict (Ioo a b)) := isFiniteMeasure_restrict.mpr hfinite.ne
  have havg := integral_mono_ae
    (integrable_const (‖m t‖ - ∫ τ in Ioo a b, ‖g τ‖)) hmint
    (Eventually.of_forall fun s ↦ by linarith [hpoint s])
  rw [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ,
    Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith : 0 ≤ b - a)] at havg
  have hdiv : ‖m t‖ - ∫ τ in Ioo a b, ‖g τ‖ ≤
      (b - a)⁻¹ * (∫ s in Ioo a b, ‖m s‖) := by
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ (by linarith : 0 < b - a)).2
    simpa only [mul_comm] using havg
  linarith

/-- A pointwise integrable envelope controls a spatial integral and then its
time integral. No interchange of a nonintegrable pairing is required. -/
theorem integral_norm_spatial_integral_le_envelope
    {B : Set Vec3} {J : Set ℝ} {F G : Vec3 × ℝ → ℝ}
    (hG : Integrable G ((volume.restrict B).prod (volume.restrict J)))
    (hbound : ∀ w, ‖F w‖ ≤ G w) :
    (∫ t in J, ‖∫ x in B, F (x, t)‖) ≤
      ∫ w, G w ∂((volume.restrict B).prod (volume.restrict J)) := by
  rw [integral_prod_symm G hG]
  apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
    hG.integral_prod_right
  filter_upwards [hG.prod_left_ae] with t ht
  exact norm_integral_le_of_norm_le ht (Eventually.of_forall fun x ↦ hbound (x, t))

private theorem component_moment_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {v : X → Vec3} {a : ℝ} (ha : 0 ≤ a)
    (hint : Integrable (fun x ↦ ‖v x‖ ^ a) μ) (i : Fin 3) :
    (∫ x, ‖v x i‖ ^ a ∂μ) ≤ ∫ x, ‖v x‖ ^ a ∂μ := by
  apply integral_mono_of_nonneg
    (Eventually.of_forall fun x ↦ Real.rpow_nonneg (norm_nonneg _) _) hint
  exact Eventually.of_forall fun x ↦ Real.rpow_le_rpow (norm_nonneg _)
    (norm_le_pi_norm (v x) i) ha

/-- The actual three-term box charge, in the fixed finite-dimensional norms
used by the CKN library. -/
def meanMotionCharge (Q : Set ParabolicPoint) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (Dp : ParabolicPoint → Vec3) : ℝ :=
  ∫ w in Q, ‖Du w‖ ^ (2 : ℝ) + ‖u w‖ ^ (10 / 3 : ℝ) + ‖Dp w‖ ^ (5 / 4 : ℝ)

/-- With a uniform component moment budget, the gradient acceleration formula
has the exact volume powers used in the manuscript. -/
theorem weighted_gradient_acceleration_integral_le
    {B : Set Vec3} {J : Set ℝ} (hB : volume B < ∞) (hJ : volume J < ∞)
    {u : Vec3 × ℝ → Vec3} {D : Vec3 × ℝ → Fin 3 → Vec3}
    {P : Vec3 × ℝ → Vec3} {χ : Vec3 → ℝ} {g : ℝ → ℝ}
    {L₀ L₁ A : ℝ} (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hA : 0 ≤ A)
    (hweight : ∀ x, ‖χ x‖ ≤ L₀)
    (hgradient : ∀ x j, ‖spatialDeriv χ j x‖ ≤ L₁)
    (i : Fin 3)
    (hu : ∀ j, MemLp (fun w ↦ u w j) (ENNReal.ofReal (10 / 3 : ℝ))
      ((volume.restrict B).prod (volume.restrict J)))
    (hD : ∀ j, MemLp (fun w ↦ D w i j) 2
      ((volume.restrict B).prod (volume.restrict J)))
    (hP : MemLp (fun w ↦ P w i) (ENNReal.ofReal (5 / 4 : ℝ))
      ((volume.restrict B).prod (volume.restrict J)))
    (huA : ∀ j, (∫ w, ‖u w j‖ ^ (10 / 3 : ℝ)
      ∂((volume.restrict B).prod (volume.restrict J))) ≤ A)
    (hDA : ∀ j, (∫ w, ‖D w i j‖ ^ (2 : ℝ)
      ∂((volume.restrict B).prod (volume.restrict J))) ≤ A)
    (hPA : (∫ w, ‖P w i‖ ^ (5 / 4 : ℝ)
      ∂((volume.restrict B).prod (volume.restrict J))) ≤ A)
    (hformula : ∀ᵐ t ∂volume.restrict J,
      g t = -(∫ x in B, ∑ j, D (x, t) i j * spatialDeriv χ j x) -
        (∫ x in B, χ x * ∑ j, u (x, t) j * D (x, t) i j) -
        (∫ x in B, P (x, t) i * χ x)) :
    (∫ t in J, ‖g t‖) ≤
      3 * L₁ * A ^ (1 / 2 : ℝ) * ((volume B * volume J).toReal) ^ (1 / 2 : ℝ) +
        4 * L₀ * A ^ (4 / 5 : ℝ) * ((volume B * volume J).toReal) ^ (1 / 5 : ℝ) := by
  let μ := (volume.restrict B).prod (volume.restrict J)
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hB.ne
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr hJ.ne
  have hμ : μ univ = volume B * volume J := by
    rw [show (univ : Set (Vec3 × ℝ)) = univ ×ˢ univ by ext; simp,
      Measure.prod_prod]
    simp only [Measure.restrict_apply_univ]
  let H₁ : Vec3 × ℝ → ℝ := fun w ↦ L₁ * ∑ j, ‖D w i j‖
  let H₂ : Vec3 × ℝ → ℝ := fun w ↦ L₀ * ∑ j, ‖u w j‖ * ‖D w i j‖
  let H₃ : Vec3 × ℝ → ℝ := fun w ↦ L₀ * ‖P w i‖
  have hDint (j : Fin 3) : Integrable (fun w ↦ ‖D w i j‖) μ :=
    ((hD j).integrable (by norm_num)).norm
  let : ENNReal.HolderTriple (ENNReal.ofReal (10 / 3 : ℝ)) 2
      (ENNReal.ofReal (5 / 4 : ℝ)) := by
    convert (show Real.HolderTriple (10 / 3 : ℝ) 2 (5 / 4 : ℝ) by
      constructor <;> norm_num).ennrealOfReal using 1
    norm_num
  have hUDint (j : Fin 3) : Integrable (fun w ↦ ‖u w j‖ * ‖D w i j‖) μ := by
    exact (((hu j).norm.mul (hD j).norm :
      MemLp (fun w ↦ ‖u w j‖ * ‖D w i j‖) (ENNReal.ofReal (5 / 4 : ℝ)) μ).integrable
      (by norm_num))
  have hHint₁ : Integrable H₁ μ :=
    (integrable_finsetSum Finset.univ (fun j _ ↦ hDint j)).const_mul L₁
  have hHint₂ : Integrable H₂ μ :=
    (integrable_finsetSum Finset.univ (fun j _ ↦ hUDint j)).const_mul L₀
  have hHint₃ : Integrable H₃ μ := ((hP.integrable (by norm_num)).norm).const_mul L₀
  have hbound₁ (w : Vec3 × ℝ) :
      ‖∑ j, D w i j * spatialDeriv χ j w.1‖ ≤ H₁ w := by
    calc
      _ ≤ ∑ j, ‖D w i j * spatialDeriv χ j w.1‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖D w i j‖ * L₁ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hgradient w.1 j) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; dsimp [H₁]; ring
  have hbound₂ (w : Vec3 × ℝ) :
      ‖χ w.1 * ∑ j, u w j * D w i j‖ ≤ H₂ w := by
    rw [norm_mul]
    calc
      _ ≤ L₀ * ∑ j, ‖u w j * D w i j‖ :=
        mul_le_mul (hweight w.1) (norm_sum_le _ _) (norm_nonneg _) hL₀
      _ = _ := by simp only [H₂, norm_mul]
  have hbound₃ (w : Vec3 × ℝ) : ‖P w i * χ w.1‖ ≤ H₃ w := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hweight w.1) (norm_nonneg _)).trans_eq (by
      dsimp [H₃]; ring)
  have hpoint : ∀ᵐ t ∂volume.restrict J, ‖g t‖ ≤
      (∫ x in B, H₁ (x, t)) + (∫ x in B, H₂ (x, t)) + (∫ x in B, H₃ (x, t)) := by
    filter_upwards [hformula, hHint₁.prod_left_ae, hHint₂.prod_left_ae,
      hHint₃.prod_left_ae] with t ht ht₁ ht₂ ht₃
    rw [ht]
    have htri := norm_sub_le
      (-(∫ x in B, ∑ j, D (x, t) i j * spatialDeriv χ j x) -
        (∫ x in B, χ x * ∑ j, u (x, t) j * D (x, t) i j))
      (∫ x in B, P (x, t) i * χ x)
    have htri' := norm_sub_le (-(∫ x in B, ∑ j, D (x, t) i j * spatialDeriv χ j x))
      (∫ x in B, χ x * ∑ j, u (x, t) j * D (x, t) i j)
    rw [norm_neg] at htri'
    have hb₁ := norm_integral_le_of_norm_le ht₁
      (Eventually.of_forall fun x ↦ hbound₁ (x, t))
    have hb₂ := norm_integral_le_of_norm_le ht₂
      (Eventually.of_forall fun x ↦ hbound₂ (x, t))
    have hb₃ := norm_integral_le_of_norm_le ht₃
      (Eventually.of_forall fun x ↦ hbound₃ (x, t))
    linarith
  have htotal := integral_mono_of_nonneg (Eventually.of_forall fun t ↦ norm_nonneg _)
    ((hHint₁.integral_prod_right.add hHint₂.integral_prod_right).add
      hHint₃.integral_prod_right) hpoint
  have hadd₁ := integral_add (hHint₁.integral_prod_right.add hHint₂.integral_prod_right)
    hHint₃.integral_prod_right
  have hadd₂ := integral_add hHint₁.integral_prod_right hHint₂.integral_prod_right
  simp only [Pi.add_apply] at htotal hadd₁ hadd₂
  rw [hadd₁, hadd₂,
    ← integral_prod_symm H₁ hHint₁, ← integral_prod_symm H₂ hHint₂,
    ← integral_prod_symm H₃ hHint₃] at htotal
  have hDmass (j : Fin 3) : (∫ w, ‖D w i j‖ ∂μ) ≤
      A ^ (1 / 2 : ℝ) * (μ univ).toReal ^ (1 / 2 : ℝ) := by
    have hh := integral_norm_le_moment_mul_volume
      (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
      (show MemLp (fun w ↦ D w i j) (ENNReal.ofReal 2) μ by simpa using hD j)
    apply hh.trans
    norm_num only [show 1 / (2 : ℝ) = 1 / 2 by norm_num]
    gcongr
    exact hDA j
  have hUDmass (j : Fin 3) : (∫ w, ‖u w j‖ * ‖D w i j‖ ∂μ) ≤
      A ^ (4 / 5 : ℝ) * (μ univ).toReal ^ (1 / 5 : ℝ) := by
    calc
      _ ≤ A ^ (3 / 10 : ℝ) * A ^ (1 / 2 : ℝ) * (μ univ).toReal ^ (1 / 5 : ℝ) := by
        apply (integral_norm_mul_norm_le_three_tenths_half (hu j) (hD j)).trans
        gcongr
        · exact huA j
        · exact hDA j
      _ = _ := by rw [← Real.rpow_add' hA (by norm_num : (3 / 10 : ℝ) + 1 / 2 ≠ 0)]
                  norm_num
  have hPmass : (∫ w, ‖P w i‖ ∂μ) ≤
      A ^ (4 / 5 : ℝ) * (μ univ).toReal ^ (1 / 5 : ℝ) := by
    have hh := integral_norm_le_moment_mul_volume
      (show (5 / 4 : ℝ).HolderConjugate 5 by constructor <;> norm_num) hP
    apply hh.trans
    norm_num only [show 1 / (5 / 4 : ℝ) = 4 / 5 by norm_num]
    gcongr
  have hH₁ : (∫ w, H₁ w ∂μ) ≤
      3 * L₁ * A ^ (1 / 2 : ℝ) * (μ univ).toReal ^ (1 / 2 : ℝ) := by
    dsimp only [H₁]
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ ↦ hDint j)]
    calc
      _ ≤ L₁ * ∑ _j : Fin 3, A ^ (1 / 2 : ℝ) * (μ univ).toReal ^ (1 / 2 : ℝ) := by
        gcongr with j
        exact hDmass j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hH₂ : (∫ w, H₂ w ∂μ) ≤
      3 * L₀ * A ^ (4 / 5 : ℝ) * (μ univ).toReal ^ (1 / 5 : ℝ) := by
    dsimp only [H₂]
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ ↦ hUDint j)]
    calc
      _ ≤ L₀ * ∑ _j : Fin 3, A ^ (4 / 5 : ℝ) * (μ univ).toReal ^ (1 / 5 : ℝ) := by
        gcongr with j
        exact hUDmass j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hH₃ : (∫ w, H₃ w ∂μ) ≤
      L₀ * A ^ (4 / 5 : ℝ) * (μ univ).toReal ^ (1 / 5 : ℝ) := by
    dsimp only [H₃]
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hPmass hL₀).trans_eq (by ring)
  rw [← hμ]
  linarith

/-- The time integral of a weighted component is bounded by its true spatial
weight bound and the finite-volume velocity moment. -/
theorem weighted_mean_time_integral_le
    {B : Set Vec3} {J : Set ℝ} (hB : volume B < ∞) (hJ : volume J < ∞)
    {u : Vec3 × ℝ → Vec3} {χ : Vec3 → ℝ} {L A : ℝ}
    (hL : 0 ≤ L) (hweight : ∀ x, ‖χ x‖ ≤ L) (i : Fin 3)
    (hu : MemLp (fun w ↦ u w i) (ENNReal.ofReal (10 / 3 : ℝ))
      ((volume.restrict B).prod (volume.restrict J)))
    (huA : (∫ w, ‖u w i‖ ^ (10 / 3 : ℝ)
      ∂((volume.restrict B).prod (volume.restrict J))) ≤ A) :
    (∫ t in J, ‖∫ x in B, u (x, t) i * χ x‖) ≤
      L * A ^ (3 / 10 : ℝ) * ((volume B * volume J).toReal) ^ (7 / 10 : ℝ) := by
  let μ := (volume.restrict B).prod (volume.restrict J)
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hB.ne
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr hJ.ne
  have hμ : μ univ = volume B * volume J := by
    rw [show (univ : Set (Vec3 × ℝ)) = univ ×ˢ univ by ext; simp, Measure.prod_prod]
    simp only [Measure.restrict_apply_univ]
  have hint : Integrable (fun w ↦ L * ‖u w i‖) μ :=
    (hu.integrable (by norm_num)).norm.const_mul L
  have henvelope := integral_norm_spatial_integral_le_envelope hint (fun w ↦ by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hweight w.1) (norm_nonneg _)).trans_eq (by ring))
  apply henvelope.trans
  rw [integral_const_mul]
  have hh := integral_norm_le_moment_mul_volume
    (show (10 / 3 : ℝ).HolderConjugate (10 / 7 : ℝ) by constructor <;> norm_num) hu
  calc
    _ ≤ L * ((∫ w, ‖u w i‖ ^ (10 / 3 : ℝ) ∂μ) ^ (3 / 10 : ℝ) *
        (μ univ).toReal ^ (7 / 10 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hL
      simpa only [show 1 / (10 / 3 : ℝ) = 3 / 10 by norm_num,
        show 1 / (10 / 7 : ℝ) = 7 / 10 by norm_num] using hh
    _ ≤ _ := by
      rw [hμ]
      have hp := Real.rpow_le_rpow
        (integral_nonneg fun w ↦ Real.rpow_nonneg (norm_nonneg _) _) huA
        (by norm_num : (0 : ℝ) ≤ 3 / 10)
      exact (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hp (by positivity)) hL).trans_eq (by ring)

/-- The universal spatial volume constant for the Euclidean three-dimensional ball. -/
def meanMotionBallVolume : ℝ := Real.pi * 4 / 3

theorem meanMotionBallVolume_pos : 0 < meanMotionBallVolume := by
  unfold meanMotionBallVolume
  positivity

/-- A radius-independent constant depending only on the two fixed weight bounds. -/
def meanMotionBoundConstant (C : ℝ) : ℝ :=
  C * (meanMotionBallVolume ^ (7 / 10 : ℝ) +
    3 * meanMotionBallVolume ^ (1 / 2 : ℝ) + 4 * meanMotionBallVolume ^ (1 / 5 : ℝ))

theorem meanMotionBoundConstant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ meanMotionBoundConstant C := by
  unfold meanMotionBoundConstant
  have hV := meanMotionBallVolume_pos.le
  positivity

private theorem scaled_volume_power {R : ℝ} (hR : 0 < R) (k a : ℝ) :
    R ^ k * (meanMotionBallVolume * R ^ 5) ^ a =
      meanMotionBallVolume ^ a * R ^ (k + 5 * a) := by
  rw [Real.mul_rpow meanMotionBallVolume_pos.le (by positivity),
    ← Real.rpow_natCast R 5, ← Real.rpow_mul hR.le]
  rw [mul_left_comm, ← Real.rpow_add hR]
  norm_num

private theorem mean_motion_coefficients_le {R A C : ℝ}
    (hR : 0 < R) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    R ^ (-2 : ℝ) *
        (C * R ^ (-3 : ℝ) * A ^ (3 / 10 : ℝ) *
          (meanMotionBallVolume * R ^ 5) ^ (7 / 10 : ℝ)) +
      (3 * (C * R ^ (-4 : ℝ)) * A ^ (1 / 2 : ℝ) *
          (meanMotionBallVolume * R ^ 5) ^ (1 / 2 : ℝ) +
        4 * (C * R ^ (-3 : ℝ)) * A ^ (4 / 5 : ℝ) *
          (meanMotionBallVolume * R ^ 5) ^ (1 / 5 : ℝ)) ≤
    meanMotionBoundConstant C *
      (R ^ (-(3 / 2 : ℝ)) * A ^ (3 / 10 : ℝ) +
        R ^ (-(3 / 2 : ℝ)) * A ^ (1 / 2 : ℝ) +
        R ^ (-2 : ℝ) * A ^ (4 / 5 : ℝ)) := by
  have havg : R ^ (-2 : ℝ) *
      (C * R ^ (-3 : ℝ) * A ^ (3 / 10 : ℝ) *
        (meanMotionBallVolume * R ^ 5) ^ (7 / 10 : ℝ)) =
      C * meanMotionBallVolume ^ (7 / 10 : ℝ) *
        (R ^ (-(3 / 2 : ℝ)) * A ^ (3 / 10 : ℝ)) := by
    calc
      _ = C * A ^ (3 / 10 : ℝ) *
          (R ^ ((-2 : ℝ) + (-3)) * (meanMotionBallVolume * R ^ 5) ^ (7 / 10 : ℝ)) := by
        rw [Real.rpow_add hR]; ring
      _ = _ := by rw [scaled_volume_power hR]; norm_num; ring
  have hdiff : 3 * (C * R ^ (-4 : ℝ)) * A ^ (1 / 2 : ℝ) *
      (meanMotionBallVolume * R ^ 5) ^ (1 / 2 : ℝ) =
      (3 * C * meanMotionBallVolume ^ (1 / 2 : ℝ)) *
        (R ^ (-(3 / 2 : ℝ)) * A ^ (1 / 2 : ℝ)) := by
    calc
      _ = 3 * C * A ^ (1 / 2 : ℝ) *
          (R ^ (-4 : ℝ) * (meanMotionBallVolume * R ^ 5) ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [scaled_volume_power hR]; norm_num; ring
  have hnonlinear : 4 * (C * R ^ (-3 : ℝ)) * A ^ (4 / 5 : ℝ) *
      (meanMotionBallVolume * R ^ 5) ^ (1 / 5 : ℝ) =
      (4 * C * meanMotionBallVolume ^ (1 / 5 : ℝ)) *
        (R ^ (-2 : ℝ) * A ^ (4 / 5 : ℝ)) := by
    calc
      _ = 4 * C * A ^ (4 / 5 : ℝ) *
          (R ^ (-3 : ℝ) * (meanMotionBallVolume * R ^ 5) ^ (1 / 5 : ℝ)) := by ring
      _ = _ := by rw [scaled_volume_power hR]; norm_num; ring
  rw [havg, hdiff, hnonlinear]
  have hcoeff₁ : C * meanMotionBallVolume ^ (7 / 10 : ℝ) ≤ meanMotionBoundConstant C := by
    unfold meanMotionBoundConstant
    nlinarith [Real.rpow_nonneg meanMotionBallVolume_pos.le (1 / 2 : ℝ),
      Real.rpow_nonneg meanMotionBallVolume_pos.le (1 / 5 : ℝ)]
  have hcoeff₂ : 3 * C * meanMotionBallVolume ^ (1 / 2 : ℝ) ≤
      meanMotionBoundConstant C := by
    unfold meanMotionBoundConstant
    nlinarith [Real.rpow_nonneg meanMotionBallVolume_pos.le (7 / 10 : ℝ),
      Real.rpow_nonneg meanMotionBallVolume_pos.le (1 / 5 : ℝ)]
  have hcoeff₃ : 4 * C * meanMotionBallVolume ^ (1 / 5 : ℝ) ≤
      meanMotionBoundConstant C := by
    unfold meanMotionBoundConstant
    nlinarith [Real.rpow_nonneg meanMotionBallVolume_pos.le (7 / 10 : ℝ),
      Real.rpow_nonneg meanMotionBallVolume_pos.le (1 / 2 : ℝ)]
  calc
    _ ≤ meanMotionBoundConstant C * (R ^ (-(3 / 2 : ℝ)) * A ^ (3 / 10 : ℝ)) +
        (meanMotionBoundConstant C * (R ^ (-(3 / 2 : ℝ)) * A ^ (1 / 2 : ℝ)) +
          meanMotionBoundConstant C * (R ^ (-2 : ℝ) * A ^ (4 / 5 : ℝ))) := by
      gcongr
    _ = _ := by ring

private theorem meanMotionCharge_component_moments
    {Q : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {Dp : ParabolicPoint → Vec3}
    (hu : MemLp u (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict Q))
    (hDu : MemLp Du 2 (volume.restrict Q))
    (hDp : MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict Q)) :
    0 ≤ meanMotionCharge Q u Du Dp ∧
      (∀ i, (∫ w in Q, ‖u w i‖ ^ (10 / 3 : ℝ)) ≤ meanMotionCharge Q u Du Dp) ∧
      (∀ i j, (∫ w in Q, ‖Du w i j‖ ^ (2 : ℝ)) ≤ meanMotionCharge Q u Du Dp) ∧
      (∀ i, (∫ w in Q, ‖Dp w i‖ ^ (5 / 4 : ℝ)) ≤ meanMotionCharge Q u Du Dp) := by
  have huInt : Integrable (fun w ↦ ‖u w‖ ^ (10 / 3 : ℝ)) (volume.restrict Q) := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 10 / 3)] using
      hu.integrable_norm_rpow (by norm_num) ENNReal.ofReal_ne_top
  have hDuInt : Integrable (fun w ↦ ‖Du w‖ ^ (2 : ℝ)) (volume.restrict Q) := by
    simpa only [ENNReal.toReal_ofNat] using hDu.integrable_norm_rpow (by norm_num) (by norm_num)
  have hDpInt : Integrable (fun w ↦ ‖Dp w‖ ^ (5 / 4 : ℝ)) (volume.restrict Q) := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 5 / 4)] using
      hDp.integrable_norm_rpow (by norm_num) ENNReal.ofReal_ne_top
  have hint := (hDuInt.add huInt).add hDpInt
  refine ⟨integral_nonneg (fun _ ↦ by positivity), ?_, ?_, ?_⟩
  · intro i
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ by positivity) hint
    exact Eventually.of_forall fun w ↦ by
      have hi := Real.rpow_le_rpow (norm_nonneg _) (norm_le_pi_norm (u w) i)
        (by norm_num : (0 : ℝ) ≤ 10 / 3)
      have hd := Real.rpow_nonneg (norm_nonneg (Du w)) (2 : ℝ)
      have hp := Real.rpow_nonneg (norm_nonneg (Dp w)) (5 / 4 : ℝ)
      dsimp only [Pi.add_apply]
      linarith
  · intro i j
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ by positivity) hint
    exact Eventually.of_forall fun w ↦ by
      have hi := Real.rpow_le_rpow (norm_nonneg _)
        ((norm_le_pi_norm (Du w i) j).trans (norm_le_pi_norm (Du w) i))
        (by norm_num : (0 : ℝ) ≤ 2)
      have hv := Real.rpow_nonneg (norm_nonneg (u w)) (10 / 3 : ℝ)
      have hp := Real.rpow_nonneg (norm_nonneg (Dp w)) (5 / 4 : ℝ)
      dsimp only [Pi.add_apply]
      linarith
  · intro i
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ by positivity) hint
    exact Eventually.of_forall fun w ↦ by
      have hi := Real.rpow_le_rpow (norm_nonneg _) (norm_le_pi_norm (Dp w) i)
        (by norm_num : (0 : ℝ) ≤ 5 / 4)
      have hv := Real.rpow_nonneg (norm_nonneg (u w)) (10 / 3 : ℝ)
      have hd := Real.rpow_nonneg (norm_nonneg (Du w)) (2 : ℝ)
      dsimp only [Pi.add_apply]
      linarith

private theorem backward_box_volume {x : Vec3} {t R : ℝ} (hR : 0 < R) :
    (volume (vec3Ball x R) * volume (Ioo (t - R ^ 2) t)).toReal =
      meanMotionBallVolume * R ^ 5 := by
  rw [ENNReal.toReal_mul, volume_vec3Ball_eq, Real.volume_Ioo]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le,
    ENNReal.toReal_ofReal (by have h := Real.pi_pos; positivity),
    ENNReal.toReal_ofReal (by nlinarith [sq_nonneg R] : 0 ≤ t - (t - R ^ 2))]
  unfold meanMotionBallVolume
  ring

/-- Quantitative control using a genuine supplied weak pressure gradient. The
next theorem constructs that gradient from suitability itself. -/
theorem exists_suitable_weighted_mean_bound_with_pressure_gradient
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (z : ParabolicPoint) {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hbox : localBox Ω I (vec3Ball z.1 R) (Ioo (z.2 - R ^ 2) z.2))
    {Dp : ParabolicPoint → Vec3}
    (hDpLp : MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball z.1 R) (Ioo (z.2 - R ^ 2) z.2))))
    (hDpweak : ∀ᵐ t ∂volume.restrict (Ioo (z.2 - R ^ 2) z.2), ∀ i : Fin 3,
      HasWeakPartialDerivOn (vec3Ball z.1 R) i
        (fun x ↦ p (x, t)) (fun x ↦ Dp (x, t) i))
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ vec3Ball z.1 R)
    (hweight : ∀ x, ‖χ x‖ ≤ C * R ^ (-3 : ℝ))
    (hgradient : ∀ x j, ‖spatialDeriv χ j x‖ ≤ C * R ^ (-4 : ℝ))
    (i : Fin 3) :
    ∃ m : ℝ → ℝ, Continuous m ∧
      AbsolutelyContinuousOnInterval m (z.2 - R ^ 2) z.2 ∧
      MemLp (deriv m) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (Ioo (z.2 - R ^ 2) z.2)) ∧
      (weightedVelocityMean (vec3Ball z.1 R) χ u i =ᵐ[
        volume.restrict (Ioo (z.2 - R ^ 2) z.2)] m) ∧
      ∀ t : ℝ, ‖m t‖ ≤ meanMotionBoundConstant C *
        (R ^ (-(3 / 2 : ℝ)) * (meanMotionCharge
            (spaceTimeSet (vec3Ball z.1 R) (Ioo (z.2 - R ^ 2) z.2)) u Du Dp) ^ (3 / 10 : ℝ) +
          R ^ (-(3 / 2 : ℝ)) * (meanMotionCharge
            (spaceTimeSet (vec3Ball z.1 R) (Ioo (z.2 - R ^ 2) z.2)) u Du Dp) ^ (1 / 2 : ℝ) +
          R ^ (-2 : ℝ) * (meanMotionCharge
            (spaceTimeSet (vec3Ball z.1 R) (Ioo (z.2 - R ^ 2) z.2)) u Du Dp) ^ (4 / 5 : ℝ)) := by
  let B := vec3Ball z.1 R
  let J := Ioo (z.2 - R ^ 2) z.2
  let Q := spaceTimeSet B J
  let A := meanMotionCharge Q u Du Dp
  let g : ℝ → ℝ := fun t ↦ ∫ x in B, weightedMomentumFlux χ u Du p i (x, t)
  have htime : z.2 - R ^ 2 < z.2 := by nlinarith [sq_pos_of_pos hR]
  have hB : volume B < ∞ := volume_vec3Ball_lt_top
  have hJ : volume J < ∞ := by dsimp [J]; rw [Real.volume_Ioo]; finiteness
  have hu : MemLp u (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict Q) :=
    MemLp.of_eval fun j ↦ velocity_component_memLp_tenThirds_on_ballBox_of_data
      hsol.toData hbox hR (Subset.refl _) j
  have hd : MemLp Du 2 (volume.restrict Q) := by
    rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (hsol.toData.aestronglyMeasurable_gradient hbox)]
    simp only [ENNReal.toReal_ofNat]
    apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    exact ((lintegral_mono fun _ ↦ le_add_of_nonneg_left (by positivity)).trans_lt
      (hsol.toData.energy_lintegral_lt_top hbox)).ne
  obtain ⟨hA, huA, hdA, hpA⟩ := meanMotionCharge_component_moments hu hd hDpLp
  have hprod : (volume : Measure ParabolicPoint).restrict Q =
      (volume.restrict B).prod (volume.restrict J) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
    rfl
  have huv (j : Fin 3) : MemLp (fun w : Vec3 × ℝ ↦ u (w.1, w.2) j)
      (ENNReal.ofReal (10 / 3 : ℝ)) ((volume.restrict B).prod (volume.restrict J)) := by
    rw [← hprod]
    exact hu.eval j
  have hdv (j : Fin 3) : MemLp (fun w : Vec3 × ℝ ↦ Du (w.1, w.2) i j) 2
      ((volume.restrict B).prod (volume.restrict J)) := by
    rw [← hprod]
    exact (hd.eval i).eval j
  have hpv : MemLp (fun w : Vec3 × ℝ ↦ Dp (w.1, w.2) i)
      (ENNReal.ofReal (5 / 4 : ℝ)) ((volume.restrict B).prod (volume.restrict J)) := by
    rw [← hprod]
    exact hDpLp.eval i
  have huvA (j : Fin 3) : (∫ w : Vec3 × ℝ, ‖u (w.1, w.2) j‖ ^ (10 / 3 : ℝ)
      ∂((volume.restrict B).prod (volume.restrict J))) ≤ A := by
    rw [← hprod]
    exact huA j
  have hdvA (j : Fin 3) : (∫ w : Vec3 × ℝ, ‖Du (w.1, w.2) i j‖ ^ (2 : ℝ)
      ∂((volume.restrict B).prod (volume.restrict J))) ≤ A := by
    rw [← hprod]
    exact hdA i j
  have hpvA : (∫ w : Vec3 × ℝ, ‖Dp (w.1, w.2) i‖ ^ (5 / 4 : ℝ)
      ∂((volume.restrict B).prod (volume.restrict J))) ≤ A := by
    rw [← hprod]
    exact hpA i
  have hformula := suitable_weighted_flux_eq_gradient hsol hbox hDpweak hχ hχc hχs i
  have hvar := weighted_gradient_acceleration_integral_le hB hJ
    (by positivity : 0 ≤ C * R ^ (-3 : ℝ)) (by positivity : 0 ≤ C * R ^ (-4 : ℝ))
    hA hweight hgradient i huv hdv hpv huvA hdvA hpvA hformula
  have havg := weighted_mean_time_integral_le hB hJ
    (by positivity : 0 ≤ C * R ^ (-3 : ℝ)) hweight i (huv i) (huvA i)
  obtain ⟨m, hmc, hmac, hme, hmd, hinc⟩ :=
    exists_suitable_weighted_mean_absolutelyContinuous hsol hbox htime hχ hχc hχs i
  have hg := suitable_weighted_mean_acceleration_memLp_threeHalves hsol hbox hχ hχc i
  have hderiv : deriv m =ᵐ[volume.restrict J] g := hmd.mono fun _ ht ↦ ht.deriv
  refine ⟨m, hmc, hmac, hg.ae_eq hderiv.symm, hme, ?_⟩
  intro t
  have hprim := norm_primitive_le_average_add_variation htime hmc
    (suitable_weighted_mean_hasWeakDerivOn hsol hbox hχ hχc hχs i).2.1 hinc t
  have hmeanInt : (∫ s in J, ‖m s‖) = ∫ s in J, ‖∫ x in B, u (x, s) i * χ x‖ :=
    integral_congr_ae ((hme.fun_comp norm).symm)
  rw [hmeanInt] at hprim
  have hvolume := backward_box_volume (x := z.1) (t := z.2) hR
  have hinv : (z.2 - (z.2 - R ^ 2))⁻¹ = R ^ (-2 : ℝ) := by
    rw [show z.2 - (z.2 - R ^ 2) = R ^ 2 by ring, Real.rpow_neg hR.le, Real.rpow_two]
  rw [hinv] at hprim
  rw [hvolume] at havg hvar
  apply hprim.trans
  calc
    _ ≤ R ^ (-2 : ℝ) *
        (C * R ^ (-3 : ℝ) * A ^ (3 / 10 : ℝ) *
          (meanMotionBallVolume * R ^ 5) ^ (7 / 10 : ℝ)) +
      (3 * (C * R ^ (-4 : ℝ)) * A ^ (1 / 2 : ℝ) *
          (meanMotionBallVolume * R ^ 5) ^ (1 / 2 : ℝ) +
        4 * (C * R ^ (-3 : ℝ)) * A ^ (4 / 5 : ℝ) *
          (meanMotionBallVolume * R ^ 5) ^ (1 / 5 : ℝ)) := by gcongr
    _ ≤ _ := mean_motion_coefficients_le hR hA hC

/-- The three explicit radius and charge powers in the mean bound. -/
def meanMotionScaleBound (R A : ℝ) : ℝ :=
  R ^ (-(3 / 2 : ℝ)) * A ^ (3 / 10 : ℝ) +
    R ^ (-(3 / 2 : ℝ)) * A ^ (1 / 2 : ℝ) + R ^ (-2 : ℝ) * A ^ (4 / 5 : ℝ)

theorem meanMotionScaleBound_nonneg {R A : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A) :
    0 ≤ meanMotionScaleBound R A := by unfold meanMotionScaleBound; positivity

theorem meanMotionScaleBound_mono {R A B : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A) (hAB : A ≤ B) :
    meanMotionScaleBound R A ≤ meanMotionScaleBound R B := by
  unfold meanMotionScaleBound
  gcongr

private theorem suitable_ballBox_moments
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x : Vec3} {R : ℝ} (hR : 0 < R) (hbox : localBox Ω I (vec3Ball x R) J) :
    MemLp u (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (spaceTimeSet (vec3Ball x R) J)) ∧
      MemLp Du 2 (volume.restrict (spaceTimeSet (vec3Ball x R) J)) := by
  refine ⟨MemLp.of_eval fun j ↦ velocity_component_memLp_tenThirds_on_ballBox_of_data
    hsol.toData hbox hR (Subset.refl _) j, ?_⟩
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (hsol.toData.aestronglyMeasurable_gradient hbox)]
  simp only [ENNReal.toReal_ofNat]
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  exact ((lintegral_mono fun _ ↦ le_add_of_nonneg_left (by positivity)).trans_lt
    (hsol.toData.energy_lintegral_lt_top hbox)).ne

private theorem backward_localBox_of_parabolic_ball
    {Ω : Set Vec3} {I : Set ℝ} {z : ParabolicPoint} {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r ≤ ρ)
    (hdom : Metric.ball z (2 * ρ) ⊆ spaceTimeSet Ω I) :
    localBox Ω I (vec3Ball z.1 r) (Ioo (z.2 - r ^ 2) z.2) := by
  have hbig := CKN.Core.Endgame.localBox_of_parabolic_ball hρ hdom
  have ht : z.2 - r ^ 2 < z.2 := by nlinarith [sq_pos_of_pos hr]
  refine ⟨isOpen_vec3Ball _ _, isCompact_closure_vec3Ball hr,
    (closure_mono (vec3Ball_mono hrρ)).trans hbig.2.2.1, ordConnected_Ioo, ?_, ?_⟩
  · rw [closure_Ioo ht.ne]
    exact isCompact_Icc
  · rw [closure_Ioo ht.ne]
    intro t ht
    apply hbig.2.2.2.2.2
    rw [closure_Ioo (by nlinarith [sq_pos_of_pos hρ] :
      z.2 - ρ ^ 2 ≠ z.2 + ρ ^ 2)]
    constructor <;> nlinarith [ht.1, ht.2, sq_nonneg (ρ - r)]

private theorem meanMotionCharge_integrable
    {Q : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {Dp : ParabolicPoint → Vec3}
    (hu : MemLp u (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict Q))
    (hDu : MemLp Du 2 (volume.restrict Q))
    (hDp : MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict Q)) :
    IntegrableOn (fun w ↦ ‖Du w‖ ^ (2 : ℝ) + ‖u w‖ ^ (10 / 3 : ℝ) +
      ‖Dp w‖ ^ (5 / 4 : ℝ)) Q := by
  have huInt : Integrable (fun w ↦ ‖u w‖ ^ (10 / 3 : ℝ)) (volume.restrict Q) := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 10 / 3)] using
      hu.integrable_norm_rpow (by norm_num) ENNReal.ofReal_ne_top
  have hDuInt : Integrable (fun w ↦ ‖Du w‖ ^ (2 : ℝ)) (volume.restrict Q) := by
    simpa only [ENNReal.toReal_ofNat] using hDu.integrable_norm_rpow (by norm_num) (by norm_num)
  have hDpInt : Integrable (fun w ↦ ‖Dp w‖ ^ (5 / 4 : ℝ)) (volume.restrict Q) := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 5 / 4)] using
      hDp.integrable_norm_rpow (by norm_num) ENNReal.ofReal_ne_top
  exact (hDuInt.add huInt).add hDpInt

/-- Actual suitability constructs a pressure gradient and continuous weighted
means, with a uniform bound by the genuine charge on the larger cylinder.
Only smooth weight bounds and an interior domain condition are required. -/
theorem exists_suitable_weighted_mean_motion_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (z : ParabolicPoint) {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hdom : Metric.ball z (8 * R) ⊆ spaceTimeSet Ω I)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ vec3Ball z.1 R)
    (hweight : ∀ x, ‖χ x‖ ≤ C * R ^ (-3 : ℝ))
    (hgradient : ∀ x j, ‖spatialDeriv χ j x‖ ≤ C * R ^ (-4 : ℝ)) :
    ∃ (Dp : ParabolicPoint → Vec3) (m : ℝ → Vec3), Measurable Dp ∧
      MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ))
        (volume.restrict (spaceTimeSet (vec3Ball z.1 (2 * R))
          (Ioo (z.2 - (2 * R) ^ 2) z.2))) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (z.2 - (2 * R) ^ 2) z.2), ∀ i : Fin 3,
        LocallyIntegrableOn (fun x ↦ Dp (x, t) i) (vec3Ball z.1 (2 * R)) volume ∧
          HasWeakPartialDerivOn (vec3Ball z.1 (2 * R)) i
            (fun x ↦ p (x, t)) (fun x ↦ Dp (x, t) i)) ∧
      Continuous m ∧
      (∀ i, AbsolutelyContinuousOnInterval (fun t ↦ m t i) (z.2 - R ^ 2) z.2) ∧
      (∀ i, MemLp (deriv (fun t ↦ m t i)) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (Ioo (z.2 - R ^ 2) z.2))) ∧
      (∀ i, weightedVelocityMean (vec3Ball z.1 R) χ u i =ᵐ[
        volume.restrict (Ioo (z.2 - R ^ 2) z.2)] (fun t ↦ m t i)) ∧
      (∀ t, ‖m t‖ ≤ meanMotionBoundConstant C * meanMotionScaleBound R
        (meanMotionCharge (spaceTimeSet (vec3Ball z.1 (2 * R))
          (Ioo (z.2 - (2 * R) ^ 2) z.2)) u Du Dp)) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → R ≤ 1 →
        meanMotionCharge (spaceTimeSet (vec3Ball z.1 (2 * R))
          (Ioo (z.2 - (2 * R) ^ 2) z.2)) u Du Dp ≤ ε * R ^ (25 / 23 : ℝ) →
        ∀ t, ‖m t‖ ≤ (3 * meanMotionBoundConstant C) *
          ε ^ (3 / 10 : ℝ) * R ^ (-(27 / 23 : ℝ)) := by
  have h4R : 0 < 4 * R := by positivity
  have hdom' : Metric.ball z (2 * (4 * R)) ⊆ spaceTimeSet Ω I := by
    simpa only [show 2 * (4 * R) = 8 * R by ring] using hdom
  have hbox := backward_localBox_of_parabolic_ball h4R hR (by linarith) hdom'
  have hbox₂ := backward_localBox_of_parabolic_ball h4R
    (by positivity : 0 < 2 * R) (by linarith) hdom'
  obtain ⟨Dp, hDpm, hDpLp, hDpweak⟩ :=
    exists_suitable_pressure_gradient_memLp_fiveFourths hsol z h4R hdom'
  simp only [show 4 * R / 2 = 2 * R by ring,
    show (4 * R) ^ 2 / 4 = (2 * R) ^ 2 by ring] at hDpLp hDpweak
  let Q₁ := spaceTimeSet (vec3Ball z.1 R) (Ioo (z.2 - R ^ 2) z.2)
  let Q₂ := spaceTimeSet (vec3Ball z.1 (2 * R)) (Ioo (z.2 - (2 * R) ^ 2) z.2)
  have htime₁ : Ioo (z.2 - R ^ 2) z.2 ⊆
      Ioo (z.2 - (2 * R) ^ 2) (z.2 + (2 * R) ^ 2) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, sq_pos_of_pos hR]
  have htime₂ : Ioo (z.2 - (2 * R) ^ 2) z.2 ⊆
      Ioo (z.2 - (2 * R) ^ 2) (z.2 + (2 * R) ^ 2) := by
    intro t ht
    exact ⟨ht.1, by nlinarith [ht.2, sq_pos_of_pos hR]⟩
  have hQ₁₂ : Q₁ ⊆ Q₂ := by
    apply prod_mono (vec3Ball_mono (by linarith))
    intro t ht
    exact ⟨by nlinarith [ht.1, sq_nonneg R], ht.2⟩
  have hDp₂ : MemLp Dp (ENNReal.ofReal (5 / 4 : ℝ)) (volume.restrict Q₂) :=
    hDpLp.mono_measure (Measure.restrict_mono_set volume (prod_mono le_rfl htime₂))
  have hDp₁ := hDp₂.mono_measure (Measure.restrict_mono_set volume hQ₁₂)
  have hweak₁ : ∀ᵐ t ∂volume.restrict (Ioo (z.2 - R ^ 2) z.2), ∀ i : Fin 3,
      HasWeakPartialDerivOn (vec3Ball z.1 R) i
        (fun x ↦ p (x, t)) (fun x ↦ Dp (x, t) i) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset htime₁ hDpweak] with t ht i
    exact (ht i).2.restrict (isOpen_vec3Ball _ _) (vec3Ball_mono (by linarith))
  obtain ⟨hu₂, hd₂⟩ := suitable_ballBox_moments hsol (by positivity : 0 < 2 * R) hbox₂
  have hcostInt := meanMotionCharge_integrable hu₂ hd₂ hDp₂
  have hA : 0 ≤ meanMotionCharge Q₁ u Du Dp := integral_nonneg fun _ ↦ by positivity
  have hA₂ : 0 ≤ meanMotionCharge Q₂ u Du Dp := integral_nonneg fun _ ↦ by positivity
  have hcost : meanMotionCharge Q₁ u Du Dp ≤ meanMotionCharge Q₂ u Du Dp :=
    setIntegral_mono_set hcostInt (Eventually.of_forall fun _ ↦ by positivity)
      hQ₁₂.eventuallySubset
  choose m hmc hmac hmlp hme hmb using fun i ↦
    exists_suitable_weighted_mean_bound_with_pressure_gradient hsol z hR hC hbox hDp₁
      hweak₁ hχ hχc hχs hweight hgradient i
  let M : ℝ → Vec3 := fun t i ↦ m i t
  have hbound (t : ℝ) : ‖M t‖ ≤ meanMotionBoundConstant C *
      meanMotionScaleBound R (meanMotionCharge Q₂ u Du Dp) := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (meanMotionBoundConstant_nonneg hC)
      (meanMotionScaleBound_nonneg hR.le hA₂))).2
    intro i
    exact (hmb i t).trans (mul_le_mul_of_nonneg_left
      (meanMotionScaleBound_mono hR.le hA hcost) (meanMotionBoundConstant_nonneg hC))
  refine ⟨Dp, M, hDpm, hDp₂, ae_restrict_of_ae_restrict_of_subset htime₂ hDpweak,
    continuous_pi fun i ↦ hmc i, hmac, hmlp, hme, hbound, ?_⟩
  intro ε hε hεone hRone hsmall t
  have hpowers := mean_motion_endpoint_powers hR hRone hε hεone hA₂ hsmall
  exact ((hbound t).trans (mul_le_mul_of_nonneg_left hpowers
    (meanMotionBoundConstant_nonneg hC))).trans_eq (by ring)

/-- The manuscript's Euclidean magnitude differs from the fixed CKN velocity
norm by at most the radius-independent factor `sqrt 3`. -/
theorem mean_motion_euclidean_bound_of_norm_bound
    {m : ℝ → Vec3} {B : ℝ} (hbound : ∀ t, ‖m t‖ ≤ B) (t : ℝ) :
    vec3EuclideanNorm (m t) ≤ Real.sqrt 3 * B :=
  (vec3EuclideanNorm_le_sqrt_three_mul_norm (m t)).trans
    (mul_le_mul_of_nonneg_left (hbound t) (Real.sqrt_nonneg _))

end FluidSingularSets
