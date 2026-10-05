-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import CKN.Setting.SobolevPoincareBallWeak
public import CKN.Setting.SobolevPoincareConstantFinite
public import CKN.Setting.PoincareSobolevL1SliceBasic
public import FluidSingularSets.CompactCharge

/-!
# Sobolev-Poincare around normalized weighted velocity means

The actual weak-gradient Sobolev-Poincare theorem on a ball controls subtraction of
its ordinary average. Normalization and a dimensionless bound for a smooth spatial
weight control the change from this average to the weighted mean. The resulting
constant is independent of the ball centre and radius.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Changing an arbitrary reference constant to a normalized weighted mean costs only
the dimensionless supremum-times-mass bound of the weight. -/
theorem weightedMean_eLpNorm_six_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {v χ : X → ℝ} (a L A : ℝ) (_hA : 0 ≤ A)
    (hχ : Integrable χ μ) (hvχ : Integrable (fun x ↦ v x * χ x) μ)
    (hnormal : ∫ x, χ x ∂μ = 1)
    (hweight : ∀ᵐ x ∂μ, ‖χ x‖ ≤ L)
    (hbudget : ENNReal.ofReal L * μ univ ≤ ENNReal.ofReal A)
    (hv : AEStronglyMeasurable (fun x ↦ v x - a) μ) :
    eLpNorm (fun x ↦ v x - ∫ y, v y * χ y ∂μ) 6 μ ≤
      (1 + ENNReal.ofReal A) * eLpNorm (fun x ↦ v x - a) 6 μ := by
  let m := ∫ y, v y * χ y ∂μ
  have hdiff : m - a = ∫ x, (v x - a) * χ x ∂μ := by
    have heq : (fun x ↦ (v x - a) * χ x) =
        (fun x ↦ v x * χ x) - (fun x ↦ a * χ x) := by
      funext x
      simp only [Pi.sub_apply]
      ring
    rw [heq]
    change m - a = ∫ x, v x * χ x - a * χ x ∂μ
    rw [integral_sub hvχ (hχ.const_mul a), integral_const_mul, hnormal]
    simp [m]
  have hmean : ‖a - m‖ₑ ≤ ENNReal.ofReal L *
      (eLpNorm (fun x ↦ v x - a) 6 μ * μ univ ^ (5 / 6 : ℝ)) := by
    have hneg : a - m = -(m - a) := by ring
    rw [hneg, enorm_neg, hdiff]
    calc
      _ ≤ ∫⁻ x, ‖(v x - a) * χ x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, ENNReal.ofReal L * ‖v x - a‖ₑ ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hweight] with x hx
        rw [enorm_mul, mul_comm]
        gcongr
        simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hx
      _ = ENNReal.ofReal L * ∫⁻ x, ‖v x - a‖ₑ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal L * eLpNorm (fun x ↦ v x - a) 1 μ := by
        rw [eLpNorm_one_eq_lintegral_enorm hv]
      _ ≤ _ := by
        have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
          (by norm_num : (1 : ℝ≥0∞) ≤ 6) hv
        norm_num at h
        gcongr
  have hconst : eLpNorm (fun _ : X ↦ a - m) 6 μ ≤
      ENNReal.ofReal A * eLpNorm (fun x ↦ v x - a) 6 μ := by
    rw [eLpNorm_const' _ (by norm_num : (6 : ℝ≥0∞) ≠ 0) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat]
    calc
      _ ≤ (ENNReal.ofReal L *
          (eLpNorm (fun x ↦ v x - a) 6 μ * μ univ ^ (5 / 6 : ℝ))) *
            μ univ ^ (1 / 6 : ℝ) := by gcongr
      _ = (ENNReal.ofReal L * μ univ) * eLpNorm (fun x ↦ v x - a) 6 μ := by
        have hpow : μ univ ^ (5 / 6 : ℝ) * μ univ ^ (1 / 6 : ℝ) = μ univ := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
          norm_num
        calc
          _ = (ENNReal.ofReal L * eLpNorm (fun x ↦ v x - a) 6 μ) *
              (μ univ ^ (5 / 6 : ℝ) * μ univ ^ (1 / 6 : ℝ)) := by ring
          _ = _ := by rw [hpow]; ring
      _ ≤ _ := by gcongr
  have hsplit : (fun x ↦ v x - m) =
      (fun x ↦ v x - a) + (fun _ : X ↦ a - m) := by
    funext x
    simp only [Pi.add_apply]
    ring
  change eLpNorm (fun x ↦ v x - m) 6 μ ≤ _
  rw [hsplit]
  calc
    _ ≤ eLpNorm (fun x ↦ v x - a) 6 μ + eLpNorm (fun _ : X ↦ a - m) 6 μ :=
      eLpNorm_add_le (by norm_num)
    _ ≤ eLpNorm (fun x ↦ v x - a) 6 μ +
        ENNReal.ofReal A * eLpNorm (fun x ↦ v x - a) 6 μ := by gcongr
    _ = _ := by ring

/-- The genuine scalar weak Sobolev-Poincare estimate remains uniform after replacing
the ordinary average by a normalized weighted mean. -/
theorem h1_weightedMean_sobolevPoincare
    (x₀ : Vec3) {r : ℝ} (hr : 0 < r)
    (v : H1Function (euclideanBall x₀ r)) {χ : Vec3 → ℝ}
    (L A : ℝ) (hA : 0 ≤ A)
    (hχ : IntegrableOn χ (euclideanBall x₀ r))
    (hχmeas : AEStronglyMeasurable χ (volume.restrict (euclideanBall x₀ r)))
    (hnormal : ∫ x in euclideanBall x₀ r, χ x = 1)
    (hweight : ∀ᵐ x ∂volume.restrict (euclideanBall x₀ r), ‖χ x‖ ≤ L)
    (hbudget : ENNReal.ofReal L * volume (euclideanBall x₀ r) ≤ ENNReal.ofReal A) :
    eLpNorm (fun x ↦ v x - ∫ y in euclideanBall x₀ r, v y * χ y) 6
        (volume.restrict (euclideanBall x₀ r)) ≤
      ((1 + ENNReal.ofReal A) * sobolevPoincareL6Constant) *
        eLpNorm v.grad 2 (volume.restrict (euclideanBall x₀ r)) := by
  let μ := volume.restrict (euclideanBall x₀ r)
  let : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using volume_euclideanBall_lt_top x₀ hr⟩
  have hvint : Integrable v μ := v.memL2.integrable (by norm_num)
  have hvχ := hvint.mul_bdd hχmeas hweight
  have hcenter : AEStronglyMeasurable
      (fun x ↦ v x - average μ v.toFun) μ :=
    v.memL2.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hweighted := weightedMean_eLpNorm_six_le (average μ v.toFun) L A hA
    hχ hvχ hnormal hweight (by simpa only [Measure.restrict_apply_univ] using hbudget)
    hcenter
  have hpoincare := sobolevPoincare_L6_ball_weak x₀ hr v
  change eLpNorm (fun x ↦ v x - average μ v.toFun) 6 μ ≤
    sobolevPoincareL6Constant * eLpNorm v.grad 2 μ at hpoincare
  calc
    _ ≤ (1 + ENNReal.ofReal A) *
        eLpNorm (fun x ↦ v x - average μ v.toFun) 6 μ := hweighted
    _ ≤ (1 + ENNReal.ofReal A) *
        (sobolevPoincareL6Constant * eLpNorm v.grad 2 μ) := by gcongr
    _ = _ := by rw [mul_assoc]

/-- A finite uniform constant for the vector weighted-mean estimate. -/
def weightedVelocityPoincareConstant (A : ℝ) : ℝ≥0∞ :=
  3 * ((1 + ENNReal.ofReal A) * sobolevPoincareL6Constant)

/-- The weighted velocity Poincare constant is finite. -/
theorem weightedVelocityPoincareConstant_ne_top (A : ℝ) :
    weightedVelocityPoincareConstant A ≠ ⊤ := by
  unfold weightedVelocityPoincareConstant
  exact ENNReal.mul_ne_top (by norm_num)
    (ENNReal.mul_ne_top (by finiteness) sobolevPoincareL6Constant_ne_top)

private theorem eLpNorm_vec3_six_le_sum {f : Vec3 → Vec3} {μ : Measure Vec3}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 6 μ ≤ ∑ i : Fin 3, eLpNorm (fun x ↦ f x i) 6 μ := by
  have hpoint : ∀ x, ‖f x‖ ≤ ∑ i : Fin 3, ‖f x i‖ := by
    intro x
    rw [Pi.norm_def]
    have hsup : Finset.univ.sup (fun i ↦ ‖f x i‖₊) ≤ ∑ i : Fin 3, ‖f x i‖₊ := by
      apply Finset.sup_le
      intro i hi
      have hnonneg : ∀ j : Fin 3, j ∈ Finset.univ → 0 ≤ ‖f x j‖₊ :=
        fun _ _ ↦ bot_le
      exact Finset.single_le_sum hnonneg hi
    exact_mod_cast hsup
  calc
    _ ≤ eLpNorm (fun x ↦ ∑ i : Fin 3, ‖f x i‖) 6 μ := by
      apply eLpNorm_mono_ae hf
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
        (fun i _ ↦ norm_nonneg (f x i)))]
      exact hpoint x
    _ = eLpNorm (∑ i : Fin 3, fun x ↦ ‖f x i‖) 6 μ := by rfl
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x ↦ ‖f x i‖) 6 μ :=
      eLpNorm_sum_le (p := (6 : ℝ≥0∞)) (s := Finset.univ)
        (f := fun i : Fin 3 ↦ fun x ↦ ‖f x i‖) (by norm_num)
    _ = _ := by
      congr 1
      funext i
      have hfi : AEStronglyMeasurable (fun x ↦ f x i) μ := by
        simpa only [ContinuousLinearMap.proj_apply] using
          (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable hf
      rw [eLpNorm_norm _ hfi]

/-- Vector velocity oscillation around a normalized weighted mean is controlled by its
actual weak gradient on the same ball, with a scale-independent constant. -/
theorem weak_weightedVelocity_sobolevPoincare
    (x₀ : Vec3) {r : ℝ} (hr : 0 < r) (v : Vec3 → Vec3)
    (D : Vec3 → Fin 3 → Vec3) {χ : Vec3 → ℝ} (L A : ℝ) (hA : 0 ≤ A)
    (hv : MemLp v 2 (volume.restrict (euclideanBall x₀ r)))
    (hD : MemLp D 2 (volume.restrict (euclideanBall x₀ r)))
    (hweak : ∀ i : Fin 3, HasWeakGradientOn (euclideanBall x₀ r)
      (fun x ↦ v x i) (fun x ↦ D x i))
    (hχ : IntegrableOn χ (euclideanBall x₀ r))
    (hnormal : ∫ x in euclideanBall x₀ r, χ x = 1)
    (hweight : ∀ᵐ x ∂volume.restrict (euclideanBall x₀ r), ‖χ x‖ ≤ L)
    (hbudget : ENNReal.ofReal L * volume (euclideanBall x₀ r) ≤ ENNReal.ofReal A) :
    eLpNorm (fun x ↦ fun i : Fin 3 ↦
      v x i - ∫ y in euclideanBall x₀ r, v y i * χ y) 6
        (volume.restrict (euclideanBall x₀ r)) ≤
      weightedVelocityPoincareConstant A *
        eLpNorm D 2 (volume.restrict (euclideanBall x₀ r)) := by
  let μ := volume.restrict (euclideanBall x₀ r)
  let w : Vec3 → Vec3 := fun x i ↦ v x i - ∫ y in euclideanBall x₀ r, v y i * χ y
  have hvcomp (i : Fin 3) := (memLp_pi_iff).1 hv i
  have hDcomp (i : Fin 3) := (memLp_pi_iff).1 hD i
  let H : Fin 3 → H1Function (euclideanBall x₀ r) := fun i ↦
    ⟨fun x ↦ v x i, fun x ↦ D x i, hvcomp i,
      (memLp_pi_iff).1 (hDcomp i), hweak i⟩
  have hscalar (i : Fin 3) : eLpNorm (fun x ↦ w x i) 6 μ ≤
      ((1 + ENNReal.ofReal A) * sobolevPoincareL6Constant) * eLpNorm D 2 μ := by
    have h := h1_weightedMean_sobolevPoincare x₀ hr (H i) L A hA
      hχ hχ.aestronglyMeasurable hnormal hweight hbudget
    change eLpNorm (fun x ↦ w x i) 6 μ ≤
      ((1 + ENNReal.ofReal A) * sobolevPoincareL6Constant) *
        eLpNorm (fun x ↦ D x i) 2 μ at h
    have hnorm : eLpNorm (fun x ↦ D x i) 2 μ ≤ eLpNorm D 2 μ := by
      apply eLpNorm_mono_ae (hDcomp i).aestronglyMeasurable
      filter_upwards [] with x
      exact norm_le_pi_norm (D x) i
    exact h.trans (by gcongr)
  have hw : AEStronglyMeasurable w μ := by
    let m : Vec3 := fun i ↦ ∫ y in euclideanBall x₀ r, v y i * χ y
    have heq : w = fun x ↦ v x - m := by rfl
    rw [heq]
    exact hv.aestronglyMeasurable.sub aestronglyMeasurable_const
  calc
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x ↦ w x i) 6 μ := eLpNorm_vec3_six_le_sum hw
    _ ≤ ∑ _i : Fin 3, ((1 + ENNReal.ofReal A) * sobolevPoincareL6Constant) *
        eLpNorm D 2 μ := Finset.sum_le_sum (fun i _ ↦ hscalar i)
    _ = _ := by simp [weightedVelocityPoincareConstant, μ, mul_assoc]

/-- Joint quadratic integrability gives genuine spatial `L²` representatives at almost
every time, for an arbitrary normed target. -/
theorem ae_memLp_two_spatial_slices {E : Type*} [NormedAddCommGroup E]
    (v : ParabolicPoint → E) (B : Set Vec3) (J : Set ℝ)
    (hv : AEStronglyMeasurable v (volume.restrict (B ×ˢ J)))
    (hfinite : (∫⁻ z in B ×ˢ J, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤) :
    ∀ᵐ t ∂volume.restrict J, MemLp (fun x ↦ v (x, t)) 2 (volume.restrict B) := by
  have hprod : AEStronglyMeasurable v
      ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hv
  have hf : AEMeasurable (fun z ↦ ‖v z‖ₑ ^ (2 : ℝ))
      ((volume.restrict B).prod (volume.restrict J)) := hprod.enorm.pow_const _
  have htime : (∫⁻ t in J, ∫⁻ x in B, ‖v (x, t)‖ₑ ^ (2 : ℝ)) ≠ ⊤ := by
    rw [← lintegral_prod_symm _ hf, Measure.prod_restrict,
      ← volume_parabolicPoint_eq_prod]
    exact hfinite.ne
  have hinner := ae_lt_top' hf.lintegral_prod_left' htime
  filter_upwards [hprod.prodMk_right, hinner] with t ht htop
  have hmem := (memLp_ofReal_iff_lintegral_enorm_rpow_lt_top (by norm_num) ht).2 htop
  simpa only [ENNReal.ofReal_ofNat] using hmem

/-- The squared spatial `L⁶` oscillation integrates to at most a universal multiple of
the actual quadratic gradient mass on the product cylinder. -/
theorem integrated_weak_weightedVelocity_sobolevPoincare
    (x₀ : Vec3) {r : ℝ} (hr : 0 < r) (J : Set ℝ)
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    {χ : Vec3 → ℝ} (L A : ℝ) (hA : 0 ≤ A)
    (hD : AEStronglyMeasurable D (volume.restrict (euclideanBall x₀ r ×ˢ J)))
    (hslice : ∀ᵐ t ∂volume.restrict J,
      MemLp (fun x ↦ u (x, t)) 2 (volume.restrict (euclideanBall x₀ r)) ∧
      MemLp (fun x ↦ D (x, t)) 2 (volume.restrict (euclideanBall x₀ r)) ∧
      ∀ i : Fin 3, HasWeakGradientOn (euclideanBall x₀ r)
        (fun x ↦ u (x, t) i) (fun x ↦ D (x, t) i))
    (hχ : IntegrableOn χ (euclideanBall x₀ r))
    (hnormal : ∫ x in euclideanBall x₀ r, χ x = 1)
    (hweight : ∀ᵐ x ∂volume.restrict (euclideanBall x₀ r), ‖χ x‖ ≤ L)
    (hbudget : ENNReal.ofReal L * volume (euclideanBall x₀ r) ≤ ENNReal.ofReal A) :
    (∫⁻ t in J, eLpNorm (fun x ↦ fun i : Fin 3 ↦
      u (x, t) i - ∫ y in euclideanBall x₀ r, u (y, t) i * χ y) 6
        (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ)) ≤
      weightedVelocityPoincareConstant A ^ (2 : ℝ) *
        ∫⁻ z in euclideanBall x₀ r ×ˢ J, ‖D z‖ₑ ^ (2 : ℝ) := by
  have hprod : AEStronglyMeasurable D
      ((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hD
  have hf : AEMeasurable (fun z ↦ ‖D z‖ₑ ^ (2 : ℝ))
      ((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J)) :=
    hprod.enorm.pow_const _
  calc
    _ ≤ ∫⁻ t in J, weightedVelocityPoincareConstant A ^ (2 : ℝ) *
        ∫⁻ x in euclideanBall x₀ r, ‖D (x, t)‖ₑ ^ (2 : ℝ) := by
      apply lintegral_mono_ae
      filter_upwards [hslice] with t ht
      have h := weak_weightedVelocity_sobolevPoincare x₀ hr
        (fun x ↦ u (x, t)) (fun x ↦ D (x, t)) L A hA
        ht.1 ht.2.1 ht.2.2 hχ hnormal hweight hbudget
      have hnorm : eLpNorm (fun x ↦ D (x, t)) 2
          (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ) =
          ∫⁻ x in euclideanBall x₀ r, ‖D (x, t)‖ₑ ^ (2 : ℝ) := by
        have hn := eLpNorm_nnreal_pow_eq_lintegral
          (p := (2 : ℝ≥0)) (by norm_num) ht.2.1.aestronglyMeasurable
        norm_num at hn
        simpa only [ENNReal.rpow_two] using hn
      calc
        _ ≤ (weightedVelocityPoincareConstant A *
            eLpNorm (fun x ↦ D (x, t)) 2
              (volume.restrict (euclideanBall x₀ r))) ^ (2 : ℝ) := by gcongr
        _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hnorm]
    _ = weightedVelocityPoincareConstant A ^ (2 : ℝ) *
        ∫⁻ t in J, ∫⁻ x in euclideanBall x₀ r, ‖D (x, t)‖ₑ ^ (2 : ℝ) :=
      lintegral_const_mul' _ _ (by
        exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
          (weightedVelocityPoincareConstant_ne_top A)).ne)
    _ = _ := by
      congr 1
      rw [← lintegral_prod_symm _ hf, Measure.prod_restrict,
        ← volume_parabolicPoint_eq_prod]
      rfl

/-- The actual suitable solution supplies all slice and integrability hypotheses of the
weighted velocity estimate on every admissible ball-time box. -/
theorem suitable_integrated_weightedVelocity_sobolevPoincare
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (x₀ : Vec3) {r : ℝ} (hr : 0 < r) (J : Set ℝ)
    (hbox : localBox Ω I (euclideanBall x₀ r) J)
    {χ : Vec3 → ℝ} (L A : ℝ) (hA : 0 ≤ A)
    (hχ : IntegrableOn χ (euclideanBall x₀ r))
    (hnormal : ∫ x in euclideanBall x₀ r, χ x = 1)
    (hweight : ∀ᵐ x ∂volume.restrict (euclideanBall x₀ r), ‖χ x‖ ≤ L)
    (hbudget : ENNReal.ofReal L * volume (euclideanBall x₀ r) ≤ ENNReal.ofReal A) :
    (∫⁻ t in J, eLpNorm (fun x ↦ fun i : Fin 3 ↦
      u (x, t) i - ∫ y in euclideanBall x₀ r, u (y, t) i * χ y) 6
        (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ)) ≤
      weightedVelocityPoincareConstant A ^ (2 : ℝ) *
        ∫⁻ z in euclideanBall x₀ r ×ˢ J, ‖D z‖ₑ ^ (2 : ℝ) := by
  obtain ⟨hu, hD, -, -, -, henergy, -, -, hweak⟩ :=
    hsol.2.2.2.2.2.1 (euclideanBall x₀ r) J hbox
  have huenergy : (∫⁻ z in euclideanBall x₀ r ×ˢ J, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    (lintegral_mono fun _ ↦ le_add_right le_rfl).trans_lt henergy
  have hDenergy : (∫⁻ z in euclideanBall x₀ r ×ˢ J, ‖D z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    (lintegral_mono fun _ ↦ le_add_left le_rfl).trans_lt henergy
  have hume := ae_memLp_two_spatial_slices u (euclideanBall x₀ r) J hu huenergy
  have hDme := ae_memLp_two_spatial_slices D (euclideanBall x₀ r) J hD hDenergy
  have hweakall : ∀ᵐ t ∂volume.restrict J, ∀ i : Fin 3,
      HasWeakGradientOn (euclideanBall x₀ r)
        (fun x ↦ u (x, t) i) (fun x ↦ D (x, t) i) := by
    rw [ae_all_iff]
    exact hweak
  apply integrated_weak_weightedVelocity_sobolevPoincare
    x₀ hr J u D L A hA hD _ hχ hnormal hweight hbudget
  filter_upwards [hume, hDme, hweakall] with t hut hDt hweakt
  exact ⟨hut, hDt, hweakt⟩

/-- The Euclidean spatial norm changes the native supremum norm estimate by at most three. -/
theorem eLpNorm_vec3EuclideanNorm_le_three
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {v : X → Vec3}
    (hv : AEStronglyMeasurable v μ) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ vec3EuclideanNorm (v x)) p μ ≤ 3 * eLpNorm v p μ := by
  have hnorm : ∀ x, ‖vec3EuclideanNorm (v x)‖₊ ≤ (3 : ℝ≥0) * ‖v x‖₊ := by
    intro x
    have hsqrt : Real.sqrt 3 ≤ 3 := by
      apply Real.sqrt_le_iff.mpr
      norm_num
    have hreal : ‖vec3EuclideanNorm (v x)‖ ≤ 3 * ‖v x‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      exact (native_euclidean_norm_le_sqrt_three_norm _).trans
        (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _))
    exact_mod_cast hreal
  have h := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (CKN.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hv)
    (Eventually.of_forall hnorm) p
  simpa only [ENNReal.smul_def, ENNReal.coe_ofNat, smul_eq_mul] using h

/-- A finite uniform constant when velocity length is measured by the Euclidean norm. -/
def weightedVelocityEuclideanPoincareConstant (A : ℝ) : ℝ≥0∞ :=
  3 * weightedVelocityPoincareConstant A

/-- The Euclidean weighted velocity constant is finite. -/
theorem weightedVelocityEuclideanPoincareConstant_ne_top (A : ℝ) :
    weightedVelocityEuclideanPoincareConstant A ≠ ⊤ :=
  ENNReal.mul_ne_top (by norm_num) (weightedVelocityPoincareConstant_ne_top A)

/-- The actual suitable solution satisfies the paper's squared mixed `L²_t L⁶_x`
bound around the smooth normalized weighted mean, with Euclidean velocity length. -/
theorem suitable_integrated_weightedVelocity_euclidean_sobolevPoincare
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (x₀ : Vec3) {r : ℝ} (hr : 0 < r) (J : Set ℝ)
    (hbox : localBox Ω I (euclideanBall x₀ r) J)
    {χ : Vec3 → ℝ} (L A : ℝ) (hA : 0 ≤ A)
    (hχ : IntegrableOn χ (euclideanBall x₀ r))
    (hnormal : ∫ x in euclideanBall x₀ r, χ x = 1)
    (hweight : ∀ᵐ x ∂volume.restrict (euclideanBall x₀ r), ‖χ x‖ ≤ L)
    (hbudget : ENNReal.ofReal L * volume (euclideanBall x₀ r) ≤ ENNReal.ofReal A) :
    (∫⁻ t in J, eLpNorm (fun x ↦ vec3EuclideanNorm (fun i : Fin 3 ↦
      u (x, t) i - ∫ y in euclideanBall x₀ r, u (y, t) i * χ y)) 6
        (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ)) ≤
      weightedVelocityEuclideanPoincareConstant A ^ (2 : ℝ) *
        ∫⁻ z in euclideanBall x₀ r ×ˢ J, ‖D z‖ₑ ^ (2 : ℝ) := by
  have hnative := suitable_integrated_weightedVelocity_sobolevPoincare
    hsol x₀ hr J hbox L A hA hχ hnormal hweight hbudget
  obtain ⟨hu, -, -, -, -, henergy, -, -, -⟩ :=
    hsol.2.2.2.2.2.1 (euclideanBall x₀ r) J hbox
  have huenergy : (∫⁻ z in euclideanBall x₀ r ×ˢ J, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    (lintegral_mono fun _ ↦ le_add_right le_rfl).trans_lt henergy
  have hume := ae_memLp_two_spatial_slices u (euclideanBall x₀ r) J hu huenergy
  calc
    _ ≤ ∫⁻ t in J, (3 : ℝ≥0∞) ^ (2 : ℝ) *
        eLpNorm (fun x ↦ fun i : Fin 3 ↦
          u (x, t) i - ∫ y in euclideanBall x₀ r, u (y, t) i * χ y) 6
            (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ) := by
      apply lintegral_mono_ae
      filter_upwards [hume] with t ht
      have hosc : AEStronglyMeasurable (fun x ↦ fun i : Fin 3 ↦
          u (x, t) i - ∫ y in euclideanBall x₀ r, u (y, t) i * χ y)
          (volume.restrict (euclideanBall x₀ r)) := by
        change AEStronglyMeasurable (fun x ↦ u (x, t) -
          fun i ↦ ∫ y in euclideanBall x₀ r, u (y, t) i * χ y) _
        exact ht.aestronglyMeasurable.sub aestronglyMeasurable_const
      have h := eLpNorm_vec3EuclideanNorm_le_three hosc 6
      calc
        _ ≤ (3 * eLpNorm (fun x ↦ fun i : Fin 3 ↦
            u (x, t) i - ∫ y in euclideanBall x₀ r, u (y, t) i * χ y) 6
              (volume.restrict (euclideanBall x₀ r))) ^ (2 : ℝ) := by gcongr
        _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ = (3 : ℝ≥0∞) ^ (2 : ℝ) *
        ∫⁻ t in J, eLpNorm (fun x ↦ fun i : Fin 3 ↦
          u (x, t) i - ∫ y in euclideanBall x₀ r, u (y, t) i * χ y) 6
            (volume.restrict (euclideanBall x₀ r)) ^ (2 : ℝ) :=
      lintegral_const_mul' _ _ (by norm_num)
    _ ≤ (3 : ℝ≥0∞) ^ (2 : ℝ) * (weightedVelocityPoincareConstant A ^ (2 : ℝ) *
        ∫⁻ z in euclideanBall x₀ r ×ˢ J, ‖D z‖ₑ ^ (2 : ℝ)) := by gcongr
    _ = _ := by
      rw [weightedVelocityEuclideanPoincareConstant,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), mul_assoc]

/-- Replacing the literal weighted means by their continuous or absolutely continuous
time representatives preserves the mixed oscillation exactly. -/
theorem integrated_weightedVelocity_euclidean_congr_mean
    (B : Set Vec3) (J : Set ℝ) (u : ParabolicPoint → Vec3) (χ : Vec3 → ℝ)
    (m : ℝ → Vec3)
    (hmean : ∀ᵐ t ∂volume.restrict J,
      ∀ i : Fin 3, m t i = ∫ y in B, u (y, t) i * χ y) :
    (∫⁻ t in J, eLpNorm (fun x ↦ vec3EuclideanNorm (u (x, t) - m t)) 6
      (volume.restrict B) ^ (2 : ℝ)) =
    ∫⁻ t in J, eLpNorm (fun x ↦ vec3EuclideanNorm (fun i : Fin 3 ↦
      u (x, t) i - ∫ y in B, u (y, t) i * χ y)) 6 (volume.restrict B) ^ (2 : ℝ) := by
  apply lintegral_congr_ae
  filter_upwards [hmean] with t ht
  congr 1
  congr 1
  funext x
  congr 1
  funext i
  exact congrArg (fun a ↦ u (x, t) i - a) (ht i)

end FluidSingularSets
