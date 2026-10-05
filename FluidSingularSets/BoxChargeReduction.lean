-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.PressureGradientUniqueness
public import FluidSingularSets.MovingRelativeVelocity
public import FluidSingularSets.AbsolutelyContinuousFrame
public import FluidSingularSets.AcceleratedRegularity
public import FluidSingularSets.SlidingMixedCost
public import FluidSingularSets.MovingScale
public import CKN.Core.Step4.PressureGradientOriginCellInstanceTimeIntegrals

@[expose] public section

open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The squared scale-invariant velocity-only `L²_t L⁶_x` cost on a native
backward cylinder. -/
def velocityOnlyMixedCost (v : ParabolicPoint → Vec3) (t r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal r)⁻¹ * ∫⁻ s in Ioo (t - r ^ 2) t,
    eLpNorm (fun x ↦ vec3EuclideanNorm (v (x, s))) 6
      (volume.restrict (vec3Ball 0 r)) ^ (2 : ℝ)

/-- The remaining universal analytic input for the box reduction. Strict
small velocity cost and a fixed normalized slice-energy bound give a bounded
inner backward cylinder, with a radius uniform in the terminal time. This
internal predicate is an explicit hypothesis; the main target must prove it. -/
def UniformVelocityOnlyInteriorCriterion (q κ : ℝ) : Prop :=
  ∀ B : ℝ, 0 < B → ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
    ∀ (Ω : Set Vec3) (I : Set ℝ) (v : ParabolicPoint → Vec3)
      (Dv : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ),
      IsSuitableWeakSolutionIntegrable Ω I q v Dv p (fun _ ↦ 0) →
      ∀ (t r : ℝ), 0 < r →
        closure (parabolicCylinder 0 t r) ⊆ spaceTimeSet Ω I →
        velocityOnlyMixedCost v t r < ENNReal.ofReal κ →
        essSup (fun s ↦ ∫⁻ x in vec3Ball 0 r, ‖v (x, s)‖ₑ ^ (2 : ℝ))
          (volume.restrict (Ioo (t - r ^ 2) t)) ≤ ENNReal.ofReal (B * r) →
        ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ w ∂volume.restrict (parabolicCylinder 0 t (θ * r)),
          vec3EuclideanNorm (v w) ≤ A

/-- Genuine suitable momentum extends any chosen continuous weighted mean
past an interior terminal time. The new representative agrees at every past
time, including both traces, with the already quantitatively bounded mean. -/
theorem exists_suitable_forward_weighted_mean
    {Ω U : Set Vec3} {I : Set ℝ} {q a τ b : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I U (Ioo a b)) (haτ : a < τ) (hτb : τ < b)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ U)
    {m : ℝ → Vec3} (hm : Continuous m)
    (hmean : (fun t i ↦ weightedVelocityMean U χ u i t)
      =ᵐ[volume.restrict (Ioo a τ)] m) :
    ∃ M : ℝ → Vec3, Continuous M ∧
      (∀ i, AbsolutelyContinuousOnInterval (fun t ↦ M t i) a b) ∧
      ((fun t i ↦ weightedVelocityMean U χ u i t)
        =ᵐ[volume.restrict (Ioo a b)] M) ∧ EqOn M m (Icc a τ) := by
  obtain ⟨M, hMc, hMac, hMmean, _, _, _⟩ :=
    exists_suitable_weighted_vector_mean_primitive hsol hbox (haτ.trans hτb) hχ hχc hχs
  have hsub : Ioo a τ ⊆ Ioo a b := fun _ ht ↦ ⟨ht.1, ht.2.trans hτb⟩
  have hMmean' : (fun t i ↦ weightedVelocityMean U χ u i t)
      =ᵐ[volume.restrict (Ioo a τ)] M :=
    ae_restrict_of_ae_restrict_of_subset hsub hMmean
  have hae : M =ᵐ[volume.restrict (Ioo a τ)] m :=
    hMmean'.symm.trans hmean
  rw [restrict_Ioo_eq_restrict_Icc] at hae
  exact ⟨M, hMc, hMac, hMmean,
    Measure.eqOn_Icc_of_ae_eq volume haτ.ne hae hMc.continuousOn hm.continuousOn⟩

/-- A closed compact past tube genuinely extends slightly forward inside
the original open carrier. The endpoint is part of the past tube, so this
uses a real open neighborhood on its future side. -/
theorem exists_forward_closed_moving_tube
    {X : ℝ → Vec3} (hX : Continuous X) {S : Set Vec3} (hS : IsCompact S)
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {a τ : ℝ} (haτ : a ≤ τ)
    (hpast : acceleratedFrameMapProd X '' (S ×ˢ Icc a τ) ⊆ Ω ×ˢ I) :
    ∃ b : ℝ, τ < b ∧ acceleratedFrameMapProd X '' (S ×ˢ Icc a b) ⊆ Ω ×ˢ I := by
  let W : Set (Vec3 × ℝ) := acceleratedFrameMapProd X ⁻¹' (Ω ×ˢ I)
  have hW : IsOpen W := (hΩ.prod hI).preimage (acceleratedFrameHomeomorph X hX).continuous
  have htrace : S ×ˢ ({τ} : Set ℝ) ⊆ W := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht' : t = τ := mem_singleton_iff.mp ht
    subst t
    exact hpast ⟨(x, τ), ⟨hx, haτ, le_rfl⟩, rfl⟩
  obtain ⟨U, V, _, hV, hSU, hτV, hUV⟩ :=
    generalized_tube_lemma hS isCompact_singleton hW htrace
  have hmem : τ ∈ V := hτV (mem_singleton τ)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hmem)
  refine ⟨τ + δ / 2, by linarith, ?_⟩
  rintro z ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
  by_cases htτ : t ≤ τ
  · exact hpast ⟨(x, t), ⟨hx, ht.1, htτ⟩, rfl⟩
  · apply hUV
    refine ⟨hSU hx, hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ t - τ)]
    linarith [ht.2]

/-- A quantitative past mean bound controls the actual anchored primitive
path. Thus the entire closed native past tube lies strictly inside the
fixed spatial and temporal source buffer, before any forward extension. -/
theorem anchored_mean_closed_past_tube_subset
    {m : ℝ → Vec3} {x₀ : Vec3} {τ R r C : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R / 16) (hC : 0 ≤ C)
    (hm : ∀ t ∈ Icc (τ - R ^ 2) τ, ‖m t‖ ≤ C)
    (hmotion : 2 * Real.sqrt 3 * C * r ^ 2 ≤ R / 2) :
    acceleratedFrameMapProd (fun t ↦ x₀ + ∫ s in τ..t, m s) ''
        (closure (vec3Ball 0 (2 * r)) ×ˢ Icc (τ - 2 * r ^ 2) τ) ⊆
      vec3Ball x₀ (2 * R) ×ˢ Ioo (τ - R ^ 2) (τ + R ^ 2) := by
  have hr2 : 0 < 2 * r := by positivity
  have hrr : 2 * r ^ 2 < R ^ 2 := by nlinarith [sq_nonneg (R - 16 * r)]
  rintro z ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
  have hint : ‖∫ s in τ..t, m s‖ ≤ C * |t - τ| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs ↦ by
      rw [uIoc_of_ge ht.2] at hs
      apply hm s
      exact ⟨by linarith [hs.1, ht.1], hs.2⟩)
  rw [abs_of_nonpos (sub_nonpos.mpr ht.2)] at hint
  have hpath : vec3EuclideanNorm (∫ s in τ..t, m s) ≤ R / 2 := by
    calc
      _ ≤ Real.sqrt 3 * ‖∫ s in τ..t, m s‖ := vec3EuclideanNorm_le_sqrt_three_mul_norm _
      _ ≤ Real.sqrt 3 * (C * (-(t - τ))) :=
        mul_le_mul_of_nonneg_left hint (Real.sqrt_nonneg _)
      _ ≤ 2 * Real.sqrt 3 * C * r ^ 2 := by
        nlinarith [mul_nonneg (Real.sqrt_nonneg 3) hC, ht.1]
      _ ≤ R / 2 := hmotion
  rw [closure_vec3Ball hr2] at hy
  change vec3EuclideanNorm (y - 0) ≤ 2 * r at hy
  rw [sub_zero] at hy
  have heq : x₀ + (∫ s in τ..t, m s) + y - x₀ = (∫ s in τ..t, m s) + y := by abel
  refine ⟨?_, ?_⟩
  · change vec3EuclideanNorm (x₀ + (∫ s in τ..t, m s) + y - x₀) < 2 * R
    rw [heq]
    exact (vec3EuclideanNorm_add_le _ _).trans_lt (by linarith [hpath, hy])
  · change t ∈ Ioo (τ - R ^ 2) (τ + R ^ 2)
    exact ⟨by linarith [ht.1], by nlinarith [ht.2, sq_pos_of_pos hR]⟩

/-- The actual weighted mean and its quantitative past trace construct a
full suitable accelerating frame with a genuine future buffer. The closed
moving tube stays in the fixed outer spatial box, so the same source
Poincaré estimate controls costs on that buffer. -/
theorem exists_suitable_forward_anchored_frame
    {Ω : Set Vec3} {I : Set ℝ} {q τ R r C : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (x₀ : Vec3) (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R / 16) (hC : 0 ≤ C)
    (hbox : localBox Ω I (vec3Ball x₀ R) (Ioo (τ - R ^ 2) (τ + R ^ 2)))
    (hbox₂ : localBox Ω I (vec3Ball x₀ (2 * R)) (Ioo (τ - R ^ 2) (τ + R ^ 2)))
    {m : ℝ → Vec3} (hm : Continuous m)
    (hmean : (fun t i ↦ weightedVelocityMean (vec3Ball x₀ R)
      (normalizedWeightedCutoff x₀ hR) u i t)
      =ᵐ[volume.restrict (Ioo (τ - R ^ 2) τ)] m)
    (hbound : ∀ t ∈ Icc (τ - R ^ 2) τ, ‖m t‖ ≤ C)
    (hmotion : 2 * Real.sqrt 3 * C * r ^ 2 ≤ R / 2) :
    ∃ (M : ℝ → Vec3) (b : ℝ), Continuous M ∧ τ < b ∧ b < τ + R ^ 2 ∧
      EqOn M m (Icc (τ - R ^ 2) τ) ∧
      ((fun t i ↦ weightedVelocityMean (vec3Ball x₀ R)
        (normalizedWeightedCutoff x₀ hR) u i t)
        =ᵐ[volume.restrict (Ioo (τ - R ^ 2) (τ + R ^ 2))] M) ∧
      (acceleratedFrameMapProd (fun t ↦ x₀ + ∫ s in τ..t, M s) ''
        (closure (vec3Ball 0 (2 * r)) ×ˢ Icc (τ - 2 * r ^ 2) b) ⊆
          vec3Ball x₀ (2 * R) ×ˢ Ioo (τ - R ^ 2) (τ + R ^ 2)) ∧
      IsSuitableWeakSolutionIntegrable (vec3Ball 0 (2 * r)) (Ioo (τ - 2 * r ^ 2) b) q
        (acceleratedVelocity (fun t ↦ x₀ + ∫ s in τ..t, M s) M u)
        (acceleratedGradient (fun t ↦ x₀ + ∫ s in τ..t, M s) D)
        (acceleratedPressure (fun t ↦ x₀ + ∫ s in τ..t, M s)
          ((Ioo (τ - 2 * r ^ 2) b).indicator
            (weightedMeanAcceleration (vec3Ball x₀ R)
              (normalizedWeightedCutoff x₀ hR) u D p)) p) (fun _ ↦ 0) := by
  have hRτ : τ - R ^ 2 < τ := by nlinarith [sq_pos_of_pos hR]
  have hτR : τ < τ + R ^ 2 := by nlinarith [sq_pos_of_pos hR]
  obtain ⟨M, hMc, _, hMmean, hMeq⟩ := exists_suitable_forward_weighted_mean hsol hbox
    hRτ hτR (normalizedWeightedCutoff_smooth x₀ hR)
    (normalizedWeightedCutoff_hasCompactSupport x₀ hR)
    (normalizedWeightedCutoff_tsupport_subset x₀ hR) hm hmean
  have hMbound : ∀ t ∈ Icc (τ - R ^ 2) τ, ‖M t‖ ≤ C := by
    intro t ht
    rw [hMeq ht]
    exact hbound t ht
  let X : ℝ → Vec3 := fun t ↦ x₀ + ∫ s in τ..t, M s
  have hX : Continuous X := continuous_const.add
    (intervalIntegral.differentiable_integral_of_continuous hMc).continuous
  have hclosedpast := anchored_mean_closed_past_tube_subset (x₀ := x₀)
    hR hr hrR hC hMbound hmotion
  have hr2 : 0 < 2 * r := by positivity
  obtain ⟨b, hτb, htube⟩ := exists_forward_closed_moving_tube hX
    (isCompact_closure_vec3Ball hr2) (isOpen_vec3Ball _ _) isOpen_Ioo
    (by nlinarith [sq_nonneg r] : τ - 2 * r ^ 2 ≤ τ) hclosedpast
  have hzero : (0 : Vec3) ∈ closure (vec3Ball 0 (2 * r)) := by
    apply subset_closure
    simp only [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero]
    exact hr2
  have hbR : b < τ + R ^ 2 :=
    (htube ⟨(0, b), ⟨hzero, by nlinarith [sq_nonneg r], le_rfl⟩, rfl⟩).2.2
  have htime : Icc (τ - 2 * r ^ 2) b ⊆ Ioo (τ - R ^ 2) (τ + R ^ 2) := by
    have hrr : 2 * r ^ 2 < R ^ 2 := by nlinarith [sq_nonneg (R - 16 * r)]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2.trans_lt hbR⟩
  have hab : τ - 2 * r ^ 2 < b := by nlinarith [sq_nonneg r]
  have hlocal : localBox Ω I (vec3Ball x₀ R) (Ioo (τ - 2 * r ^ 2) b) := by
    refine ⟨hbox.1, hbox.2.1, hbox.2.2.1, ordConnected_Ioo, ?_, ?_⟩
    · rw [closure_Ioo hab.ne]
      exact isCompact_Icc
    · rw [closure_Ioo hab.ne]
      exact htime.trans (subset_closure.trans hbox.2.2.2.2.2)
  have hMlocal : (fun t i ↦ weightedVelocityMean (vec3Ball x₀ R)
      (normalizedWeightedCutoff x₀ hR) u i t)
      =ᵐ[volume.restrict (Ioo (τ - 2 * r ^ 2) b)] M :=
    ae_restrict_of_ae_restrict_of_subset ((Ioo_subset_Icc_self).trans htime) hMmean
  have hdom : vec3Ball x₀ (2 * R) ×ˢ Ioo (τ - R ^ 2) (τ + R ^ 2) ⊆ Ω ×ˢ I :=
    prod_mono (subset_closure.trans hbox₂.2.2.1)
      (subset_closure.trans hbox₂.2.2.2.2.2)
  exact ⟨M, b, hMc, hτb, hbR, hMeq, hMmean, htube,
    suitable_weighted_mean_accelerated_frame_at_time hsol hlocal hab
      (normalizedWeightedCutoff_smooth x₀ hR)
      (normalizedWeightedCutoff_hasCompactSupport x₀ hR)
      (normalizedWeightedCutoff_tsupport_subset x₀ hR) hMc hMlocal
      (isOpen_vec3Ball _ _) (isCompact_closure_vec3Ball hr2) (htube.trans hdom)⟩

/-- A bounded cylinder ending slightly after the original time contains
the original native point in a full open neighborhood. -/
theorem local_ae_velocity_bound_of_forward_bounded_cylinder
    {v : ParabolicPoint → Vec3} {τ h ρ A : ℝ}
    (hh : 0 < h) (hρ : 0 < ρ) (hhρ : h < ρ ^ 2) (hA : 0 ≤ A)
    (hbound : ∀ᵐ w ∂volume.restrict (parabolicCylinder 0 (τ + h) ρ),
      vec3EuclideanNorm (v w) ≤ A) :
    HasLocalAEVelocityBound v ((0 : Vec3), τ) := by
  refine ⟨interior (parabolicCylinder 0 (τ + h) ρ), isOpen_interior, ?_, A, hA,
    ae_restrict_of_ae_restrict_of_subset interior_subset hbound⟩
  rw [interior_parabolicCylinder]
  constructor
  · simpa only [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero] using hρ
  · constructor <;> linarith

/-- The terminal-time step of the box reduction. The actual relative
suitable class supplies one finite slice-energy bound on a forward buffer.
An eventual strict cost bound then permits a future terminal time whose
uniform inner cylinder contains the original point in its interior. -/
theorem suitable_regular_of_eventually_shifted_velocity_cost
    {Ω : Set Vec3} {I : Set ℝ} {q κ a τ b r : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hcriterion : UniformVelocityOnlyInteriorCriterion q κ)
    {X m acc : ℝ → Vec3} (hX : Continuous X) (hm : Continuous m)
    (hrelative : IsSuitableWeakSolutionIntegrable (vec3Ball 0 (2 * r)) (Ioo a b) q
      (acceleratedVelocity X m u) (acceleratedGradient X D)
      (acceleratedPressure X acc p) (fun _ ↦ 0))
    (htube : acceleratedFrameMap X '' spaceTimeSet (vec3Ball 0 (2 * r)) (Ioo a b) ⊆
      spaceTimeSet Ω I)
    (hr : 0 < r) (ha : a < τ - r ^ 2) (hb : τ < b)
    (hcost : ∀ᶠ h : ℝ in 𝓝[>] 0,
      velocityOnlyMixedCost (acceleratedVelocity X m u) (τ + h) r < ENNReal.ofReal κ) :
    CKN.IsRegularPoint Ω I u (acceleratedFrameMap X ((0 : Vec3), τ)) := by
  let J : Set ℝ := Ioo (τ - r ^ 2) ((τ + b) / 2)
  have hJlt : τ - r ^ 2 < (τ + b) / 2 := by nlinarith [sq_nonneg r]
  have hbox : localBox (vec3Ball 0 (2 * r)) (Ioo a b) (vec3Ball 0 r) J := by
    refine ⟨isOpen_vec3Ball _ _, isCompact_closure_vec3Ball hr, ?_,
      ordConnected_Ioo, ?_, ?_⟩
    · intro x hx
      rw [closure_vec3Ball hr] at hx
      exact (mem_vec3Ball).2 (lt_of_le_of_lt hx (by linarith))
    · dsimp [J]
      rw [closure_Ioo hJlt.ne]
      exact isCompact_Icc
    · dsimp [J]
      rw [closure_Ioo hJlt.ne]
      intro t ht
      exact ⟨ha.trans_le ht.1, by linarith [ht.2]⟩
  let E : ℝ → ℝ≥0∞ := fun s ↦ ∫⁻ x in vec3Ball 0 r,
    ‖acceleratedVelocity X m u (x, s)‖ₑ ^ (2 : ℝ)
  let T : ℝ≥0∞ := essSup E (volume.restrict J)
  have hT : T < ⊤ := hrelative.toData.essSup_sliceEnergy_lt_top hbox
  let B : ℝ := (T.toReal + 1) / r
  have hB : 0 < B := div_pos (by positivity) hr
  obtain ⟨θ, hθ, hθhalf, hcrit⟩ := hcriterion B hB
  have hδ : 0 < min ((b - τ) / 2) ((θ * r) ^ 2) :=
    lt_min (by linarith) (sq_pos_of_pos (mul_pos hθ hr))
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0,
      0 < h ∧ h < min ((b - τ) / 2) ((θ * r) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with h hh hhδ
    exact ⟨hh, hhδ⟩
  obtain ⟨h, hcosth, hh, hhδ⟩ := (hcost.and hsmall).exists
  have hhfuture : h < (b - τ) / 2 := hhδ.trans_le (min_le_left _ _)
  have hJsub : Ioo (τ + h - r ^ 2) (τ + h) ⊆ J := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have henergy : essSup E (volume.restrict (Ioo (τ + h - r ^ 2) (τ + h))) ≤
      ENNReal.ofReal (B * r) := by
    have hAE : ∀ᵐ s ∂volume.restrict (Ioo (τ + h - r ^ 2) (τ + h)), E s ≤ T :=
      ae_restrict_of_ae_restrict_of_subset hJsub (ENNReal.ae_le_essSup E)
    apply (essSup_le_of_ae_le T hAE).trans
    have hBr : B * r = T.toReal + 1 := by dsimp [B]; field_simp
    rw [hBr, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_toReal hT.ne]
    exact le_add_right le_rfl
  have hclosed : closure (parabolicCylinder 0 (τ + h) r) ⊆
      spaceTimeSet (vec3Ball 0 (2 * r)) (Ioo a b) := by
    rw [closure_parabolicCylinder hr]
    rintro ⟨x, s⟩ ⟨hx, hs⟩
    exact ⟨(mem_vec3Ball).2 (lt_of_le_of_lt hx (by linarith)),
      by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨A, hA, hbound⟩ := hcrit (vec3Ball 0 (2 * r)) (Ioo a b)
    (acceleratedVelocity X m u) (acceleratedGradient X D) (acceleratedPressure X acc p)
    hrelative (τ + h) r hr hclosed hcosth henergy
  apply suitable_regular_of_accelerated_local_ae_bound hsol hX hm htube
  · exact ⟨(mem_vec3Ball).2 (by simp only [sub_self, vec3EuclideanNorm_zero]; linarith),
      by nlinarith [sq_nonneg r], hb⟩
  · exact local_ae_velocity_bound_of_forward_bounded_cylinder hh (mul_pos hθ hr)
      (hhδ.trans_le (min_le_right _ _)) hA hbound

/-- Actual suitable data and the genuine normalized weighted mean provide
the finite measurable time density needed to preserve a strict endpoint
cost through future shifts. No time-continuity assumption is made. -/
theorem suitable_regular_of_small_moving_velocity_cost
    {Ω : Set Vec3} {I J₀ : Set ℝ} {q κ a τ b r R : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hcriterion : UniformVelocityOnlyInteriorCriterion q κ)
    {X m acc : ℝ → Vec3} (hX : Continuous X) (hm : Continuous m)
    (hrelative : IsSuitableWeakSolutionIntegrable (vec3Ball 0 (2 * r)) (Ioo a b) q
      (acceleratedVelocity X m u) (acceleratedGradient X D)
      (acceleratedPressure X acc p) (fun _ ↦ 0))
    (htube : acceleratedFrameMap X '' spaceTimeSet (vec3Ball 0 (2 * r)) (Ioo a b) ⊆
      spaceTimeSet Ω I)
    (hr : 0 < r) (ha : a ≤ τ - 2 * r ^ 2) (hb : τ < b)
    (x₀ : Vec3) (hR : 0 < R)
    (hbox : localBox Ω I (vec3Ball x₀ (2 * R)) J₀)
    (htime : Ioo (τ - (3 / 2) * r ^ 2) ((τ + b) / 2) ⊆ J₀)
    (hspace : ∀ t ∈ Ioo (τ - (3 / 2) * r ^ 2) ((τ + b) / 2),
      (fun x : Vec3 ↦ X t + x) '' vec3Ball 0 r ⊆ vec3Ball x₀ (2 * R))
    (hmean : ∀ᵐ t ∂volume.restrict (Ioo (τ - (3 / 2) * r ^ 2) ((τ + b) / 2)),
      m t = fun i ↦ weightedVelocityMean (vec3Ball x₀ R)
        (normalizedWeightedCutoff x₀ hR) u i t)
    (hsmall : velocityOnlyMixedCost (acceleratedVelocity X m u) τ r < ENNReal.ofReal κ) :
    CKN.IsRegularPoint Ω I u (acceleratedFrameMap X ((0 : Vec3), τ)) := by
  let J : Set ℝ := Ioo (τ - (3 / 2) * r ^ 2) ((τ + b) / 2)
  have hJlt : τ - (3 / 2) * r ^ 2 < (τ + b) / 2 := by
    nlinarith [sq_pos_of_pos hr]
  have hboxv : localBox (vec3Ball 0 (2 * r)) (Ioo a b) (vec3Ball 0 r) J := by
    refine ⟨isOpen_vec3Ball _ _, isCompact_closure_vec3Ball hr, ?_,
      ordConnected_Ioo, ?_, ?_⟩
    · intro x hx
      rw [closure_vec3Ball hr] at hx
      exact (mem_vec3Ball).2 (lt_of_le_of_lt hx (by linarith))
    · dsimp [J]
      rw [closure_Ioo hJlt.ne]
      exact isCompact_Icc
    · dsimp [J]
      rw [closure_Ioo hJlt.ne]
      intro t ht
      exact ⟨by nlinarith [ht.1, sq_pos_of_pos hr], by linarith [ht.2]⟩
  have hv := hrelative.toData.aestronglyMeasurable_velocity hboxv
  have hvscalar : AEMeasurable (fun w : Vec3 × ℝ ↦
      vec3EuclideanNorm (acceleratedVelocity X m u w))
      (volume.restrict (vec3Ball 0 r ×ˢ J)) := by
    rw [Measure.volume_eq_prod]
    rw [← volume_parabolicPoint_eq_prod]
    exact (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hv).aemeasurable
  have hg : AEMeasurable (fun t ↦ eLpNorm (fun x ↦
      vec3EuclideanNorm (acceleratedVelocity X m u (x, t))) 6
        (volume.restrict (vec3Ball 0 r)) ^ (2 : ℝ)) (volume.restrict J) := by
    have h := CKN.Core.Step4.origin_time_slice_norm_aemeasurable
      (by norm_num : (0 : ℝ) < 6) hvscalar
    simpa only [ENNReal.ofReal_ofNat] using h.pow_const (2 : ℝ)
  have hbound := suitable_moving_relativeVelocity_mixed_bound hsol x₀ hR J J₀
    hbox measurableSet_Ioo htime X m (vec3Ball 0 r) hspace hmean
  have hDfin : (∫⁻ z in spaceTimeSet (vec3Ball x₀ (2 * R)) J₀,
      ‖D z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    (lintegral_mono fun _ ↦ le_add_of_nonneg_left (by positivity)).trans_lt
      (hsol.toData.energy_lintegral_lt_top hbox)
  have hfin : (∫⁻ t in J, eLpNorm (fun x ↦
      vec3EuclideanNorm (acceleratedVelocity X m u (x, t))) 6
        (volume.restrict (vec3Ball 0 r)) ^ (2 : ℝ)) ≠ ⊤ := by
    apply (hbound.trans_lt ?_).ne
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (weightedVelocityEuclideanPoincareConstant_ne_top 64)) hDfin
  have hshift := eventually_movingRelativeVelocityCost_shift_lt X m u hr
    (by nlinarith [sq_pos_of_pos hr] : τ - (3 / 2) * r ^ 2 < τ - r ^ 2)
    (by linarith : τ < (τ + b) / 2) hg hfin hsmall
  have htend : Tendsto (fun h : ℝ ↦ τ + h) (𝓝[>] 0) (𝓝 τ) := by
    have hc : Continuous (fun h : ℝ ↦ τ + h) := continuous_const.add continuous_id
    simpa only [add_zero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  exact suitable_regular_of_eventually_shifted_velocity_cost hsol hcriterion hX hm
    hrelative htube hr (by nlinarith [sq_pos_of_pos hr]) hb (htend.eventually hshift)

set_option maxHeartbeats 1200000 in
/-- Actual small common charge gives regularity, conditional only on the
explicit remaining universal velocity-only analytic criterion. The pressure
gradient is freshly constructed from the solution, reconciled with the fixed
measure by weak uniqueness, and used to construct the genuine accelerating
frame and its full future neighborhood. -/
theorem suitable_regular_of_small_compact_box_charge
    {ι : Type*} {Ω : Set Vec3} {I : Set ℝ} {q κ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hcriterion : UniformVelocityOnlyInteriorCriterion q κ)
    {S : Set ParabolicPoint} (hS : IsCompact S) (hSdom : S ⊆ spaceTimeSet Ω I)
    (P : ι → PressureGradientPatch p) (t : Finset ι) {i : ι} (hi : i ∈ t)
    (z : ParabolicPoint) {R c ε : ℝ} (hR : 0 < R) (hRone : R ≤ 1)
    (hc : 0 < c) (hcone : c ≤ 1 / 16) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hdom : Metric.ball z (8 * R) ⊆ spaceTimeSet Ω I)
    (hBS : Metric.ball z (2 * R) ⊆ S) (hBP : Metric.ball z (2 * R) ⊆ (P i).carrier)
    (hεmotion : (3 * Real.sqrt 3 * meanMotionBoundConstant normalizedWeightedCutoffScaleConstant) *
      c ^ 2 * ε ^ (3 / 10 : ℝ) ≤ 1 / 4)
    (hεcost : weightedVelocityEuclideanPoincareConstant 64 ^ (2 : ℝ) *
      ENNReal.ofReal (ε / c) < ENNReal.ofReal κ)
    (hsmall : (compactBoxMeasure S u D P t (Metric.ball z (2 * R))).toReal ≤
      ε * R ^ (25 / 23 : ℝ)) :
    CKN.IsRegularPoint Ω I u z := by
  let K := meanMotionBoundConstant normalizedWeightedCutoffScaleConstant
  have hK : 0 ≤ K := meanMotionBoundConstant_nonneg
    normalizedWeightedCutoffScaleConstant_pos.le
  obtain ⟨Dp, m, hDpm, hDpLp, hDpweak, hmc, _, _, hmean, _, hmb⟩ :=
    exists_suitable_weighted_mean_motion_bound hsol z hR
      normalizedWeightedCutoffScaleConstant_pos.le hdom
      (normalizedWeightedCutoff_smooth z.1 hR)
      (normalizedWeightedCutoff_hasCompactSupport z.1 hR)
      (normalizedWeightedCutoff_tsupport_subset z.1 hR)
      (normalizedWeightedCutoff_norm_le z.1 hR)
      (normalizedWeightedCutoff_spatialDeriv_norm_le z.1 hR)
  have hcharge : meanMotionCharge (spaceTimeSet (vec3Ball z.1 (2 * R))
      (Ioo (z.2 - (2 * R) ^ 2) z.2)) u D Dp ≤ ε * R ^ (25 / 23 : ℝ) :=
    (meanMotionCharge_backward_ball_le_compactBoxMeasure hsol hS hSdom P t hi hR
      hBS hBP hDpm hDpLp hDpweak).trans hsmall
  let r : ℝ := c * R ^ (25 / 23 : ℝ)
  have hr : 0 < r := moving_radius_pos hR hc
  have hrR : r ≤ R / 16 := moving_radius_le_sixteenth hR.le hRone hc.le hcone (by norm_num)
  let C : ℝ := (3 * K) * ε ^ (3 / 10 : ℝ) * R ^ (-(27 / 23 : ℝ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ s, ‖m s‖ ≤ C := hmb ε hε hεone hRone hcharge
  have hCM : Real.sqrt 3 * C ≤ (3 * Real.sqrt 3 * K) *
      ε ^ (3 / 10 : ℝ) * R ^ (3 * (25 / 23 : ℝ) / 10 - 3 / 2) := by
    norm_num
    dsimp [C]
    ring_nf
    exact le_rfl
  have hdisplace := moving_displacement_le_quarter hR hRone
    (by positivity : 0 ≤ 3 * Real.sqrt 3 * K) hε.le (by norm_num : (25 / 23 : ℝ) ≤ 25 / 23)
    hCM hεmotion
  have hmotion : 2 * Real.sqrt 3 * C * r ^ 2 ≤ R / 2 := by
    change (c * R ^ (25 / 23 : ℝ)) ^ 2 * (Real.sqrt 3 * C) ≤ R / 4 at hdisplace
    dsimp [r]
    nlinarith
  have hdom₂ : Metric.ball z (2 * R) ⊆ spaceTimeSet Ω I :=
    (Metric.ball_subset_ball (by linarith : 2 * R ≤ 8 * R)).trans hdom
  have hdom₄ : Metric.ball z (2 * (2 * R)) ⊆ spaceTimeSet Ω I :=
    (Metric.ball_subset_ball (by linarith : 2 * (2 * R) ≤ 8 * R)).trans hdom
  have hbox := CKN.Core.Endgame.localBox_of_parabolic_ball hR hdom₂
  have hboxbig := CKN.Core.Endgame.localBox_of_parabolic_ball (by positivity : 0 < 2 * R) hdom₄
  have hτ : z.2 - R ^ 2 < z.2 + R ^ 2 := by nlinarith [sq_pos_of_pos hR]
  have hbox₂ : localBox Ω I (vec3Ball z.1 (2 * R))
      (Ioo (z.2 - R ^ 2) (z.2 + R ^ 2)) := by
    refine ⟨hboxbig.1, hboxbig.2.1, hboxbig.2.2.1, ordConnected_Ioo, ?_, ?_⟩
    · rw [closure_Ioo hτ.ne]
      exact isCompact_Icc
    · rw [closure_Ioo hτ.ne]
      intro s hs
      apply hboxbig.2.2.2.2.2
      rw [closure_Ioo (by nlinarith [sq_pos_of_pos hR] :
        z.2 - (2 * R) ^ 2 ≠ z.2 + (2 * R) ^ 2)]
      constructor <;> nlinarith [hs.1, hs.2, sq_nonneg R]
  have hmeanjoint : (fun s j ↦ weightedVelocityMean (vec3Ball z.1 R)
      (normalizedWeightedCutoff z.1 hR) u j s)
      =ᵐ[volume.restrict (Ioo (z.2 - R ^ 2) z.2)] m := by
    filter_upwards [ae_all_iff.mpr hmean] with s hs
    funext j
    exact hs j
  obtain ⟨M, b, hMc, hτb, hbR, _, hMmean, htube, hrelative⟩ :=
    exists_suitable_forward_anchored_frame hsol z.1 hR hr hrR hC hbox hbox₂ hmc
      hmeanjoint (fun s _ ↦ hbound s) hmotion
  let X : ℝ → Vec3 := fun s ↦ z.1 + ∫ σ in z.2..s, M σ
  have hX : Continuous X := continuous_const.add
    (intervalIntegral.differentiable_integral_of_continuous hMc).continuous
  have hrr : 2 * r ^ 2 < R ^ 2 := by nlinarith [sq_nonneg (R - 16 * r)]
  have htubeopen : acceleratedFrameMap X '' spaceTimeSet (vec3Ball 0 (2 * r))
      (Ioo (z.2 - 2 * r ^ 2) b) ⊆ spaceTimeSet Ω I := by
    rintro w ⟨y, hy, rfl⟩
    have hp := htube ⟨y, ⟨subset_closure hy.1, hy.2.1.le, hy.2.2.le⟩, rfl⟩
    exact ⟨hbox₂.2.2.1 (subset_closure hp.1), hbox₂.2.2.2.2.2 (subset_closure hp.2)⟩
  have hspaceall : ∀ s ∈ Ioo (z.2 - 2 * r ^ 2) b,
      (fun y : Vec3 ↦ X s + y) '' vec3Ball 0 r ⊆ vec3Ball z.1 (2 * R) := by
    intro s hs y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (htube ⟨(x, s),
      ⟨subset_closure ((vec3Ball_mono (by linarith : r ≤ 2 * r)) hx), hs.1.le, hs.2.le⟩,
      rfl⟩).1
  have hJpast : Ioo (z.2 - r ^ 2) z.2 ⊆ Ioo (z.2 - 2 * r ^ 2) b := by
    intro s hs
    exact ⟨by nlinarith [hs.1, sq_nonneg r], hs.2.trans hτb⟩
  have hJmean : Ioo (z.2 - 2 * r ^ 2) b ⊆ Ioo (z.2 - R ^ 2) (z.2 + R ^ 2) := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2.trans hbR⟩
  have hMmeanlocal : (fun s j ↦ weightedVelocityMean (vec3Ball z.1 R)
      (normalizedWeightedCutoff z.1 hR) u j s)
      =ᵐ[volume.restrict (Ioo (z.2 - 2 * r ^ 2) b)] M :=
    ae_restrict_of_ae_restrict_of_subset hJmean hMmean
  have hMmean' : ∀ᵐ s ∂volume.restrict (Ioo (z.2 - 2 * r ^ 2) b),
      M s = fun j ↦ weightedVelocityMean (vec3Ball z.1 R)
        (normalizedWeightedCutoff z.1 hR) u j s :=
    hMmeanlocal.symm
  have hboxpast : localBox Ω I (vec3Ball z.1 (2 * R))
      (Ioo (z.2 - (2 * R) ^ 2) z.2) := by
    refine ⟨hboxbig.1, hboxbig.2.1, hboxbig.2.2.1, ordConnected_Ioo, ?_, ?_⟩
    · rw [closure_Ioo (by nlinarith [sq_pos_of_pos hR] : z.2 - (2 * R) ^ 2 ≠ z.2)]
      exact isCompact_Icc
    · rw [closure_Ioo (by nlinarith [sq_pos_of_pos hR] : z.2 - (2 * R) ^ 2 ≠ z.2)]
      intro s hs
      apply hboxbig.2.2.2.2.2
      rw [closure_Ioo (by nlinarith [sq_pos_of_pos hR] :
        z.2 - (2 * R) ^ 2 ≠ z.2 + (2 * R) ^ 2)]
      exact ⟨hs.1, by nlinarith [hs.2, sq_nonneg R]⟩
  have hcost : velocityOnlyMixedCost (acceleratedVelocity X M u) z.2 r < ENNReal.ofReal κ := by
    apply lt_of_le_of_lt (suitable_moving_relativeVelocity_endpoint_cost_le hsol z.1 hR hc
      (Ioo (z.2 - r ^ 2) z.2) (Ioo (z.2 - (2 * R) ^ 2) z.2) hboxpast measurableSet_Ioo
      (by intro s hs; exact ⟨by nlinarith [hs.1, hrr, sq_nonneg R], hs.2⟩)
      X M (fun s hs ↦ hspaceall s (hJpast hs))
      (ae_restrict_of_ae_restrict_of_subset hJpast hMmean') hDpLp hcharge) hεcost
  have hbuf : Ioo (z.2 - (3 / 2) * r ^ 2) ((z.2 + b) / 2) ⊆
      Ioo (z.2 - 2 * r ^ 2) b := by
    intro s hs
    exact ⟨by nlinarith [hs.1, sq_nonneg r], by linarith [hs.2]⟩
  have hreg := suitable_regular_of_small_moving_velocity_cost hsol hcriterion hX hMc
    hrelative htubeopen hr le_rfl hτb z.1 hR hboxbig
    (by
      intro s hs
      have hs' := hJmean (hbuf hs)
      exact ⟨by nlinarith [hs'.1, sq_nonneg R], by nlinarith [hs'.2, sq_nonneg R]⟩)
    (fun s hs ↦ hspaceall s (hbuf hs))
    (ae_restrict_of_ae_restrict_of_subset hbuf hMmean') hcost
  have hz : acceleratedFrameMap X ((0 : Vec3), z.2) = z := by
    simp only [acceleratedFrameMap, X, intervalIntegral.integral_same, add_zero, Prod.eta]
  rwa [hz] at hreg

/-- One genuinely positive radius-independent charge threshold meets both
the mean-displacement and endpoint mixed-cost requirements. -/
theorem exists_box_charge_smallness {κ c : ℝ} (hκ : 0 < κ) (_hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      (3 * Real.sqrt 3 * meanMotionBoundConstant normalizedWeightedCutoffScaleConstant) *
        c ^ 2 * ε ^ (3 / 10 : ℝ) ≤ 1 / 4 ∧
      weightedVelocityEuclideanPoincareConstant 64 ^ (2 : ℝ) *
        ENNReal.ofReal (ε / c) < ENNReal.ofReal κ := by
  let A := (3 * Real.sqrt 3 * meanMotionBoundConstant normalizedWeightedCutoffScaleConstant) * c ^ 2
  have hmot : ContinuousAt (fun ε : ℝ ↦ A * ε ^ (3 / 10 : ℝ)) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 (3 / 10 : ℝ) (.inr (by norm_num)))
  have hmot' : ∀ᶠ ε : ℝ in 𝓝 0, A * ε ^ (3 / 10 : ℝ) < 1 / 4 := by
    have hlim : Tendsto (fun ε : ℝ ↦ A * ε ^ (3 / 10 : ℝ)) (𝓝 0) (𝓝 0) := by
      simpa only [Real.zero_rpow (by norm_num : (3 / 10 : ℝ) ≠ 0), mul_zero] using hmot.tendsto
    exact hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hCP : weightedVelocityEuclideanPoincareConstant 64 ^ (2 : ℝ) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (weightedVelocityEuclideanPoincareConstant_ne_top 64)).ne
  have hcost : Continuous (fun ε : ℝ ↦ weightedVelocityEuclideanPoincareConstant 64 ^ (2 : ℝ) *
      ENNReal.ofReal (ε / c)) :=
    (ENNReal.continuous_const_mul hCP).comp
      (ENNReal.continuous_ofReal.comp (continuous_id.div_const c))
  have hcost' : ∀ᶠ ε : ℝ in 𝓝 0,
      weightedVelocityEuclideanPoincareConstant 64 ^ (2 : ℝ) * ENNReal.ofReal (ε / c) <
        ENNReal.ofReal κ := by
    have hlim : Tendsto (fun ε : ℝ ↦ weightedVelocityEuclideanPoincareConstant 64 ^ (2 : ℝ) *
        ENNReal.ofReal (ε / c)) (𝓝 0) (𝓝 0) := by
      simpa only [zero_div, ENNReal.ofReal_zero, mul_zero] using
        (hcost.continuousAt (x := 0)).tendsto
    exact hlim.eventually (eventually_lt_nhds (ENNReal.ofReal_pos.mpr hκ))
  have hall : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 ∧
      A * ε ^ (3 / 10 : ℝ) < 1 / 4 ∧
      weightedVelocityEuclideanPoincareConstant 64 ^ (2 : ℝ) *
        ENNReal.ofReal (ε / c) < ENNReal.ofReal κ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
      hmot'.filter_mono nhdsWithin_le_nhds, hcost'.filter_mono nhdsWithin_le_nhds]
      with ε hε hεone hεmot hεcost
    exact ⟨hε, hεone, hεmot, hεcost⟩
  obtain ⟨ε, hε, hεone, hεmot, hεcost⟩ := hall.exists
  exact ⟨ε, hε, hεone.le, hεmot.le, hεcost⟩

/-- The uniform reverse charge needed for the box covering argument, with
the remaining universal velocity-only criterion explicitly named. The
threshold is independent of the solution, point, patch and radius. -/
theorem exists_uniform_reverse_compact_box_charge
    {q κ : ℝ} (hκ : 0 < κ) (hcriterion : UniformVelocityOnlyInteriorCriterion q κ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {ι : Type*} {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ},
      IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0) →
      ∀ {S : Set ParabolicPoint}, IsCompact S → S ⊆ spaceTimeSet Ω I →
      ∀ (P : ι → PressureGradientPatch p) (t : Finset ι) {i : ι}, i ∈ t →
      ∀ (z : ParabolicPoint) {R : ℝ}, 0 < R → R ≤ 1 →
      Metric.ball z (8 * R) ⊆ spaceTimeSet Ω I →
      Metric.ball z (2 * R) ⊆ S → Metric.ball z (2 * R) ⊆ (P i).carrier →
      ¬ CKN.IsRegularPoint Ω I u z →
      ENNReal.ofReal (ε * R ^ (25 / 23 : ℝ)) <
        compactBoxMeasure S u D P t (Metric.ball z (2 * R)) := by
  obtain ⟨ε, hε, hεone, hεmotion, hεcost⟩ :=
    exists_box_charge_smallness hκ (by norm_num : (0 : ℝ) < 1 / 32)
  refine ⟨ε, hε, ?_⟩
  intro ι Ω I u D p hsol S hS hSdom P t i hi z R hR hRone hdom hBS hBP hsing
  let := compactBoxMeasure_finite hsol hS hSdom P t
  by_contra hnot
  have hμ : compactBoxMeasure S u D P t (Metric.ball z (2 * R)) ≤
      ENNReal.ofReal (ε * R ^ (25 / 23 : ℝ)) := le_of_not_gt hnot
  have hsmall : (compactBoxMeasure S u D P t (Metric.ball z (2 * R))).toReal ≤
      ε * R ^ (25 / 23 : ℝ) := by
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ ε * R ^ (25 / 23 : ℝ))] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hμ
  exact hsing (suitable_regular_of_small_compact_box_charge hsol hcriterion hS hSdom
    P t hi z hR hRone (by norm_num : (0 : ℝ) < 1 / 32) (by norm_num) hε hεone hdom
    hBS hBP hεmotion hεcost hsmall)

end FluidSingularSets
