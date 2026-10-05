-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.AcceleratedPressureLimit
public import FluidSingularSets.AcceleratedTubeLimit
public import FluidSingularSets.SmoothAcceleratedSuitability
public import FluidSingularSets.MeanSmoothApprox
public import FluidSingularSets.LocalEnergyLimit

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Actual smooth frame data with the genuine time convergence preserve
suitability in the limit. A compact closed limit tube supplies a common
interior buffer and discards finitely many inadmissible approximants. All
joint strong field limits are derived from the actual source solution. -/
theorem suitable_accelerated_frame_of_smooth_sequence
    {Ω B : Set Vec3} {I : Set ℝ} {q t₀ t₁ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hB : IsOpen B) (hBc : IsCompact (closure B)) (ht : t₀ < t₁)
    {X m acc : ℝ → Vec3} (hX : Continuous X) (hm : Continuous m)
    (ha : MemLp acc (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    {Xs ms accs : ℕ → ℝ → Vec3}
    (hsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (accs n) ∧ ContDiff ℝ (⊤ : ℕ∞) (ms n) ∧
      ContDiff ℝ (⊤ : ℕ∞) (Xs n) ∧ tsupport (accs n) ⊆ meanApproxTimeSet t₀ t₁ ∧
      MemLp (accs n) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      (∀ t, HasDerivAt (ms n) (accs n t) t) ∧
      (∀ t, HasDerivAt (Xs n) (ms n t) t))
    (hXconv : TendstoUniformlyOn Xs X atTop (Icc t₀ t₁))
    (hmconv : TendstoUniformlyOn ms m atTop (Icc t₀ t₁))
    (haconv : Tendsto (fun n ↦ eLpNorm (accs n - acc) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
      atTop (𝓝 0))
    (htube : acceleratedFrameMapProd X '' (closure B ×ˢ Icc t₀ t₁) ⊆ Ω ×ˢ I) :
    IsSuitableWeakSolutionIntegrable B (Ioo t₀ t₁) q (acceleratedVelocity X m u)
      (acceleratedGradient X Du) (acceleratedPressure X acc p) (fun _ ↦ 0) := by
  let C : Set (Vec3 × ℝ) := closure B ×ˢ Icc t₀ t₁
  have hC : IsCompact C := hBc.prod isCompact_Icc
  obtain ⟨K, hK, hKdom, hXK, hXsK⟩ := exists_compact_common_moving_tube hX hXconv hC
    (hsol.1.prod hsol.2.1) (fun _ hz ↦ hz.2) htube
  have hKraw : IsCompact (show Set ParabolicPoint from K) := by
    have h := parabolicHomeomorph.isCompact_preimage.mpr hK
    rwa [parabolicHomeomorph_preimage] at h
  have hdom : (show Set ParabolicPoint from K) ⊆ spaceTimeSet Ω I := hKdom
  obtain ⟨N, hN⟩ := eventually_atTop.mp hXsK
  let Y : ℕ → ℝ → Vec3 := fun n ↦ Xs (n + N)
  let M : ℕ → ℝ → Vec3 := fun n ↦ ms (n + N)
  let A : ℕ → ℝ → Vec3 := fun n ↦ accs (n + N)
  have hYconv : TendstoUniformlyOn Y X atTop (Icc t₀ t₁) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact (tendsto_add_atTop_nat N).eventually
      (Metric.tendstoUniformlyOn_iff.mp hXconv ε hε)
  have hMconv : TendstoUniformlyOn M m atTop (Icc t₀ t₁) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact (tendsto_add_atTop_nat N).eventually
      (Metric.tendstoUniformlyOn_iff.mp hmconv ε hε)
  have hAconv : Tendsto (fun n ↦ eLpNorm (A n - acc) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
      atTop (𝓝 0) := haconv.comp (tendsto_add_atTop_nat N)
  have hYimage (n : ℕ) : acceleratedFrameMapProd (Y n) '' C ⊆ K :=
    hN (n + N) (Nat.le_add_left N n)
  have hYtube (n : ℕ) : acceleratedFrameMap (Y n) '' spaceTimeSet B (Ioo t₀ t₁) ⊆
      spaceTimeSet Ω I := by
    rintro z ⟨w, hw, rfl⟩
    exact hKdom (hYimage n ⟨w, ⟨subset_closure hw.1, Ioo_subset_Icc_self hw.2⟩, rfl⟩)
  have hXtube : acceleratedFrameMap X '' spaceTimeSet B (Ioo t₀ t₁) ⊆
      spaceTimeSet Ω I := by
    rintro z ⟨w, hw, rfl⟩
    exact htube ⟨w, ⟨subset_closure hw.1, Ioo_subset_Icc_self hw.2⟩, rfl⟩
  have hforce (P : ℝ → Vec3) : acceleratedForce P (fun _ ↦ (0 : Vec3)) =
      (fun _ : ParabolicPoint ↦ 0) := rfl
  have hdata : IsSuitableWeakSolutionData B (Ioo t₀ t₁) q (acceleratedVelocity X m u)
      (acceleratedGradient X Du) (acceleratedPressure X acc p) (fun _ ↦ 0) := by
    simpa only [hforce] using suitable_accelerated_data_of_acceleration_memLp
      hsol hX hm (ha.mono_measure Measure.restrict_le_self) hB isOpen_Ioo
      ordConnected_Ioo hXtube
  have hsols (n : ℕ) : IsSuitableWeakSolutionIntegrable B (Ioo t₀ t₁) q
      (acceleratedVelocity (Y n) (M n) u) (acceleratedGradient (Y n) Du)
      (acceleratedPressure (Y n) (A n) p) (fun _ ↦ 0) := by
    have hs := hsmooth (n + N)
    simpa only [hforce] using suitable_smooth_accelerated_frame hsol hs.2.2.1
      hs.2.1 hs.1 hs.2.2.2.2.2.2 hs.2.2.2.2.2.1 hB isOpen_Ioo ordConnected_Ioo (hYtube n)
  apply suitable_of_strongLp hdata hsols
  intro T hT hTsub
  have hTC : (show Set (Vec3 × ℝ) from T) ⊆ C := fun _ hz ↦
    ⟨subset_closure (hTsub hz).1, Ioo_subset_Icc_self (hTsub hz).2⟩
  have hTtime : ∀ z ∈ T, z.2 ∈ Icc t₀ t₁ := fun _ hz ↦ (hTC hz).2
  have hYimages : ∀ᶠ n in atTop, acceleratedFrameMap (Y n) '' T ⊆
      (show Set ParabolicPoint from K) := Eventually.of_forall fun n ↦ by
    rintro z ⟨w, hw, rfl⟩
    exact hYimage n ⟨w, hTC hw, rfl⟩
  have hXimage : acceleratedFrameMap X '' T ⊆ (show Set ParabolicPoint from K) := by
    rintro z ⟨w, hw, rfl⟩
    exact hXK ⟨w, hTC hw, rfl⟩
  obtain ⟨_, hu, hD, hp, _⟩ := suitable_accelerated_fields_strongLp hsol
    (fun n ↦ (hsmooth (n + N)).2.2.1.continuous) hX
    (fun n ↦ (hsmooth (n + N)).2.1.continuous) hm ht.le hYconv hMconv ha
    (fun n ↦ (hsmooth (n + N)).2.2.2.2.1) hAconv hT hKraw hdom hTtime hYimages hXimage
  refine ⟨hu, hD, hp, ?_⟩
  simp

/-- The actual continuous weighted mean of an unforced suitable solution
defines a suitable absolutely continuous accelerating frame on its genuine
interior tube. Smooth frame data are constructed from actual momentum; the
acceleration is the zero extension of the actual weighted momentum flux,
which agrees with that flux throughout the interior time interval. -/
theorem suitable_weighted_mean_accelerated_frame
    {Ω U B : Set Vec3} {I : Set ℝ} {q t₀ t₁ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I U (Ioo t₀ t₁)) (ht : t₀ < t₁)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ U)
    {m : ℝ → Vec3} (hm : Continuous m)
    (hmean : (fun t i ↦ weightedVelocityMean U χ u i t)
      =ᵐ[volume.restrict (Ioo t₀ t₁)] m)
    (hB : IsOpen B) (hBc : IsCompact (closure B))
    {c : Vec3} (htube : acceleratedFrameMapProd (fun t ↦ c + ∫ τ in t₀..t, m τ) ''
      (closure B ×ˢ Icc t₀ t₁) ⊆ Ω ×ˢ I) :
    IsSuitableWeakSolutionIntegrable B (Ioo t₀ t₁) q
      (acceleratedVelocity (fun t ↦ c + ∫ τ in t₀..t, m τ) m u)
      (acceleratedGradient (fun t ↦ c + ∫ τ in t₀..t, m τ) Du)
      (acceleratedPressure (fun t ↦ c + ∫ τ in t₀..t, m τ)
        ((Ioo t₀ t₁).indicator (weightedMeanAcceleration U χ u Du p)) p)
      (fun _ ↦ 0) := by
  obtain ⟨accs, ms, Xs, hsmooth, haconv, hmconv, hXconv, _⟩ :=
    exists_suitable_weighted_mean_smooth_sequence hsol hbox ht hχ hχc hχs hm hmean
  let Ys : ℕ → ℝ → Vec3 := fun n t ↦ c + Xs n t
  have hsmooth' : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (accs n) ∧
      ContDiff ℝ (⊤ : ℕ∞) (ms n) ∧ ContDiff ℝ (⊤ : ℕ∞) (Ys n) ∧
      tsupport (accs n) ⊆ meanApproxTimeSet t₀ t₁ ∧
      MemLp (accs n) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      (∀ t, HasDerivAt (ms n) (accs n t) t) ∧
      (∀ t, HasDerivAt (Ys n) (ms n t) t) := by
    intro n
    have hn := hsmooth n
    exact ⟨hn.1, hn.2.1, contDiff_const.add hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1,
      hn.2.2.2.2.2.1, (fun t ↦ (hn.2.2.2.2.2.2 t).const_add c)⟩
  have hYconv : TendstoUniformlyOn Ys (fun t ↦ c + ∫ τ in t₀..t, m τ) atTop
      (Icc t₀ t₁) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hXconv ε hε] with n hn
    intro t ht
    simpa only [Ys, dist_add_left] using hn t ht
  have ha : MemLp ((Ioo t₀ t₁).indicator (weightedMeanAcceleration U χ u Du p))
      (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioo).mpr
      (suitable_weightedMeanAcceleration_memLp_threeHalves hsol hbox hχ hχc)
  have haconv' : Tendsto (fun n ↦ eLpNorm
      (accs n - (Ioo t₀ t₁).indicator (weightedMeanAcceleration U χ u Du p))
      (ENNReal.ofReal (3 / 2 : ℝ)) volume) atTop (𝓝 0) := by
    simpa only [eLpNorm_sub_comm] using haconv
  exact suitable_accelerated_frame_of_smooth_sequence hsol hB hBc ht
    (continuous_const.add (intervalIntegral.differentiable_integral_of_continuous hm).continuous)
    hm ha hsmooth' hYconv hmconv haconv' htube

/-- The same genuine mean frame can be anchored at any specified time,
including an interior terminal time, and at any spatial point. Both sides of
that time remain in the suitable-solution domain when its closed tube is
contained in the original carrier. -/
theorem suitable_weighted_mean_accelerated_frame_at_time
    {Ω U B : Set Vec3} {I : Set ℝ} {q t₀ t₁ s : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I U (Ioo t₀ t₁)) (ht : t₀ < t₁)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ U)
    {m : ℝ → Vec3} (hm : Continuous m)
    (hmean : (fun t i ↦ weightedVelocityMean U χ u i t)
      =ᵐ[volume.restrict (Ioo t₀ t₁)] m)
    (hB : IsOpen B) (hBc : IsCompact (closure B))
    {x₀ : Vec3} (htube : acceleratedFrameMapProd (fun t ↦ x₀ + ∫ τ in s..t, m τ) ''
      (closure B ×ˢ Icc t₀ t₁) ⊆ Ω ×ˢ I) :
    IsSuitableWeakSolutionIntegrable B (Ioo t₀ t₁) q
      (acceleratedVelocity (fun t ↦ x₀ + ∫ τ in s..t, m τ) m u)
      (acceleratedGradient (fun t ↦ x₀ + ∫ τ in s..t, m τ) Du)
      (acceleratedPressure (fun t ↦ x₀ + ∫ τ in s..t, m τ)
        ((Ioo t₀ t₁).indicator (weightedMeanAcceleration U χ u Du p)) p)
      (fun _ ↦ 0) := by
  have heq : (fun t ↦ (x₀ - ∫ τ in t₀..s, m τ) + ∫ τ in t₀..t, m τ) =
      (fun t ↦ x₀ + ∫ τ in s..t, m τ) := by
    funext t
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hm.intervalIntegrable t₀ s) (hm.intervalIntegrable s t)]
    abel
  have h := suitable_weighted_mean_accelerated_frame hsol hbox ht hχ hχc hχs hm hmean
    hB hBc (c := x₀ - ∫ τ in t₀..s, m τ) (by rwa [heq])
  rwa [heq] at h

end FluidSingularSets
