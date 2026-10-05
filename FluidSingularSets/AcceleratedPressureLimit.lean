-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.AcceleratedPressureLp
public import FluidSingularSets.WeakEquationLimit

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The exact time marginal gives the strong norm of a time field on a
spatial product, with its genuine spatial-volume factor. -/
theorem accelerated_time_eLpNorm_product
    {E : Type*} [NormedAddCommGroup E] {B : Set Vec3} {J : Set ℝ}
    (hB : volume B < ⊤) {g : ℝ → E}
    (hg : AEStronglyMeasurable g (volume.restrict J))
    {b : ℝ≥0∞} (hb₀ : b ≠ 0) (hbtop : b ≠ ⊤) :
    eLpNorm (fun z : ParabolicPoint ↦ g z.2) b
      (volume.restrict (spaceTimeSet B J)) =
        (volume B) ^ (1 / b).toReal * eLpNorm g b (volume.restrict J) := by
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hB.ne
  have hmpProd : MeasurePreserving (Prod.snd : Vec3 × ℝ → ℝ)
      ((volume.restrict B).prod (volume.restrict J))
      (volume B • volume.restrict J) := by
    refine ⟨measurable_snd, ?_⟩
    rw [Measure.map_snd_prod, Measure.restrict_apply_univ]
  have hmp : MeasurePreserving (fun z : ParabolicPoint ↦ z.2)
      (volume.restrict (spaceTimeSet B J)) (volume B • volume.restrict J) := by
    rw [spaceTimeSet, volume_parabolicPoint_eq_prod, ← Measure.prod_restrict]
    exact hmpProd
  calc
    _ = eLpNorm g b (volume B • volume.restrict J) :=
      eLpNorm_comp_measurePreserving (hg.smul_measure _) hmp
    _ = _ := by
      simpa only [smul_eq_mul] using
        eLpNorm_smul_measure_of_ne_zero_of_ne_top hb₀ hbtop (volume B)

/-- Global strong time convergence gives strong convergence of the pulled
time field on every compact space-time set. -/
theorem accelerated_time_strongLp_on_compact
    {E : Type*} [NormedAddCommGroup E] {K : Set ParabolicPoint} (hK : IsCompact K)
    {g : ℝ → E} {gs : ℕ → ℝ → E} {b : ℝ≥0∞}
    (hb₀ : b ≠ 0) (hbtop : b ≠ ⊤)
    (hg : MemLp g b volume) (hgs : ∀ n, MemLp (gs n) b volume)
    (hconv : Tendsto (fun n ↦ eLpNorm (gs n - g) b volume) atTop (𝓝 0)) :
    MemLp (fun z : ParabolicPoint ↦ g z.2) b (volume.restrict K) ∧
      (∀ n, MemLp (fun z : ParabolicPoint ↦ gs n z.2) b (volume.restrict K)) ∧
      Tendsto (fun n ↦ eLpNorm (fun z : ParabolicPoint ↦ gs n z.2 - g z.2) b
        (volume.restrict K)) atTop (𝓝 0) := by
  let B : Set Vec3 := Prod.fst '' (show Set (Vec3 × ℝ) from K)
  have hBc : IsCompact B := (isCompact_prod_of_isCompact_parabolic hK).image continuous_fst
  have hB : volume B < ⊤ := hBc.measure_lt_top
  have hsub : K ⊆ spaceTimeSet B univ := fun z hz ↦ ⟨⟨z, hz, rfl⟩, mem_univ _⟩
  have hμ := Measure.restrict_mono hsub (le_refl (volume : Measure ParabolicPoint))
  have hmem {v : ℝ → E} (hv : MemLp v b volume) :
      MemLp (fun z : ParabolicPoint ↦ v z.2) b (volume.restrict K) := by
    have hv' : MemLp v b (volume.restrict univ) := by simpa using hv
    exact (accelerated_time_memLp_product hB hv').mono_measure hμ
  refine ⟨hmem hg, (fun n ↦ hmem (hgs n)), ?_⟩
  have hfactor : (volume B) ^ (1 / b).toReal ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hB.ne).ne
  have hbound (n : ℕ) : eLpNorm (fun z : ParabolicPoint ↦ gs n z.2 - g z.2) b
      (volume.restrict K) ≤
        (volume B) ^ (1 / b).toReal * eLpNorm (gs n - g) b volume := by
    calc
      _ ≤ eLpNorm (fun z : ParabolicPoint ↦ gs n z.2 - g z.2) b
          (volume.restrict (spaceTimeSet B univ)) := eLpNorm_mono_measure _ hμ
      _ = _ := by
        have hm : AEStronglyMeasurable (gs n - g) (volume.restrict univ) := by
          simpa using ((hgs n).sub hg).aestronglyMeasurable
        simpa using accelerated_time_eLpNorm_product hB hm hb₀ hbtop
  have hzero := ENNReal.Tendsto.const_mul hconv (Or.inr hfactor)
  simp only [mul_zero] at hzero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
    (fun _ ↦ bot_le) hbound

/-- A genuine strong acceleration limit gives the exact strong affine
pressure limit on compact spatial supports. Coordinates are bounded there;
the time marginal supplies the acceleration norm without any assumed joint
convergence premise. -/
theorem accelerated_affine_pressure_strongLp
    {K : Set ParabolicPoint} (hK : IsCompact K)
    {a : ℝ → Vec3} {as : ℕ → ℝ → Vec3}
    (ha : MemLp a (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (has : ∀ n, MemLp (as n) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hconv : Tendsto (fun n ↦ eLpNorm (as n - a) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm
      (fun z : ParabolicPoint ↦ (∑ i : Fin 3, as n z.2 i * z.1 i) -
        (∑ i : Fin 3, a z.2 i * z.1 i))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict K)) atTop (𝓝 0) := by
  let r : ℝ≥0∞ := ENNReal.ofReal (3 / 2 : ℝ)
  have hr : 1 ≤ r := by norm_num [r]
  obtain ⟨hat, hast, htime⟩ := accelerated_time_strongLp_on_compact hK
    (by norm_num [r] : r ≠ 0) ENNReal.ofReal_ne_top ha has hconv
  have hcoord (i : Fin 3) : MemLp (fun z : ParabolicPoint ↦ z.1 i) ⊤
      (volume.restrict K) := accelerated_continuous_memLp_on_compact hK
    ((continuous_apply i).comp continuous_fst_parabolicPoint) ⊤
  have hterms (i : Fin 3) : Tendsto (fun n ↦ eLpNorm
      (fun z : ParabolicPoint ↦ as n z.2 i * z.1 i - a z.2 i * z.1 i) r
      (volume.restrict K)) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ ↦
        eLpNorm ((fun z : ParabolicPoint ↦ z.1 i) - (fun z : ParabolicPoint ↦ z.1 i)) ⊤
          (volume.restrict K)) atTop (𝓝 0) := by simp
    exact tendsto_eLpNorm_sub_mul hr (by simp) hr (memLp_pi_iff.mp hat i) (hcoord i)
      (fun n ↦ memLp_pi_iff.mp (hast n) i) (fun _ ↦ hcoord i)
      (tendsto_eLpNorm_pi_component_sub hat hast htime i) hc
  have hsum := tendsto_finsetSum Finset.univ (fun i _ ↦ hterms i)
  simp only [Finset.sum_const_zero] at hsum
  have hbound (n : ℕ) : eLpNorm
      (fun z : ParabolicPoint ↦ (∑ i : Fin 3, as n z.2 i * z.1 i) -
        (∑ i : Fin 3, a z.2 i * z.1 i)) r (volume.restrict K) ≤
      ∑ i : Fin 3, eLpNorm
        (fun z : ParabolicPoint ↦ as n z.2 i * z.1 i - a z.2 i * z.1 i) r
        (volume.restrict K) := by
    have heq : (fun z : ParabolicPoint ↦ (∑ i : Fin 3, as n z.2 i * z.1 i) -
        (∑ i : Fin 3, a z.2 i * z.1 i)) =
        ∑ i : Fin 3, (fun z : ParabolicPoint ↦ as n z.2 i * z.1 i - a z.2 i * z.1 i) := by
      funext z
      simp only [Finset.sum_apply, Finset.sum_sub_distrib]
    rw [heq]
    exact eLpNorm_sum_le hr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ bot_le) hbound

/-- Uniform convergence of continuous means gives strong convergence of the
actual mean time fields on any finite local tube, in every exponent. -/
theorem accelerated_mean_strongLp_of_uniform
    {E : Type*} [NormedAddCommGroup E] {S : Set ParabolicPoint} (hS : MeasurableSet S)
    [IsFiniteMeasure (volume.restrict S)] {T : Set ℝ}
    (hST : ∀ z ∈ S, z.2 ∈ T)
    {m : ℝ → E} {ms : ℕ → ℝ → E} (hm : Continuous m)
    (hms : ∀ n, Continuous (ms n)) (hconv : TendstoUniformlyOn ms m atTop T)
    (b : ℝ≥0∞) :
    Tendsto (fun n ↦ eLpNorm (fun z : ParabolicPoint ↦ ms n z.2 - m z.2) b
      (volume.restrict S)) atTop (𝓝 0) := by
  let F := (volume.restrict S) univ ^ b.toReal⁻¹
  have hF : F ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg
    (inv_nonneg.mpr ENNReal.toReal_nonneg) (measure_ne_top _ _)).ne
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ := ENNReal.exists_nnreal_pos_mul_lt hF hε.ne'
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv (δ : ℝ) hδ] with n hn
  have hdiff : AEStronglyMeasurable
      (fun z : ParabolicPoint ↦ ms n z.2 - m z.2) (volume.restrict S) :=
    (((hms n).comp continuous_snd_parabolicPoint).sub
      (hm.comp continuous_snd_parabolicPoint)).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂volume.restrict S, ‖ms n z.2 - m z.2‖ ≤ (δ : ℝ) := by
    filter_upwards [ae_restrict_mem hS] with z hz
    simpa only [dist_eq_norm_sub, norm_sub_rev] using (hn z.2 (hST z hz)).le
  calc
    _ ≤ F * ENNReal.ofReal δ := eLpNorm_le_of_ae_bound hdiff hbound
    _ = (δ : ℝ≥0∞) * F := by rw [ENNReal.ofReal_coe_nnreal, mul_comm]
    _ ≤ ε := hδbound.le

/-- Genuine source suitability, converging paths, uniformly converging means,
and strongly converging time accelerations give all strong limits of the
actual transformed fields. The affine pressure and mean corrections are
derived here, rather than supplied as joint convergence hypotheses. -/
theorem suitable_accelerated_fields_strongLp
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {Xs : ℕ → ℝ → Vec3} {X : ℝ → Vec3}
    {ms : ℕ → ℝ → Vec3} {m : ℝ → Vec3}
    {accs : ℕ → ℝ → Vec3} {acc : ℝ → Vec3}
    (hXs : ∀ n, Continuous (Xs n)) (hX : Continuous X)
    (hms : ∀ n, Continuous (ms n)) (hm : Continuous m)
    {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hXconv : TendstoUniformlyOn Xs X atTop (Icc t₀ t₁))
    (hmconv : TendstoUniformlyOn ms m atTop (Icc t₀ t₁))
    (ha : MemLp acc (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (has : ∀ n, MemLp (accs n) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (haconv : Tendsto (fun n ↦ eLpNorm (accs n - acc) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
      atTop (𝓝 0))
    {S K : Set ParabolicPoint} (hS : IsCompact S) (hK : IsCompact K)
    (hKdom : K ⊆ spaceTimeSet Ω I) (hStime : ∀ z ∈ S, z.2 ∈ Icc t₀ t₁)
    (himages : ∀ᶠ n in atTop, acceleratedFrameMap (Xs n) '' S ⊆ K)
    (himage : acceleratedFrameMap X '' S ⊆ K) :
    Tendsto (fun n ↦ eLpNorm
      (acceleratedVelocity (Xs n) (ms n) u - acceleratedVelocity X m u) 2
        (volume.restrict S)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm
        (acceleratedVelocity (Xs n) (ms n) u - acceleratedVelocity X m u) 3
          (volume.restrict S)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm
        (acceleratedGradient (Xs n) Du - acceleratedGradient X Du) 2
          (volume.restrict S)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm
        (acceleratedPressure (Xs n) (accs n) p - acceleratedPressure X acc p)
          (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict S)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm
        (acceleratedForce (Xs n) f - acceleratedForce X f)
          (ENNReal.ofReal q) (volume.restrict S)) atTop (𝓝 0) := by
  let : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  obtain ⟨hu2, hu3, hD, hp, hf⟩ := suitable_moving_fields_strongLp hsol hXs hX ht hXconv
    hS.measurableSet hK hKdom hStime himages himage
  have hmean (b : ℝ≥0∞) := accelerated_mean_strongLp_of_uniform hS.measurableSet hStime
    hm hms hmconv b
  have hvel (b : ℝ≥0∞) (hb : 1 ≤ b)
      (hv : Tendsto (fun n ↦ eLpNorm
        ((u ∘ acceleratedFrameMap (Xs n)) - (u ∘ acceleratedFrameMap X)) b
        (volume.restrict S)) atTop (𝓝 0)) :
      Tendsto (fun n ↦ eLpNorm
        (acceleratedVelocity (Xs n) (ms n) u - acceleratedVelocity X m u) b
          (volume.restrict S)) atTop (𝓝 0) := by
    have hzero := hv.add (hmean b)
    simp only [zero_add] at hzero
    have hbound (n : ℕ) : eLpNorm
        (acceleratedVelocity (Xs n) (ms n) u - acceleratedVelocity X m u) b
          (volume.restrict S) ≤
        eLpNorm ((u ∘ acceleratedFrameMap (Xs n)) - (u ∘ acceleratedFrameMap X)) b
          (volume.restrict S) +
        eLpNorm (fun z : ParabolicPoint ↦ ms n z.2 - m z.2) b (volume.restrict S) := by
      have heq : acceleratedVelocity (Xs n) (ms n) u - acceleratedVelocity X m u =
          ((u ∘ acceleratedFrameMap (Xs n)) - (u ∘ acceleratedFrameMap X)) -
            (fun z : ParabolicPoint ↦ ms n z.2 - m z.2) := by
        funext z
        simp only [acceleratedVelocity, Pi.sub_apply, Function.comp_apply]
        abel
      rw [heq]
      exact eLpNorm_sub_le hb
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
      (fun _ ↦ bot_le) hbound
  have hAff := accelerated_affine_pressure_strongLp hS ha has haconv
  have hP : Tendsto (fun n ↦ eLpNorm
      (acceleratedPressure (Xs n) (accs n) p - acceleratedPressure X acc p)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict S)) atTop (𝓝 0) := by
    have hzero := hp.add hAff
    simp only [zero_add] at hzero
    have hbound (n : ℕ) : eLpNorm
        (acceleratedPressure (Xs n) (accs n) p - acceleratedPressure X acc p)
          (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict S) ≤
        eLpNorm ((p ∘ acceleratedFrameMap (Xs n)) - (p ∘ acceleratedFrameMap X))
          (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict S) +
        eLpNorm (fun z : ParabolicPoint ↦ (∑ i : Fin 3, accs n z.2 i * z.1 i) -
          (∑ i : Fin 3, acc z.2 i * z.1 i)) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict S) := by
      have heq : acceleratedPressure (Xs n) (accs n) p - acceleratedPressure X acc p =
          ((p ∘ acceleratedFrameMap (Xs n)) - (p ∘ acceleratedFrameMap X)) +
            (fun z : ParabolicPoint ↦ (∑ i : Fin 3, accs n z.2 i * z.1 i) -
              (∑ i : Fin 3, acc z.2 i * z.1 i)) := by
        funext z
        simp only [acceleratedPressure, Pi.sub_apply, Function.comp_apply, Pi.add_apply]
        ring
      rw [heq]
      exact eLpNorm_add_le (by norm_num)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
      (fun _ ↦ bot_le) hbound
  exact ⟨hvel 2 (by norm_num) hu2, hvel 3 (by norm_num) hu3, hD, hP, hf⟩

end FluidSingularSets
