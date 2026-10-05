-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.AcceleratedFrame
public import FluidSingularSets.CompactCharge
public import FluidSingularSets.WeightedVelocityPoincare
public import CKN.Foundation.Parabolic.Campanato
public import CKN.Setting.ScalingInvarianceWeak
public import CKN.Foundation.Sobolev.WeakGradientGluingTPressureMean

/-!
# Actual local data in a moving frame

Continuous moving coordinates preserve volume and compactness. This transports
actual suitable-solution integrability to compact subtubes. Subtracting a bounded
continuous mean and adding a continuous affine acceleration pressure preserve
those local classes. The slice energy and weak-gradient clauses are proved
separately before assembling the full data predicate.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual moving-coordinate homeomorphism on parabolic space-time. -/
def acceleratedParabolicHomeomorph (X : ℝ → Vec3) (hX : Continuous X) :
    ParabolicPoint ≃ₜ ParabolicPoint :=
  parabolicHomeomorph.trans ((acceleratedFrameHomeomorph X hX).trans
    parabolicHomeomorph.symm)

/-- The volume-preserving coordinate change restricts exactly to any source set
and its image, rather than a larger bounding cylinder. -/
theorem acceleratedFrameMap_restrict_measurePreserving
    {X : ℝ → Vec3} (hX : Continuous X) (K : Set ParabolicPoint) :
    MeasurePreserving (acceleratedFrameMap X) (volume.restrict K)
      (volume.restrict (acceleratedFrameMap X '' K)) := by
  have hemb : MeasurableEmbedding (acceleratedFrameMap X) :=
    (acceleratedParabolicHomeomorph X hX).measurableEmbedding
  exact (acceleratedFrameMap_measurePreserving X hX.measurable).restrict_image_emb hemb K

/-- Exact compact-set transport of an ordinary local `MemLp` class. -/
theorem accelerated_comp_memLp {E : Type*} [NormedAddCommGroup E]
    {X : ℝ → Vec3} (hX : Continuous X) (K : Set ParabolicPoint)
    {g : ParabolicPoint → E} {b : ℝ≥0∞}
    (hg : MemLp g b (volume.restrict (acceleratedFrameMap X '' K))) :
    MemLp (fun z ↦ g (acceleratedFrameMap X z)) b (volume.restrict K) :=
  hg.comp_measurePreserving (acceleratedFrameMap_restrict_measurePreserving hX K)

/-- Continuous functions have every finite-exponent local norm on a compact set. -/
theorem accelerated_continuous_memLp_on_compact {E : Type*} [NormedAddCommGroup E]
    {K : Set ParabolicPoint} (hK : IsCompact K) {g : ParabolicPoint → E}
    (hg : Continuous g) (b : ℝ≥0∞) : MemLp g b (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  obtain ⟨C, hC⟩ := (hK.image hg).isBounded.exists_norm_le
  exact MemLp.of_bound hg.aestronglyMeasurable C (by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact hC (g z) ⟨z, hz, rfl⟩)

/-- Actual suitable data give all four genuine pulled-back compact norms. -/
theorem suitable_accelerated_compact_pullback_memLp
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X : ℝ → Vec3} (hX : Continuous X) {K : Set ParabolicPoint} (hK : IsCompact K)
    (hKdom : acceleratedFrameMap X '' K ⊆ spaceTimeSet Ω I) :
    MemLp (fun z ↦ u (acceleratedFrameMap X z)) 2 (volume.restrict K) ∧
      MemLp (acceleratedGradient X Du) 2 (volume.restrict K) ∧
      MemLp (fun z ↦ p (acceleratedFrameMap X z))
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict K) ∧
      MemLp (acceleratedForce X f) (ENNReal.ofReal q) (volume.restrict K) := by
  have himage : IsCompact (acceleratedFrameMap X '' K) :=
    hK.image (acceleratedParabolicHomeomorph X hX).continuous
  exact ⟨accelerated_comp_memLp hX K
      (velocity_memLp_two_on_compact_of_data hsol.toData himage hKdom),
    accelerated_comp_memLp hX K
      (gradient_memLp_two_on_compact_of_data hsol.toData himage hKdom),
    accelerated_comp_memLp hX K
      (pressure_memLp_threeHalves_on_compact_of_data hsol.toData himage hKdom),
    accelerated_comp_memLp hX K
      (force_memLp_on_compact_of_data hsol.toData himage hKdom)⟩

/-- Actual suitable data retain the complete compact velocity, gradient, pressure
and force norms after subtracting a continuous mean and adding affine pressure. -/
theorem suitable_accelerated_compact_fields_memLp
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m a : ℝ → Vec3} (hX : Continuous X) (hm : Continuous m) (ha : Continuous a)
    {K : Set ParabolicPoint} (hK : IsCompact K)
    (hKdom : acceleratedFrameMap X '' K ⊆ spaceTimeSet Ω I) :
    MemLp (acceleratedVelocity X m u) 2 (volume.restrict K) ∧
      MemLp (acceleratedGradient X Du) 2 (volume.restrict K) ∧
      MemLp (acceleratedPressure X a p) (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict K) ∧
      MemLp (acceleratedForce X f) (ENNReal.ofReal q) (volume.restrict K) := by
  obtain ⟨hu, hDu, hp, hf⟩ := suitable_accelerated_compact_pullback_memLp hsol hX hK hKdom
  have hmean : MemLp (fun z : ParabolicPoint ↦ m z.2) 2 (volume.restrict K) :=
    accelerated_continuous_memLp_on_compact hK
      (hm.comp continuous_snd_parabolicPoint) 2
  have haffine : Continuous (fun z : ParabolicPoint ↦ ∑ i : Fin 3, a z.2 i * z.1 i) := by
    apply continuous_finsetSum
    intro i _
    exact (((continuous_apply i).comp ha).comp continuous_snd_parabolicPoint).mul
      ((continuous_apply i).comp continuous_fst_parabolicPoint)
  have hpressure := accelerated_continuous_memLp_on_compact hK haffine
    (ENNReal.ofReal (3 / 2 : ℝ))
  exact ⟨hu.sub hmean, hDu, hp.add hpressure, hf⟩


/-- Spatial translation preserves volume on a set and its exact translate. -/
theorem spatialTranslation_restrict_measurePreserving (a : Vec3) (B : Set Vec3) :
    MeasurePreserving (fun x : Vec3 ↦ a + x) (volume.restrict B)
      (volume.restrict ((fun x : Vec3 ↦ a + x) '' B)) :=
  (measurePreserving_add_left (volume : Measure Vec3) a).restrict_image_emb
    (Homeomorph.addLeft a).measurableEmbedding B

/-- Restriction and translation preserve an actual weak derivative, and subtracting
an arbitrary spatial constant leaves the derivative unchanged. -/
theorem weakPartial_spatialTranslation_sub_const
    {B Ω : Set Vec3} (hB : IsOpen B) (hBc : IsCompact (closure B))
    (a : Vec3) (hsub : (fun x : Vec3 ↦ a + x) '' B ⊆ Ω)
    {g dg : Vec3 → ℝ} {j : Fin 3}
    (hg : MemLp g 2 (volume.restrict Ω))
    (hdg : MemLp dg 2 (volume.restrict Ω))
    (hweak : HasWeakPartialDerivOn Ω j g dg) (c : ℝ) :
    HasWeakPartialDerivOn B j (fun x ↦ g (a + x) - c) (fun x ↦ dg (a + x)) := by
  let T := (fun x : Vec3 ↦ a + x) '' B
  have hT : IsOpen T := (Homeomorph.addLeft a).isOpenMap B hB
  have hgT : MemLp g 2 (volume.restrict T) :=
    hg.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hdgT : MemLp dg 2 (volume.restrict T) :=
    hdg.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hweakT := hweak.restrict hT hsub
  have htrans : HasWeakPartialDerivOn B j
      (fun x ↦ g (a + x)) (fun x ↦ dg (a + x)) := by
    have heq : T = scalingSpace 1 a '' B := by
      change (fun x : Vec3 ↦ a + x) '' B = scalingSpace 1 a '' B
      congr 1
      funext x
      simp [scalingSpace]
    simpa [scalingSpace] using hasWeakPartialDerivOn_scaling 1 (by norm_num) a
      hT.measurableSet j heq hweakT hgT.aestronglyMeasurable hdgT.aestronglyMeasurable
  let : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr ((measure_mono subset_closure).trans_lt
      hBc.measure_lt_top).ne
  have hgp := hgT.comp_measurePreserving (spatialTranslation_restrict_measurePreserving a B)
  have hdgp := hdgT.comp_measurePreserving (spatialTranslation_restrict_measurePreserving a B)
  have hgi : IntegrableOn (fun x ↦ g (a + x)) B := hgp.integrable (by norm_num)
  have hdgi : IntegrableOn (fun x ↦ dg (a + x)) B := hdgp.integrable (by norm_num)
  exact HasWeakPartialDerivOn.sub_const hB hgi.locallyIntegrableOn
    hdgi.locallyIntegrableOn htrans c

/-- The genuine quadratic energy controls all spatial weak-gradient slices after
time-dependent translation and subtraction of any spatially constant mean. -/
theorem suitable_accelerated_weakGradient_slices
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {Ω₀ B : Set Vec3} {J₀ J : Set ℝ}
    (hbox : localBox Ω I Ω₀ J₀) (hB : IsOpen B) (hBc : IsCompact (closure B))
    {X m : ℝ → Vec3}
    (htime : J ⊆ J₀) (hJ : MeasurableSet J) (hspace : ∀ t ∈ J, (fun x : Vec3 ↦ X t + x) '' B ⊆ Ω₀)
    (i : Fin 3) :
    ∀ᵐ t ∂volume.restrict J, HasWeakGradientOn B
      (fun x ↦ acceleratedVelocity X m u (x, t) i)
      (fun x ↦ acceleratedGradient X Du (x, t) i) := by
  have hu := hsol.toData.aestronglyMeasurable_velocity hbox
  have hDu := hsol.toData.aestronglyMeasurable_gradient hbox
  have he := hsol.toData.energy_lintegral_lt_top hbox
  have hue : (∫⁻ z in Ω₀ ×ˢ J₀, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    (lintegral_mono fun _ ↦ le_add_right le_rfl).trans_lt he
  have hDue : (∫⁻ z in Ω₀ ×ˢ J₀, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    (lintegral_mono fun _ ↦ le_add_left le_rfl).trans_lt he
  have hume := ae_memLp_two_spatial_slices u Ω₀ J₀ hu hue
  have hDume := ae_memLp_two_spatial_slices Du Ω₀ J₀ hDu hDue
  have hweak := hsol.toData.hasWeakGradientOn_slice hbox i
  have hle : volume.restrict J ≤ volume.restrict J₀ := Measure.restrict_mono htime le_rfl
  filter_upwards [ae_mono hle hume, ae_mono hle hDume, ae_mono hle hweak,
    ae_restrict_mem hJ] with t hut hDut hweakt ht
  intro j
  have hg := (memLp_pi_iff).1 hut i
  have hdg := (memLp_pi_iff).1 ((memLp_pi_iff).1 hDut i) j
  exact weakPartial_spatialTranslation_sub_const hB hBc (X t) (hspace t ht)
    hg hdg (hweakt j) (m t i)

/-- A convenient exact comparison of extended quadratic norms. -/
theorem accelerated_enorm_sub_sq_le {E : Type*} [NormedAddCommGroup E] (U M : E) :
    ‖U - M‖ₑ ^ (2 : ℝ) ≤ 2 * ‖U‖ₑ ^ (2 : ℝ) + 2 * ‖M‖ₑ ^ (2 : ℝ) := by
  have hnorm : ‖U - M‖ ^ 2 ≤ 2 * ‖U‖ ^ 2 + 2 * ‖M‖ ^ 2 := by
    have h := norm_sub_le U M
    have hU := norm_nonneg U
    have hM := norm_nonneg M
    have hsub := norm_nonneg (U - M)
    nlinarith [sq_nonneg (‖U‖ - ‖M‖)]
  have heq (v : E) : ‖v‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
    rw [ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg v)]
  rw [heq, heq, heq]
  have h := ENNReal.ofReal_le_ofReal hnorm
  rw [ENNReal.ofReal_add (by positivity : 0 ≤ 2 * ‖U‖ ^ 2)
    (by positivity : 0 ≤ 2 * ‖M‖ ^ 2),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
  norm_num only [ENNReal.ofReal_ofNat] at h
  exact h

/-- Exact translation of a spatial slice, even before a measurable representative
is chosen. The homeomorphism preserves the restricted volume. -/
theorem accelerated_lintegral_slice (a : Vec3) (B : Set Vec3) (g : Vec3 → ℝ≥0∞) :
    (∫⁻ x in B, g (a + x)) = ∫⁻ y in (fun x : Vec3 ↦ a + x) '' B, g y :=
  (spatialTranslation_restrict_measurePreserving a B).lintegral_comp_emb
    (Homeomorph.addLeft a).measurableEmbedding g


/-- The actual essential spatial slice energy remains finite in a moving tube.
A continuous mean is bounded on the compact time closure; translation compares
its pulled-back energy to the actual source box energy at the same time. -/
theorem suitable_accelerated_sliceEnergy_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {Ω₀ B : Set Vec3} {J₀ J : Set ℝ} (hbox : localBox Ω I Ω₀ J₀)
    (hBc : IsCompact (closure B)) (hJc : IsCompact (closure J))
    {X m : ℝ → Vec3} (hm : Continuous m) (htime : J ⊆ J₀) (hJ : MeasurableSet J)
    (hspace : ∀ t ∈ J, (fun x : Vec3 ↦ X t + x) '' B ⊆ Ω₀) :
    essSup (fun t ↦ ∫⁻ x in B, ‖acceleratedVelocity X m u (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict J) < ⊤ := by
  let E : ℝ → ℝ≥0∞ := fun t ↦ ∫⁻ x in Ω₀, ‖u (x, t)‖ₑ ^ (2 : ℝ)
  have hE : essSup E (volume.restrict J₀) < ⊤ :=
    hsol.toData.essSup_sliceEnergy_lt_top hbox
  obtain ⟨C, hC⟩ := (hJc.image hm).isBounded.exists_norm_le
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hmbound (t : ℝ) (ht : t ∈ J) : ‖m t‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (M ^ 2) := by
    have hnorm : ‖m t‖ ≤ M := (hC (m t) ⟨t, subset_closure ht, rfl⟩).trans
      (le_max_left _ _)
    have hsq : ‖m t‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (m t)]
    rw [ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg (m t))]
    exact ENNReal.ofReal_le_ofReal hsq
  have hvol : volume B < ⊤ := (measure_mono subset_closure).trans_lt hBc.measure_lt_top
  let A : ℝ≥0∞ := 2 * essSup E (volume.restrict J₀) +
    2 * ENNReal.ofReal (M ^ 2) * volume B
  have hA : A < ⊤ := ENNReal.add_lt_top.mpr ⟨
    ENNReal.mul_lt_top (by norm_num) hE,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top) hvol⟩
  have heae : ∀ᵐ t ∂volume.restrict J, E t ≤ essSup E (volume.restrict J₀) :=
    ae_mono (Measure.restrict_mono htime le_rfl) (ENNReal.ae_le_essSup E)
  have hbound : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖acceleratedVelocity X m u (x, t)‖ₑ ^ (2 : ℝ)) ≤ A := by
    filter_upwards [heae, ae_restrict_mem hJ] with t ht hJt
    calc
      _ ≤ ∫⁻ x in B,
          2 * ‖u (X t + x, t)‖ₑ ^ (2 : ℝ) + 2 * ‖m t‖ₑ ^ (2 : ℝ) :=
        lintegral_mono (fun x ↦ accelerated_enorm_sub_sq_le _ _)
      _ = 2 * (∫⁻ x in B, ‖u (X t + x, t)‖ₑ ^ (2 : ℝ)) +
          (2 * ‖m t‖ₑ ^ (2 : ℝ)) * volume B := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ (by norm_num), lintegral_const, Measure.restrict_apply_univ]
      _ ≤ 2 * E t + (2 * ‖m t‖ₑ ^ (2 : ℝ)) * volume B := by
        have hslice : (∫⁻ x in B, ‖u (X t + x, t)‖ₑ ^ (2 : ℝ)) ≤ E t := by
          calc
            _ = ∫⁻ y in (fun x : Vec3 ↦ X t + x) '' B,
                ‖u (y, t)‖ₑ ^ (2 : ℝ) :=
              accelerated_lintegral_slice (X t) B
                (fun y ↦ ‖u (show ParabolicPoint from (y, t))‖ₑ ^ (2 : ℝ))
            _ ≤ E t := lintegral_mono_set (hspace t hJt)
        gcongr
      _ ≤ A := by
        dsimp [A]
        gcongr
        exact hmbound t hJt
  exact (essSup_le_of_ae_le A hbound).trans_lt hA

/-- A spatially compact and temporally compact product is compact for the actual
parabolic topology, via its genuine homeomorphism with the ordinary product. -/
theorem accelerated_isCompact_product {B : Set Vec3} {J : Set ℝ}
    (hB : IsCompact B) (hJ : IsCompact J) : IsCompact (spaceTimeSet B J) := by
  have h := parabolicHomeomorph.isCompact_preimage.mpr (hB.prod hJ)
  simpa only [parabolicHomeomorph_preimage, spaceTimeSet] using h


/-- Compact norm transport gives the actual four `MemLp` clauses on each local
subbox of a moving tube. -/
theorem suitable_accelerated_localBox_memLp
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m a : ℝ → Vec3} (hX : Continuous X) (hm : Continuous m) (ha : Continuous a)
    (htube : acceleratedFrameMap X '' spaceTimeSet B J ⊆ spaceTimeSet Ω I)
    {B' : Set Vec3} {J' : Set ℝ} (hbox : localBox B J B' J') :
    MemLp (acceleratedVelocity X m u) 2 (volume.restrict (spaceTimeSet B' J')) ∧
      MemLp (acceleratedGradient X Du) 2 (volume.restrict (spaceTimeSet B' J')) ∧
      MemLp (acceleratedPressure X a p) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet B' J')) ∧
      MemLp (acceleratedForce X f) (ENNReal.ofReal q)
        (volume.restrict (spaceTimeSet B' J')) := by
  let K := spaceTimeSet (closure B') (closure J')
  have hK : IsCompact K := accelerated_isCompact_product hbox.2.1 hbox.2.2.2.2.1
  have hKdom : acceleratedFrameMap X '' K ⊆ spaceTimeSet Ω I := by
    rintro z ⟨w, hw, rfl⟩
    exact htube ⟨w, ⟨hbox.2.2.1 hw.1, hbox.2.2.2.2.2 hw.2⟩, rfl⟩
  obtain ⟨hv, hD, hp, hf⟩ := suitable_accelerated_compact_fields_memLp
    hsol hX hm ha hK hKdom
  have hsub : spaceTimeSet B' J' ⊆ K :=
    fun _ hz ↦ ⟨subset_closure hz.1, subset_closure hz.2⟩
  have hμ := Measure.restrict_mono hsub (le_refl (volume : Measure ParabolicPoint))
  exact ⟨hv.mono_measure hμ, hD.mono_measure hμ, hp.mono_measure hμ, hf.mono_measure hμ⟩

/-- Two genuine quadratic classes give the finite joint energy clause. -/
theorem accelerated_quadratic_energy_lt_top
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {S : Set ParabolicPoint} {v : ParabolicPoint → E} {D : ParabolicPoint → F}
    (hv : MemLp v 2 (volume.restrict S)) (hD : MemLp D 2 (volume.restrict S)) :
    (∫⁻ z in S, ‖v z‖ₑ ^ (2 : ℝ) + ‖D z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  have hv' : MemLp v (ENNReal.ofReal (2 : ℝ)) (volume.restrict S) := by simpa using hv
  have hD' : MemLp D (ENNReal.ofReal (2 : ℝ)) (volume.restrict S) := by simpa using hD
  have hvlt := (memLp_ofReal_iff_lintegral_enorm_rpow_lt_top (by norm_num)
    hv.aestronglyMeasurable).1 hv'
  have hDlt := (memLp_ofReal_iff_lintegral_enorm_rpow_lt_top (by norm_num)
    hD.aestronglyMeasurable).1 hD'
  rw [lintegral_add_left' (hv.aestronglyMeasurable.enorm.pow_const _) _]
  exact ENNReal.add_lt_top.mpr ⟨hvlt, hDlt⟩

/-- All actual data clauses hold for continuous moving coordinates, continuous
relative means and continuous affine pressure accelerations. Compact image tubes
are placed inside genuine source boxes, which provide the slice energy and weak
spatial derivatives; no transported analytic premise is assumed. -/
theorem suitable_accelerated_data
    {Ω B : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {X m a : ℝ → Vec3} (hX : Continuous X) (hm : Continuous m) (ha : Continuous a)
    (hB : IsOpen B) (hJ : IsOpen J) (hJord : OrdConnected J)
    (htube : acceleratedFrameMap X '' spaceTimeSet B J ⊆ spaceTimeSet Ω I) :
    IsSuitableWeakSolutionData B J q (acceleratedVelocity X m u)
      (acceleratedGradient X Du) (acceleratedPressure X a p) (acceleratedForce X f) := by
  refine ⟨hB, hJ, hJord, hsol.toData.five_halves_lt_exponent, ?_, ?_⟩
  · intro B' J' hbox
    have hf := (suitable_accelerated_localBox_memLp hsol hX hm ha htube hbox).2.2.2
    exact (memLp_pi_iff).1 hf
  · intro B' J' hbox
    obtain ⟨hv, hD, hp, hf⟩ :=
      suitable_accelerated_localBox_memLp hsol hX hm ha htube hbox
    refine ⟨hv.aestronglyMeasurable, hD.aestronglyMeasurable,
      hp.aestronglyMeasurable, hf.aestronglyMeasurable, ?_,
      accelerated_quadratic_energy_lt_top hv hD, hp, hf, ?_⟩
    all_goals
      by_cases hB' : B'.Nonempty
    · let K := spaceTimeSet (closure B') (closure J')
      have hK : IsCompact K := accelerated_isCompact_product hbox.2.1 hbox.2.2.2.2.1
      have himage : IsCompact (acceleratedFrameMap X '' K) :=
        hK.image (acceleratedParabolicHomeomorph X hX).continuous
      have hKdom : acceleratedFrameMap X '' K ⊆ spaceTimeSet Ω I := by
        rintro z ⟨w, hw, rfl⟩
        exact htube ⟨w, ⟨hbox.2.2.1 hw.1, hbox.2.2.2.2.2 hw.2⟩, rfl⟩
      obtain ⟨Ω₀, J₀, hsource, hcover⟩ := caccioppoli_localBox_of_compact_subset
        hsol.1 hsol.2.1 hsol.2.2.1 himage hKdom
      have htime : J' ⊆ J₀ := by
        obtain ⟨x, hx⟩ := hB'
        intro t ht
        exact (hcover ⟨(x, t), ⟨subset_closure hx, subset_closure ht⟩, rfl⟩).2
      have hspace : ∀ t ∈ J', (fun x : Vec3 ↦ X t + x) '' B' ⊆ Ω₀ := by
        intro t ht y hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact (hcover ⟨(x, t), ⟨subset_closure hx, subset_closure ht⟩, rfl⟩).1
      exact suitable_accelerated_sliceEnergy_lt_top hsol hsource hbox.2.1
        hbox.2.2.2.2.1 hm htime hbox.2.2.2.1.measurableSet hspace
    · have hempty : B' = ∅ := not_nonempty_iff_eq_empty.mp hB'
      have hbound : ∀ᵐ t ∂volume.restrict J',
          (∫⁻ x in B', ‖acceleratedVelocity X m u (x, t)‖ₑ ^ (2 : ℝ)) ≤ 0 := by
        simp [hempty]
      exact (essSup_le_of_ae_le 0 hbound).trans_lt (by norm_num)
    · let K := spaceTimeSet (closure B') (closure J')
      have hK : IsCompact K := accelerated_isCompact_product hbox.2.1 hbox.2.2.2.2.1
      have himage : IsCompact (acceleratedFrameMap X '' K) :=
        hK.image (acceleratedParabolicHomeomorph X hX).continuous
      have hKdom : acceleratedFrameMap X '' K ⊆ spaceTimeSet Ω I := by
        rintro z ⟨w, hw, rfl⟩
        exact htube ⟨w, ⟨hbox.2.2.1 hw.1, hbox.2.2.2.2.2 hw.2⟩, rfl⟩
      obtain ⟨Ω₀, J₀, hsource, hcover⟩ := caccioppoli_localBox_of_compact_subset
        hsol.1 hsol.2.1 hsol.2.2.1 himage hKdom
      have htime : J' ⊆ J₀ := by
        obtain ⟨x, hx⟩ := hB'
        intro t ht
        exact (hcover ⟨(x, t), ⟨subset_closure hx, subset_closure ht⟩, rfl⟩).2
      have hspace : ∀ t ∈ J', (fun x : Vec3 ↦ X t + x) '' B' ⊆ Ω₀ := by
        intro t ht y hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact (hcover ⟨(x, t), ⟨subset_closure hx, subset_closure ht⟩, rfl⟩).1
      intro i
      exact suitable_accelerated_weakGradient_slices hsol hsource hbox.1 hbox.2.1
        htime hbox.2.2.2.1.measurableSet hspace i
    · have hempty : B' = ∅ := not_nonempty_iff_eq_empty.mp hB'
      intro i
      apply Eventually.of_forall
      intro t j φ _ _ _
      simp [hempty]

end FluidSingularSets
