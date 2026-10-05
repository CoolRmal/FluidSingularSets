-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallHarmonicOperators
public import FluidSingularSets.LocalBoxProjectedLocalEnergy

/-!
# Genuine projected source classes on every compact inner radius

The compact subtype carries its actual restricted Lebesgue measure. All field
and velocity-slice classes are derived from the original suitable solution and
its original local-box interval, without a prescribed spatial margin.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual spatial Lebesgue measure on the compact pressure interior. -/
def fullBallInteriorMeasure (ρ : ℝ) : Measure (fullBallCompactInterior ρ) :=
  (volume.restrict (fullBallCompactInterior ρ)).comap Subtype.val

instance fullBallInteriorMeasure_isFiniteMeasure (ρ : ℝ) :
    IsFiniteMeasure (fullBallInteriorMeasure ρ) := by
  let : IsFiniteMeasure (volume.restrict (fullBallCompactInterior ρ)) :=
    isFiniteMeasure_restrict.mpr
      ((isCompact_iff_compactSpace.mpr
        (inferInstance : CompactSpace (fullBallCompactInterior ρ))).measure_lt_top.ne)
  unfold fullBallInteriorMeasure
  infer_instance

/-- The subtype inclusion carries the real compact interior volume to the
ambient spatial Lebesgue measure restricted to that interior. -/
theorem fullBallInterior_measurePreserving (ρ : ℝ) :
    MeasurePreserving (Subtype.val : (fullBallCompactInterior ρ) → Vec3)
      (fullBallInteriorMeasure ρ) (volume.restrict (fullBallCompactInterior ρ)) := by
  have hs : MeasurableSet (fullBallCompactInterior ρ) :=
    (isClosed_closure : IsClosed (fullBallCompactInterior ρ)).measurableSet
  have h := measurePreserving_subtype_coe
    (μa := volume.restrict (fullBallCompactInterior ρ)) hs
  simpa only [fullBallInteriorMeasure, Measure.restrict_restrict hs, inter_self] using h

/-- Product integration over the true compact interior is native Lebesgue
integration restricted to that same spatial set and time interval. -/
theorem fullBallInterior_product_measurePreserving (ρ : ℝ) (J : Set ℝ) :
    MeasurePreserving (fun z : (fullBallCompactInterior ρ) × ℝ ↦ (z.1.1, z.2))
      ((fullBallInteriorMeasure ρ).prod (volume.restrict J))
      ((volume.restrict (fullBallCompactInterior ρ)).prod (volume.restrict J)) := by
  have hs : MeasurableSet (fullBallCompactInterior ρ) :=
    (isClosed_closure : IsClosed (fullBallCompactInterior ρ)).measurableSet
  let : IsFiniteMeasure ((volume.restrict (fullBallCompactInterior ρ)).comap
      (Subtype.val : (fullBallCompactInterior ρ) → Vec3)) :=
    fullBallInteriorMeasure_isFiniteMeasure ρ
  have hp := (measurePreserving_subtype_coe
    (μa := volume.restrict (fullBallCompactInterior ρ)) hs).prod
    (MeasurePreserving.id (volume.restrict J))
  change MeasurePreserving
    (Prod.map (Subtype.val : (fullBallCompactInterior ρ) → Vec3) (id : ℝ → ℝ)) _ _
  simpa only [fullBallInteriorMeasure, Measure.restrict_restrict hs, inter_self] using hp

/-- The actual volume identity for a compactly supported energy density. -/
theorem integral_fullBallInterior_product_eq_integral (ρ : ℝ)
    {J : Set ℝ} (F : Vec3 × ℝ → ℝ)
    (hF : ∀ z, z ∉ (fullBallCompactInterior ρ) ×ˢ J → F z = 0) :
    (∫ z : (fullBallCompactInterior ρ) × ℝ, F (z.1.1, z.2)
      ∂(fullBallInteriorMeasure ρ).prod (volume.restrict J)) = ∫ z : Vec3 × ℝ, F z := by
  have hs : MeasurableSet (fullBallCompactInterior ρ) :=
    (isClosed_closure : IsClosed (fullBallCompactInterior ρ)).measurableSet
  have he : MeasurableEmbedding
      (fun z : (fullBallCompactInterior ρ) × ℝ ↦ (z.1.1, z.2)) :=
    (MeasurableEmbedding.subtype_coe hs).prodMap
      (MeasurableEmbedding.id : MeasurableEmbedding (id : ℝ → ℝ))
  have h := (fullBallInterior_product_measurePreserving ρ J).integral_comp he F
  rw [h, Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hF

/-- Pulling back by the genuine compact inclusion preserves ambient Lᵖ membership exactly. -/
theorem memLp_fullBallInterior_ambient_iff (ρ : ℝ) {E : Type*} [NormedAddCommGroup E]
    (v : Vec3 → E) (P : ℝ≥0∞) :
    MemLp v P (volume.restrict (fullBallCompactInterior ρ)) ↔
      MemLp (fun x : (fullBallCompactInterior ρ) ↦ v x.1) P (fullBallInteriorMeasure ρ) := by
  have he : MeasurableEmbedding (Subtype.val : (fullBallCompactInterior ρ) → Vec3) :=
    MeasurableEmbedding.subtype_coe
      (isClosed_closure : IsClosed (fullBallCompactInterior ρ)).measurableSet
  rw [← (fullBallInterior_measurePreserving ρ).map_eq]
  exact he.memLp_map_measure_iff

/-- Genuine inclusion of the compact product preserves actual joint Lᵖ membership. -/
theorem memLp_fullBallInterior_product_ambient_iff (ρ : ℝ) {E : Type*} [NormedAddCommGroup E]
    (v : ParabolicPoint → E) (P : ℝ≥0∞) (J : Set ℝ) :
    MemLp v P (volume.restrict ((fullBallCompactInterior ρ) ×ˢ J)) ↔
      MemLp (fun z : (fullBallCompactInterior ρ) × ℝ ↦ v (z.1.1, z.2)) P
        ((fullBallInteriorMeasure ρ).prod (volume.restrict J)) := by
  have he : MeasurableEmbedding
      (fun z : (fullBallCompactInterior ρ) × ℝ ↦ (z.1.1, z.2)) :=
    (MeasurableEmbedding.subtype_coe
      (isClosed_closure : IsClosed (fullBallCompactInterior ρ)).measurableSet).prodMap
      (MeasurableEmbedding.id : MeasurableEmbedding (id : ℝ → ℝ))
  rw [volume_parabolicPoint_eq_prod, ← Measure.prod_restrict,
    ← (fullBallInterior_product_measurePreserving ρ J).map_eq]
  exact he.memLp_map_measure_iff

/-- Actual suitable data give all three compact-interior joint classes. -/
theorem fullBallProjected_memLp
    {Ω : Set Vec3} {I : Set ℝ} {q a b ρ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b)
    (hρ : 0 < ρ) (hρone : ρ < 1) :
    MemLp (fun z : (fullBallCompactInterior ρ) × ℝ ↦ u (z.1.1, z.2)) 3
      ((fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) ∧
      MemLp (fun z : (fullBallCompactInterior ρ) × ℝ ↦ Du (z.1.1, z.2)) 2
        ((fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) ∧
      MemLp (fun z : (fullBallCompactInterior ρ) × ℝ ↦ p (z.1.1, z.2))
        (ENNReal.ofReal (3 / 2 : ℝ))
        ((fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) := by
  let J := Ioo a b
  let S : Set ParabolicPoint := (fullBallCompactInterior ρ) ×ˢ Icc a b
  have hS : IsCompact S := parabolicHomeomorph.isCompact_preimage.mpr
    ((isCompact_closure_vec3Ball hρ).prod isCompact_Icc)
  have hSdom : S ⊆ spaceTimeSet Ω I := by
    intro z hz
    refine ⟨hbox.2.2.1 (subset_closure ?_), hbox.2.2.2.2.2 ?_⟩
    · exact fullBallCompactInterior_subset_unit hρ hρone hz.1
    · rw [closure_Ioo hab.ne]
      exact hz.2
  have hu : MemLp u 3 (volume.restrict S) := by
    simpa using velocity_memLp_three_on_compact_of_data hsol.toData hS hSdom
  have hd := gradient_memLp_two_on_compact_of_data hsol.toData hS hSdom
  have hp := pressure_memLp_threeHalves_on_compact_of_data hsol.toData hS hSdom
  have hsub : (fullBallCompactInterior ρ) ×ˢ J ⊆ S :=
    prod_mono le_rfl Ioo_subset_Icc_self
  have hUP : MemLp (fun z : Vec3 × ℝ ↦ u z) 3
      ((volume.restrict (fullBallCompactInterior ρ)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict,
      ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact hu.mono_measure (Measure.restrict_mono_set volume hsub)
  have hDP : MemLp (fun z : Vec3 × ℝ ↦ Du z) 2
      ((volume.restrict (fullBallCompactInterior ρ)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict,
      ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact hd.mono_measure (Measure.restrict_mono_set volume hsub)
  have hPP : MemLp (fun z : Vec3 × ℝ ↦ p z) (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume.restrict (fullBallCompactInterior ρ)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict,
      ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact hp.mono_measure (Measure.restrict_mono_set volume hsub)
  exact ⟨hUP.comp_measurePreserving (fullBallInterior_product_measurePreserving ρ J),
    hDP.comp_measurePreserving (fullBallInterior_product_measurePreserving ρ J),
    hPP.comp_measurePreserving (fullBallInterior_product_measurePreserving ρ J)⟩

/-- The actual original slice energy gives the compact velocity time class. -/
theorem fullBallProjected_velocity_slice_data
    {Ω : Set Vec3} {I : Set ℝ} {q a b ρ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b)
    (hρ : 0 < ρ) (hρone : ρ < 1) :
    (∀ᵐ t ∂volume.restrict (Ioo a b),
      MemLp (fun x : (fullBallCompactInterior ρ) ↦ u (x.1, t)) 2
        (fullBallInteriorMeasure ρ)) ∧
      MemLp (actualSliceLp (μ := (fullBallInteriorMeasure ρ)) (p := 2)
        (fun z : (fullBallCompactInterior ρ) × ℝ ↦ u (z.1.1, z.2))) ⊤
        (volume.restrict (Ioo a b)) := by
  let J := Ioo a b
  have hsub : (fullBallCompactInterior ρ) ⊆ vec3Ball (0 : Vec3) 1 :=
    fullBallCompactInterior_subset_unit hρ hρone
  refine ⟨?_, ?_⟩
  · filter_upwards [slice_memLp_ae_of_sws hsol hbox] with t ht
    exact (ht.1.mono_measure (Measure.restrict_mono_set volume hsub)).comp_measurePreserving
      (fullBallInterior_measurePreserving ρ)
  · have hmeas := (fullBallProjected_memLp hsol hbox hab hρ hρone).1.aestronglyMeasurable
    apply actualSliceLp_memLp_top_of_sliceEnergy hmeas
    apply lt_of_le_of_lt _ (hsol.toData.essSup_sliceEnergy_lt_top hbox)
    refine essSup_mono_ae (ae_of_all _ fun t ↦ ?_)
    ·
      let ft : Vec3 → ℝ≥0∞ := fun x ↦ ‖u ((x, t) : ParabolicPoint)‖ₑ ^ (2 : ℝ)
      have hs : MeasurableSet (fullBallCompactInterior ρ) :=
        (isClosed_closure : IsClosed (fullBallCompactInterior ρ)).measurableSet
      have hm : (volume.restrict (fullBallCompactInterior ρ)).restrict
          (fullBallCompactInterior ρ) = volume.restrict (fullBallCompactInterior ρ) := by
        rw [Measure.restrict_restrict hs, inter_self]
      change (∫⁻ x : (fullBallCompactInterior ρ), ft x.1
        ∂(volume.restrict (fullBallCompactInterior ρ)).comap Subtype.val) ≤
          ∫⁻ x in vec3Ball 0 1, ft x
      calc
        _ = ∫⁻ x in (fullBallCompactInterior ρ), ft x
            ∂volume.restrict (fullBallCompactInterior ρ) := lintegral_subtype_comap hs ft
        _ = ∫⁻ x in (fullBallCompactInterior ρ), ft x :=
          congrArg (fun ρ : Measure Vec3 ↦ ∫⁻ x, ft x ∂ρ) hm
        _ ≤ _ := lintegral_mono_set hsub

end FluidSingularSets
