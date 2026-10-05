module

public import FluidSingularSets.GaugeTraceExclusion
public import FluidSingularSets.LocalizedGradientPatch

/-!
# Compact nullity from actual suitable persistence

A positive compact gauge measure produces a genuine supported Frostman
probability measure. The solution supplies a compact finite-energy gradient
patch. The proved recurrence and trace exclude every persistent point of that
patch, contradicting its Frostman mass one.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- Every compact interior persistent set of an actual unforced suitable solution
has zero measure for every positive finite-depth iterated logarithmic gauge. -/
theorem compact_persistent_set_iteratedLogGauge_null
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (k : ℕ) {E : Set ParabolicPoint} (hE : IsCompact E)
    (hEdom : E ⊆ CKN.spaceTimeSet Ω I) {ε : ℝ} (hε : 0 < ε)
    (hpersistent : ∀ z ∈ E, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      ε ≤ rawSymmetricL3Activity u p z r ∧
        closure (rawSymmetricL3Cylinder z r) ⊆ CKN.spaceTimeSet Ω I) :
    (Measure.mkMetric (iteratedLogGauge (k + 1)) : Measure ParabolicPoint) E = 0 := by
  by_contra hnonzero
  have hpos : 0 < (Measure.mkMetric (iteratedLogGauge (k + 1)) : Measure ParabolicPoint) E :=
    bot_lt_iff_ne_bot.2 hnonzero
  obtain ⟨μ, C, r₀, hμfinite, _, _, hμE, hC, hr₀, hgrowth⟩ :=
    exists_iteratedLogGauge_frostman_measure (k + 1) E hE hpos
  have : IsFiniteMeasure μ := hμfinite
  obtain ⟨ρ, hρ, _, _, hdouble⟩ := exists_iteratedLogGauge_frostman_radius (k + 1)
  obtain ⟨S, _, _, _, _, _, hD, henergy, _, _, hcells⟩ :=
    exists_suitable_compact_gradient_patch hsol hE hEdom
  have hnull := suitable_persistent_set_frostman_null hsol μ k hC hr₀ hρ hε
    hgrowth hdouble (S.indicator Du) hD henergy E (fun z hz ↦ by
      obtain ⟨R₁, hR₁, hper⟩ := hpersistent z hz
      obtain ⟨R₂, hR₂, hsmall⟩ := hcells z hz
      refine ⟨min R₁ R₂, lt_min hR₁ hR₂, fun r hr hR ↦ ?_⟩
      obtain ⟨hcharge, hdom⟩ := hper r hr (hR.trans (min_le_left _ _))
      refine ⟨hcharge, hdom, fun g Q hside hzQ a ha ↦ ?_⟩
      exact Set.indicator_of_mem
        (hsmall g Q r hr (hR.trans (min_le_right _ _)) hside hzQ ha) Du)
  rw [hnull] at hμE
  exact zero_ne_one hμE

end FluidSingularSets
