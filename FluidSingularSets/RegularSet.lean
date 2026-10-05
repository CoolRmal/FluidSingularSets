module

public import FluidSingularSets.CKNBridge

/-! # Topological properties of the independently stated singular set -/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace FluidSingularSets

/-- Having a local Hölder representative is an open condition in the base point. -/
theorem isOpen_holderRegularSet
    {X Y : Type*} [PseudoEMetricSpace X] [MeasureSpace X]
    [SeminormedAddCommGroup Y] (u : X → Y) :
    IsOpen {x | CKNChallenge.IsHolderRegularPoint u x} := by
  apply isOpen_iff_mem_nhds.2
  intro x hx
  obtain ⟨U, hU, hxU, γ, hγpos, hγle, hnorm⟩ := hx
  apply Filter.mem_of_superset (hU.mem_nhds hxU)
  intro y hy
  exact ⟨U, hU, hy, γ, hγpos, hγle, hnorm⟩

/-- The singular set is measurable on an open space-time product domain. -/
theorem measurableSet_singularSet
    {Ω : Set (EuclideanSpace ℝ (Fin 3))} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (u : EuclideanSpace ℝ (Fin 3) × ℝ →
      EuclideanSpace ℝ (Fin 3)) :
    MeasurableSet (CKNChallenge.singularSet Ω I u) := by
  change MeasurableSet ((Ω ×ˢ I) ∩ {z | ¬CKNChallenge.IsHolderRegularPoint u z})
  exact (hΩ.prod hI).measurableSet.inter (isOpen_holderRegularSet u).measurableSet.compl

/-- Compact interior localizations of the singular set are compact. -/
theorem isCompact_singularSet_inter
    {Ω : Set (EuclideanSpace ℝ (Fin 3))} {I : Set ℝ}
    (u : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3))
    {K : Set (EuclideanSpace ℝ (Fin 3) × ℝ)} (hK : IsCompact K) (hsub : K ⊆ Ω ×ˢ I) :
    IsCompact (CKNChallenge.singularSet Ω I u ∩ K) := by
  have heq : CKNChallenge.singularSet Ω I u ∩ K =
      {z | ¬CKNChallenge.IsHolderRegularPoint u z} ∩ K := by
    ext z
    constructor
    · exact fun hz ↦ ⟨hz.1.2, hz.2⟩
    · exact fun hz ↦ ⟨⟨hsub hz.2, hz.1⟩, hz.2⟩
  rw [heq]
  exact hK.inter_left (isOpen_holderRegularSet u).isClosed_compl

end FluidSingularSets
