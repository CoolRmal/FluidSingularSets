module

public import FluidSingularSets.RegularSet
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Passing from compact interior localizations to the full singular set

An open domain has a countable compact interior cover. Nullity of every compact
localization therefore gives nullity of the whole set, also after applying the
map into parabolic coordinates.
-/

@[expose] public section

open Set MeasureTheory

noncomputable section

namespace FluidSingularSets

/-- An open subset of a second-countable locally compact space has a compact interior cover. -/
theorem exists_compact_interior_cover {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [LocallyCompactSpace X] {U : Set X} (hU : IsOpen U) :
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ U) ∧ ⋃ n, K n = U := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K : ℕ → Set X := fun n ↦ Subtype.val '' compactCovering U n
  refine ⟨K, (fun n ↦ (isCompact_compactCovering U n).image continuous_subtype_val),
    (fun n x hx ↦ by obtain ⟨y, _hy, rfl⟩ := hx; exact y.property), ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨n, y, _hy, rfl⟩ := mem_iUnion.mp hx
    exact y.property
  · intro hx
    have hcover : (⟨x, hx⟩ : U) ∈ ⋃ n, compactCovering U n := by
      rw [iUnion_compactCovering]
      exact mem_univ _
    obtain ⟨n, hn⟩ := mem_iUnion.mp hcover
    exact mem_iUnion.mpr ⟨n, ⟨⟨x, hx⟩, hn, rfl⟩⟩

/-- Compact interior image-nullity implies image-nullity on the full open domain. -/
theorem measure_image_zero_of_compact_localizations {X Y : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [MeasurableSpace Y] (μ : Measure Y) (f : X → Y) {U E : Set X}
    (hU : IsOpen U) (hEU : E ⊆ U)
    (hlocal : ∀ K : Set X, IsCompact K → K ⊆ U → μ (f '' (E ∩ K)) = 0) :
    μ (f '' E) = 0 := by
  obtain ⟨K, hK, hKU, hcover⟩ := exists_compact_interior_cover hU
  have hsub : f '' E ⊆ ⋃ n, f '' (E ∩ K n) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxU : x ∈ ⋃ n, K n := by rw [hcover]; exact hEU hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hxU
    exact mem_iUnion.mpr ⟨n, ⟨x, ⟨hx, hn⟩, rfl⟩⟩
  exact measure_mono_null hsub (measure_iUnion_null (fun n ↦ hlocal _ (hK n) (hKU n)))

end FluidSingularSets
