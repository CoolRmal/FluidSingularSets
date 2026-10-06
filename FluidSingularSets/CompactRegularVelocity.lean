-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.AcceleratedRegularity
public import Mathlib.Order.Filter.Finite

/-!
# A common actual velocity bound on compact regular sets

The genuine CKN Hölder representative gives a local essential bound at each
regular point. A finite open subcover supplies a common bound on the entire
compact set. The simultaneous almost-everywhere argument is finite and does
not presume that individual regular neighborhoods have a uniform radius.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Genuine regularity at every point of a compact set gives one actual essential velocity bound. -/
theorem compact_ae_velocity_bound_of_regular_points
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3} {K : Set ParabolicPoint}
    (hK : IsCompact K) (hreg : ∀ z ∈ K, CKN.IsRegularPoint Ω I u z) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ z ∂volume.restrict K, vec3EuclideanNorm (u z) ≤ A := by
  classical
  have hlocal : ∀ z : K, HasLocalAEVelocityBound u z.1 :=
    fun z ↦ regular_has_local_ae_velocity_bound (hreg z.1 z.2)
  choose U hU hzU A hA hbound using hlocal
  have hcover : K ⊆ ⋃ z : K, U z := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, hzU ⟨z, hz⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU hcover
  have hdiag : ∀ᵐ w : ParabolicPoint ∂volume,
      ∀ z ∈ s, w ∈ U z → vec3EuclideanNorm (u w) ≤ A z := by
    apply s.eventually_all.mpr
    intro z _
    exact (ae_restrict_iff' (hU z).measurableSet).mp (hbound z)
  refine ⟨∑ z ∈ s, A z, Finset.sum_nonneg (fun z _ ↦ hA z), ?_⟩
  filter_upwards [hdiag.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem hK.measurableSet] with w hw hwK
  obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.mp (hs hwK)
  exact (hw z hz hwz).trans (Finset.single_le_sum (fun y _ ↦ hA y) hz)

end FluidSingularSets
