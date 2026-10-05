-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.AcceleratedLpStability
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A compact limit tube inside an open domain has a common compact interior
buffer containing all sufficiently late approximating tubes. The only
convergence hypothesis is uniform path convergence on its time interval. -/
theorem exists_compact_common_moving_tube
    {α : Type*} {l : Filter α} {Xs : α → ℝ → Vec3} {X : ℝ → Vec3}
    (hX : Continuous X) {a b : ℝ}
    (hconv : TendstoUniformlyOn Xs X l (Icc a b))
    {S D : Set (Vec3 × ℝ)} (hS : IsCompact S) (hD : IsOpen D)
    (hStime : ∀ z ∈ S, z.2 ∈ Icc a b)
    (himage : acceleratedFrameMapProd X '' S ⊆ D) :
    ∃ K : Set (Vec3 × ℝ), IsCompact K ∧ K ⊆ D ∧
      acceleratedFrameMapProd X '' S ⊆ K ∧
        ∀ᶠ n in l, acceleratedFrameMapProd (Xs n) '' S ⊆ K := by
  let T := acceleratedFrameMapProd X '' S
  have hT : IsCompact T := hS.image (acceleratedFrameHomeomorph X hX).continuous
  obtain ⟨δ, hδ, hbuffer⟩ := hT.exists_cthickening_subset_open hD himage
  refine ⟨Metric.cthickening δ T, hT.cthickening, hbuffer,
    Metric.self_subset_cthickening T, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv δ hδ] with n hn
  rintro z ⟨w, hw, rfl⟩
  apply Metric.mem_cthickening_of_dist_le
    (acceleratedFrameMapProd (Xs n) w) (acceleratedFrameMapProd X w) δ T
    ⟨w, hw, rfl⟩
  have h := hn w.2 (hStime w hw)
  have hd : dist (acceleratedFrameMapProd (Xs n) w) (acceleratedFrameMapProd X w) =
      dist (X w.2) (Xs n w.2) := by
    simp [acceleratedFrameMapProd, Prod.dist_eq, dist_add_right, dist_comm]
  rw [hd]
  exact h.le

end FluidSingularSets
