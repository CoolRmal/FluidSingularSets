-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.EndpointOriginRegularity
public import FluidSingularSets.EndpointRegularGeometry
public import FluidSingularSets.EndpointVelocityCostRescaling

/-!
# A genuine uniform velocity-only interior criterion

The actual native origin theorem applies to every fixed quarter-box about a
closed inner point. Physical rescaling and compact regularity then give an
essential bound on the radius-one-eighth inner cylinder. Its radius and the
source threshold are independent of the solution and terminal time.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Actual endpoint regularity discharges the universal analytic input for box counting. -/
theorem exists_uniform_velocity_only_interior_criterion (q : ℝ) (hq : 5 / 2 < q) :
    ∃ κ : ℝ, 0 < κ ∧ UniformVelocityOnlyInteriorCriterion q κ := by
  obtain ⟨ε, hε, horigin⟩ := exists_native_endpoint_origin_regular_threshold q hq
  refine ⟨ε / 4, by positivity, ?_⟩
  intro B _
  refine ⟨1 / 8, by norm_num, by norm_num, ?_⟩
  intro Ω I v Dv p hsol t r hr hdom hcost _
  have hs := suitable_unforced_rescale hsol (0, t) hr
  have hb := localBox_endpoint_unit_rescaled hr hdom
  have hx : velocityCylinderSixMoment (rescaleVelocity r (0, t) v) 1 ≤
      ENNReal.ofReal (ε / 4) :=
    (suitable_endpoint_rescaled_six_moment_le_velocity_cost hsol hr hdom).trans hcost.le
  apply endpoint_physical_inner_bound_of_native_regular hr (0, t)
  intro z hz
  exact endpoint_inner_regular_of_origin_threshold horigin hs hb hx hz

end FluidSingularSets
