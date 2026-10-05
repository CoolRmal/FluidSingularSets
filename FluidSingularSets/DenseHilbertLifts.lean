-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Extending genuine bounded Hilbert lifts from dense data

Orthogonal projection off the actual operator kernel selects the minimal-norm
lift linearly on the range. Genuine bounded lifts on a dense data subspace
therefore extend to a continuous linear right inverse on the full target.
No closed-range or arbitrary-data preimage premise is used.
-/

@[expose] public section

open Set Filter
open scoped Topology NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private instance kernel_hasOrthogonalProjection (D : E →L[ℝ] F) :
    (D.ker).HasOrthogonalProjection := by
  let K : ClosedSubmodule ℝ E := ⟨D.ker, D.isClosed_ker⟩
  exact inferInstanceAs K.HasOrthogonalProjection

/-- The actual kernel-orthogonal algebraic lift on the operator range. -/
def orthogonalRangeLift (D : E →L[ℝ] F) : D.range →ₗ[ℝ] E :=
  ((D.ker)ᗮ.subtype.comp (D.ker).quotientEquivOrthogonal.toLinearMap).comp
    D.toLinearMap.quotKerEquivRange.symm.toLinearMap

/-- On any genuine image, the orthogonal lift is no larger than its preimage. -/
theorem orthogonalRangeLift_norm_le (D : E →L[ℝ] F) (v : E) :
    ‖orthogonalRangeLift D ⟨D v, D.toLinearMap.mem_range_self v⟩‖ ≤ ‖v‖ := by
  unfold orthogonalRangeLift
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  change ‖((D.ker).quotientEquivOrthogonal
    (D.toLinearMap.quotKerEquivRange.symm
      ⟨D.toLinearMap v, D.toLinearMap.mem_range_self v⟩) : E)‖ ≤ ‖v‖
  rw [D.toLinearMap.quotKerEquivRange_symm_apply_image]
  change ‖(D.ker).quotientEquivOrthogonal (Submodule.Quotient.mk v)‖ ≤ ‖v‖
  rw [(D.ker).quotientEquivOrthogonal.norm_map]
  exact Submodule.Quotient.norm_mk_le D.ker v

/-- The constructed orthogonal lift really maps back to the actual datum. -/
theorem orthogonalRangeLift_apply (D : E →L[ℝ] F) (g : D.range) :
    D (orthogonalRangeLift D g) = g.1 := by
  let w := (D.ker).quotientEquivOrthogonal
    (D.toLinearMap.quotKerEquivRange.symm g)
  have hmk : Submodule.Quotient.mk (w : E) = D.toLinearMap.quotKerEquivRange.symm g := by
    calc
      _ = (D.ker).quotientEquivOrthogonal.symm w :=
        ((D.ker).quotientEquivOrthogonal_symm_eq_mk w w.2).symm
      _ = _ := (D.ker).quotientEquivOrthogonal.symm_apply_apply _
  have himg := congrArg D.toLinearMap.quotKerEquivRange hmk
  have himgval := congrArg Subtype.val himg
  rw [D.toLinearMap.quotKerEquivRange_apply_mk,
    D.toLinearMap.quotKerEquivRange.apply_symm_apply] at himgval
  exact himgval

/-- A bounded actual lift on dense data extends to a bounded continuous linear
right inverse. The source is Hilbert; the target need not be Hilbert. -/
theorem exists_bounded_rightInverse_of_dense_lifts
    (D : E →L[ℝ] F) (P : Submodule ℝ F) (hP : Dense (P : Set F))
    {C : ℝ} (hC : 0 ≤ C)
    (hlift : ∀ g : P, ∃ v : E, D v = g.1 ∧ ‖v‖ ≤ C * ‖g‖) :
    ∃ T : F →L[ℝ] E, D.comp T = ContinuousLinearMap.id ℝ F ∧ ‖T‖ ≤ C := by
  have hPrange : P ≤ D.range := by
    intro g hg
    obtain ⟨v, hv, _⟩ := hlift ⟨g, hg⟩
    exact ⟨v, hv⟩
  let i : P →ₗ[ℝ] D.range := P.subtype.codRestrict D.range (fun g ↦ hPrange g.2)
  let L : P →ₗ[ℝ] E := (orthogonalRangeLift D).comp i
  have hLbound (g : P) : ‖L g‖ ≤ C * ‖g‖ := by
    obtain ⟨v, hv, hvnorm⟩ := hlift g
    have hi : i g = ⟨D v, D.toLinearMap.mem_range_self v⟩ := Subtype.ext hv.symm
    change ‖orthogonalRangeLift D (i g)‖ ≤ C * ‖g‖
    rw [hi]
    exact (orthogonalRangeLift_norm_le D v).trans hvnorm
  have hLimage (g : P) : D (L g) = g.1 := orthogonalRangeLift_apply D (i g)
  let Lc : P →L[ℝ] E := L.mkContinuous C hLbound
  have hLnorm : ‖Lc‖ ≤ C := L.mkContinuous_norm_le hC hLbound
  have hdense : DenseRange P.subtypeL := by simpa using hP
  have hinduce : IsUniformInducing P.subtypeL := isometry_subtype_coe.isUniformInducing
  let T : F →L[ℝ] E := Lc.extend P.subtypeL
  have hTtest (g : P) : T g = L g := Lc.extend_eq hdense hinduce g
  refine ⟨T, ?_, ?_⟩
  · apply DFunLike.coe_injective
    apply hdense.equalizer (D.comp T).continuous (ContinuousLinearMap.id ℝ F).continuous
    funext g
    change D (T g) = g.1
    rw [hTtest]
    exact hLimage g
  · calc
      ‖T‖ ≤ (1 : ℝ≥0) * ‖Lc‖ :=
        Lc.opNorm_extend_le hdense (N := 1) (fun g ↦ by simp)
      _ = ‖Lc‖ := by simp
      _ ≤ C := hLnorm

end

end FluidSingularSets
