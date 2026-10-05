-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic

/-!
# Fischer coefficient pairing for the weighted ball operator

The factorial-weighted coefficient pairing is positive definite and makes
polynomial differentiation adjoint to multiplication by a coordinate. This
gives a genuine positive homogeneous principal block of the weighted ball
operator. No analytic divergence inverse or pressure estimate is assumed.
-/

@[expose] public section

open MvPolynomial Module
open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

abbrev BallPolynomial := MvPolynomial (Fin 3) ℝ

/-- The positive factorial weight of a polynomial multi-index. -/
def fischerWeight (α : Fin 3 →₀ ℕ) : ℝ :=
  ∏ i : Fin 3, (α i).factorial

theorem fischerWeight_pos (α : Fin 3 →₀ ℕ) : 0 < fischerWeight α := by
  apply Finset.prod_pos
  intro i _hi
  exact_mod_cast Nat.factorial_pos (α i)

/-- The actual bilinear coefficient form, constructed on the monomial basis. -/
def fischerForm : BallPolynomial →ₗ[ℝ] BallPolynomial →ₗ[ℝ] ℝ :=
  (basisMonomials (Fin 3) ℝ).constr ℝ
    (fun α ↦ fischerWeight α • lcoeff ℝ α)

/-- The factorial-weighted coefficient pairing of actual polynomials. -/
def fischerPair (p q : BallPolynomial) : ℝ := fischerForm p q

@[simp]
theorem fischerPair_add_left (p q r : BallPolynomial) :
    fischerPair (p + q) r = fischerPair p r + fischerPair q r := by
  simp [fischerPair]

@[simp]
theorem fischerPair_add_right (p q r : BallPolynomial) :
    fischerPair p (q + r) = fischerPair p q + fischerPair p r := by
  simp [fischerPair]

@[simp]
theorem fischerPair_smul_left (c : ℝ) (p q : BallPolynomial) :
    fischerPair (c • p) q = c * fischerPair p q := by
  simp [fischerPair]

@[simp]
theorem fischerPair_smul_right (c : ℝ) (p q : BallPolynomial) :
    fischerPair p (c • q) = c * fischerPair p q := by
  simp [fischerPair]

@[simp]
theorem fischerPair_zero_left (p : BallPolynomial) : fischerPair 0 p = 0 := by
  simp [fischerPair]

@[simp]
theorem fischerPair_zero_right (p : BallPolynomial) : fischerPair p 0 = 0 := by
  simp [fischerPair]

theorem fischerPair_monomial_left (α : Fin 3 →₀ ℕ) (c : ℝ) (q : BallPolynomial) :
    fischerPair (monomial α c) q = fischerWeight α * c * q.coeff α := by
  have hm : monomial α c = c • (basisMonomials (Fin 3) ℝ) α := by
    simp [coe_basisMonomials, smul_monomial]
  rw [hm, fischerPair_smul_left]
  change c * (((basisMonomials (Fin 3) ℝ).constr ℝ
    (fun α ↦ fischerWeight α • lcoeff ℝ α)) ((basisMonomials (Fin 3) ℝ) α)) q = _
  rw [Basis.constr_basis]
  simp only [LinearMap.smul_apply, lcoeff_apply, smul_eq_mul]
  ring

/-- The pairing has its literal coefficient-sum representation. -/
theorem fischerPair_eq_sum (p q : BallPolynomial) :
    fischerPair p q = ∑ α ∈ p.support, fischerWeight α * p.coeff α * q.coeff α := by
  classical
  change ((basisMonomials (Fin 3) ℝ).constr ℝ
    (fun α ↦ fischerWeight α • lcoeff ℝ α)) p q = _
  rw [Basis.constr_apply]
  simp only [basisMonomials, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply,
    lcoeff_apply, smul_eq_mul]
  change (∑ α ∈ p.support, p.coeff α * (fischerWeight α * q.coeff α)) = _
  apply Finset.sum_congr rfl
  intro α _hα
  ring

theorem fischerPair_comm (p q : BallPolynomial) : fischerPair p q = fischerPair q p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    induction q using MvPolynomial.induction_on' with
    | monomial β d =>
      rw [fischerPair_monomial_left, fischerPair_monomial_left]
      by_cases h : α = β
      · subst β
        simp [mul_comm, mul_left_comm]
      · simp [coeff_monomial, h, Ne.symm h]
    | add q r hq hr => simp [hq, hr]
  | add p q hp hq => simp [hp, hq]

theorem fischerPair_self_nonneg (p : BallPolynomial) : 0 ≤ fischerPair p p := by
  rw [fischerPair_eq_sum]
  apply Finset.sum_nonneg
  intro α _hα
  nlinarith [fischerWeight_pos α, sq_nonneg (p.coeff α)]

/-- The coefficient form is strictly positive on every nonzero actual polynomial. -/
theorem fischerPair_self_pos {p : BallPolynomial} (hp : p ≠ 0) :
    0 < fischerPair p p := by
  classical
  obtain ⟨α, hα⟩ := MvPolynomial.exists_coeff_ne_zero hp
  rw [fischerPair_eq_sum]
  apply Finset.sum_pos'
  · intro β _hβ
    nlinarith [fischerWeight_pos β, sq_nonneg (p.coeff β)]
  · refine ⟨α, mem_support_iff.mpr hα, ?_⟩
    have hsq : 0 < p.coeff α ^ 2 := sq_pos_of_ne_zero hα
    nlinarith [fischerWeight_pos α]

/-- Adding one coordinate multiplies its factorial weight by the new exponent. -/
theorem fischerWeight_add_single (α : Fin 3 →₀ ℕ) (i : Fin 3) :
    fischerWeight (α + Finsupp.single i 1) = fischerWeight α * (α i + 1) := by
  classical
  have h : ∀ j : Fin 3,
      ((((α + Finsupp.single i 1 : Fin 3 →₀ ℕ) j)).factorial : ℝ) =
        (α j).factorial * (if j = i then (α i : ℝ) + 1 else 1) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one, ite_true]
      ring
    · simp [hji]
  unfold fischerWeight
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp

/-- Differentiation is adjoint to coordinate multiplication in the genuine pairing. -/
theorem fischerPair_pderiv (p q : BallPolynomial) (i : Fin 3) :
    fischerPair (pderiv i p) q = fischerPair p (X i * q) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [pderiv_monomial, fischerPair_monomial_left, fischerPair_monomial_left,
      coeff_X_mul']
    by_cases hi : α i = 0
    · simp [hi, Finsupp.mem_support_iff]
    · have hmem : i ∈ α.support := Finsupp.mem_support_iff.mpr hi
      have hα : α = (α - Finsupp.single i 1) + Finsupp.single i 1 := by
        ext j
        by_cases hji : j = i
        · subst j
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        · simp [hji]
      have hw : fischerWeight α =
          fischerWeight (α - Finsupp.single i 1) * (α i : ℝ) := by
        conv_lhs => rw [hα]
        rw [fischerWeight_add_single]
        have hexp : (((α - Finsupp.single i 1 : Fin 3 →₀ ℕ) i) : ℝ) + 1 = α i := by
          simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
          have ha : α i - 1 + 1 = α i := by omega
          exact_mod_cast ha
        rw [hexp]
      simp only [ite_eq_left hmem, hw]
      ring
  | add p r hp hr => simp [hp, hr]

/-- The polynomial Euclidean Laplacian, defined using genuine polynomial derivatives. -/
def polynomialLaplacian : BallPolynomial →ₗ[ℝ] BallPolynomial :=
  ∑ i : Fin 3, (pderiv i).toLinearMap.comp (pderiv i).toLinearMap

/-- The literal squared radius polynomial. -/
def radiusSquaredPolynomial : BallPolynomial := ∑ i : Fin 3, X i ^ 2

theorem polynomialLaplacian_apply (p : BallPolynomial) :
    polynomialLaplacian p = ∑ i : Fin 3, pderiv i (pderiv i p) := by
  simp [polynomialLaplacian]

theorem fischerPair_polynomialLaplacian (p q : BallPolynomial) :
    fischerPair (polynomialLaplacian p) q =
      fischerPair p (radiusSquaredPolynomial * q) := by
  rw [polynomialLaplacian_apply]
  change (fischerForm (∑ i : Fin 3, pderiv i (pderiv i p))) q = _
  rw [map_sum, LinearMap.sum_apply]
  change (∑ i : Fin 3, fischerPair (pderiv i (pderiv i p)) q) = _
  simp only [fischerPair_pderiv]
  simp only [radiusSquaredPolynomial, Finset.sum_mul]
  change _ = fischerForm p (∑ i : Fin 3, X i ^ 2 * q)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [pow_two, mul_assoc]
  rfl

/-- The nonnegative part of the principal block is literally a Laplacian square. -/
theorem fischerPair_radiusSquared_laplacian (p : BallPolynomial) :
    fischerPair p (radiusSquaredPolynomial * polynomialLaplacian p) =
      fischerPair (polynomialLaplacian p) (polynomialLaplacian p) :=
  (fischerPair_polynomialLaplacian p (polynomialLaplacian p)).symm

/-- The actual principal block on homogeneous degree `n`. -/
def ballPrincipalBlock (n : ℕ) : BallPolynomial →ₗ[ℝ] BallPolynomial :=
  (LinearMap.mulLeft ℝ radiusSquaredPolynomial).comp polynomialLaplacian +
    (2 * (n : ℝ)) • LinearMap.id

theorem ballPrincipalBlock_apply (n : ℕ) (p : BallPolynomial) :
    ballPrincipalBlock n p = radiusSquaredPolynomial * polynomialLaplacian p +
      (2 * (n : ℝ)) • p := by
  simp [ballPrincipalBlock]

/-- Strict positivity follows from the actual factorial coefficient pairing. -/
theorem fischerPair_ballPrincipalBlock_pos {n : ℕ} (hn : 0 < n)
    {p : BallPolynomial} (hp : p ≠ 0) :
    0 < fischerPair p (ballPrincipalBlock n p) := by
  rw [ballPrincipalBlock_apply, fischerPair_add_right, fischerPair_smul_right,
    fischerPair_radiusSquared_laplacian]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith [fischerPair_self_nonneg (polynomialLaplacian p), fischerPair_self_pos hp]

/-- Every positive-degree principal block is injective, without an analytic premise. -/
theorem ballPrincipalBlock_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (ballPrincipalBlock n) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro p hp
  by_contra hne
  have hpos := fischerPair_ballPrincipalBlock_pos hn hne
  rw [hp, fischerPair_zero_right] at hpos
  exact (lt_irrefl 0) hpos

/-- Polynomial differentiation annihilates every homogeneous constant polynomial. -/
theorem pderiv_eq_zero_of_homogeneous_zero {p : BallPolynomial}
    (hp : p.IsHomogeneous 0) (i : Fin 3) : pderiv i p = 0 := by
  have hc := totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hp)
  rw [hc, pderiv_C]

/-- The actual Laplacian lowers homogeneous degree by two. -/
theorem polynomialLaplacian_isHomogeneous {p : BallPolynomial} {n : ℕ}
    (hp : p.IsHomogeneous n) : (polynomialLaplacian p).IsHomogeneous (n - 2) := by
  rw [polynomialLaplacian_apply]
  apply IsHomogeneous.sum
  intro i _hi
  simpa only [Nat.sub_sub] using (hp.pderiv (i := i)).pderiv (i := i)

theorem polynomialLaplacian_eq_zero_of_degree_le_one {p : BallPolynomial} {n : ℕ}
    (hp : p.IsHomogeneous n) (hn : n ≤ 1) : polynomialLaplacian p = 0 := by
  rw [polynomialLaplacian_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  apply pderiv_eq_zero_of_homogeneous_zero
  simpa only [Nat.sub_eq_zero_of_le hn] using hp.pderiv (i := i)

theorem radiusSquaredPolynomial_isHomogeneous : radiusSquaredPolynomial.IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _hi
  simpa using (isHomogeneous_X (R := ℝ) i).pow 2

/-- The genuine positive principal block preserves its finite homogeneous space. -/
theorem ballPrincipalBlock_isHomogeneous {p : BallPolynomial} {n : ℕ}
    (hp : p.IsHomogeneous n) : (ballPrincipalBlock n p).IsHomogeneous n := by
  rw [ballPrincipalBlock_apply]
  apply IsHomogeneous.add
  · by_cases hn : 2 ≤ n
    · have h := radiusSquaredPolynomial_isHomogeneous.mul
        (polynomialLaplacian_isHomogeneous hp)
      simpa only [Nat.add_sub_of_le hn] using h
    · rw [polynomialLaplacian_eq_zero_of_degree_le_one hp (by omega), mul_zero]
      exact isHomogeneous_zero (Fin 3) ℝ n
  · exact (homogeneousSubmodule (Fin 3) ℝ n).smul_mem _ hp

/-- The actual principal block acting on its homogeneous polynomial space. -/
def homogeneousBallPrincipalBlock (n : ℕ) :
    homogeneousSubmodule (Fin 3) ℝ n →ₗ[ℝ] homogeneousSubmodule (Fin 3) ℝ n :=
  (ballPrincipalBlock n).restrict fun _ hp ↦ ballPrincipalBlock_isHomogeneous hp

/-- Genuine finite-dimensional inversion of every positive homogeneous block. -/
theorem exists_homogeneousBallPrincipalBlock_inverse {n : ℕ} (hn : 0 < n)
    {f : BallPolynomial} (hf : f.IsHomogeneous n) :
    ∃ v : BallPolynomial, v.IsHomogeneous n ∧ ballPrincipalBlock n v = f := by
  let : Module.Finite ℝ (homogeneousSubmodule (Fin 3) ℝ n) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 3) ℝ n)
  have hinj : Function.Injective (homogeneousBallPrincipalBlock n) := by
    intro p q hpq
    apply Subtype.ext
    apply ballPrincipalBlock_injective hn
    exact congrArg Subtype.val hpq
  obtain ⟨v, hv⟩ := LinearMap.surjective_of_injective hinj ⟨f, hf⟩
  exact ⟨v, v.property, congrArg Subtype.val hv⟩

end FluidSingularSets
