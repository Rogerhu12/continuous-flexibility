module

public import ContinuousFlexibility.Radial.InnerRadialPoisson
public import ContinuousFlexibility.Radial.InnerRadialGreen
public import ContinuousFlexibility.Statements.RadialTargets
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FinCases

/-!
# The actual Poisson and Dirichlet-to-Neumann maps of a positive gap

The two columns are genuine solutions of the radial divergence-form
equation, constructed from conormal-flux initial data. Their linear
combination is the continuous linear Poisson map on the two-dimensional
Euclidean boundary space. Its flux matrix uses the actual outward signs.

The radial Green identity proves symmetry, and the radial energy proves
positive semidefiniteness and the quantitative mass estimate. None of
these properties is assumed of the boundary matrix. The full two by two
matrix, including both off-diagonal entries, is retained.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

/-- The two retained endpoints, in the existing left/right convention. -/
def innerGapEndpoint (a b : ℝ) (i : Fin 2) : ℝ := if i = 0 then a else b

@[simp] theorem innerGapEndpoint_zero (a b : ℝ) : innerGapEndpoint a b 0 = a := by
  simp [innerGapEndpoint]

@[simp] theorem innerGapEndpoint_one (a b : ℝ) : innerGapEndpoint a b 1 = b := by
  norm_num [innerGapEndpoint]

/-- The actual two-column Poisson map. Its function-space target carries
the pointwise topology; the physical mass estimate is proved below. -/
def innerGapPoisson (p : Fin 2 → ℝ → ℝ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] (ℝ → ℝ) := by
  let L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] (ℝ → ℝ) :=
    { toFun := fun ξ r => ξ 0 * p 0 r + ξ 1 * p 1 r
      map_add' := by
        intro ξ η
        funext r
        simp only [PiLp.add_apply, Pi.add_apply]
        ring
      map_smul' := by
        intro c ξ
        funext r
        simp only [PiLp.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  exact ⟨L, L.continuous_of_finiteDimensional⟩

theorem innerGapPoisson_two (p : Fin 2 → ℝ → ℝ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    innerGapPoisson p ξ = fun r => ξ 0 * p 0 r + ξ 1 * p 1 r := rfl

theorem innerGapPoisson_apply (p : Fin 2 → ℝ → ℝ)
    (ξ : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    innerGapPoisson p ξ r = ∑ i : Fin 2, ξ i * p i r := by
  rw [Fin.sum_univ_two]
  rfl

theorem innerGapPoisson_contDiff (p : Fin 2 → ℝ → ℝ)
    (hp : ∀ i, ContDiff ℝ ∞ (p i)) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ContDiff ℝ ∞ (innerGapPoisson p ξ) := by
  rw [innerGapPoisson_two]
  exact (contDiff_const.mul (hp 0)).add (contDiff_const.mul (hp 1))

theorem innerGapPoisson_deriv (p : Fin 2 → ℝ → ℝ)
    (hp : ∀ i, ContDiff ℝ ∞ (p i)) (ξ : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    deriv (innerGapPoisson p ξ) r = ∑ i : Fin 2, ξ i * deriv (p i) r := by
  rw [innerGapPoisson_two, Fin.sum_univ_two]
  exact ((((hp 0).differentiable (by simp) r).hasDerivAt.const_mul (ξ 0)).fun_add
    (((hp 1).differentiable (by simp) r).hasDerivAt.const_mul (ξ 1))).deriv

theorem innerGapPoisson_homogeneous {a b j : ℝ} {w : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (p : Fin 2 → ℝ → ℝ)
    (hp : ∀ i, ContDiff ℝ ∞ (p i))
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) w (p i) r = 0)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∀ r ∈ Icc a b, radialJacobi (j ^ 2) w (innerGapPoisson p ξ) r = 0 := by
  intro r hr
  rw [innerGapPoisson_two, innerRadialJacobi_linear_combination hw (hp 0) (hp 1),
    heq 0 r hr, heq 1 r hr, mul_zero, mul_zero, add_zero]

theorem innerGapPoisson_boundary {a b : ℝ} (p : Fin 2 → ℝ → ℝ)
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (ξ : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    innerGapPoisson p ξ (innerGapEndpoint a b i) = ξ i := by
  simp [innerGapPoisson_apply, hb]

/-- The column construction is the unique physical Poisson solution on
the retained closed interval, independently of its smooth extension. -/
theorem innerGapPoisson_eqOn {a b j : ℝ} (hab : a < b) (ha : 0 < a)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (p : Fin 2 → ℝ → ℝ)
    (hp : ∀ i, ContDiff ℝ ∞ (p i))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) w (p i) r = 0)
    (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv w r / w r)
    (ξ : EuclideanSpace ℝ (Fin 2)) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (huEq : ∀ r ∈ Icc a b, radialJacobi (j ^ 2) w u r = 0)
    (htrace : ∀ i, u (innerGapEndpoint a b i) = ξ i) :
    EqOn (innerGapPoisson p ξ) u (Icc a b) := by
  apply innerRadialGap_boundary_unique hab ha hw (innerGapPoisson_contDiff p hp ξ)
    hu hpos hslope (innerGapPoisson_homogeneous hw p hp heq ξ) huEq
  · simpa only [innerGapEndpoint_zero] using
      (innerGapPoisson_boundary p hb ξ 0).trans (htrace 0).symm
  · simpa only [innerGapEndpoint_one] using
      (innerGapPoisson_boundary p hb ξ 1).trans (htrace 1).symm

/-- The full actual outward conormal derivative matrix. -/
def innerGapFluxMatrix (w : ℝ → ℝ) (a b : ℝ) (p : Fin 2 → ℝ → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i k => Statements.bufferSign i * w (innerGapEndpoint a b i) *
    deriv (p k) (innerGapEndpoint a b i)

/-- The same matrix acting on the Euclidean boundary Hilbert space. -/
def innerGapFluxOperator (w : ℝ → ℝ) (a b : ℝ) (p : Fin 2 → ℝ → ℝ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (innerGapFluxMatrix w a b p)

theorem innerGapFluxOperator_apply (w : ℝ → ℝ) (a b : ℝ)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (ξ : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    innerGapFluxOperator w a b p ξ i =
      Statements.bufferSign i * w (innerGapEndpoint a b i) *
        deriv (innerGapPoisson p ξ) (innerGapEndpoint a b i) := by
  have h := congrArg (fun v : Fin 2 → ℝ => v i)
    (Matrix.ofLp_toEuclideanCLM (innerGapFluxMatrix w a b p) ξ)
  calc
    innerGapFluxOperator w a b p ξ i =
        ∑ k : Fin 2, innerGapFluxMatrix w a b p i k * ξ k := by
      simpa only [innerGapFluxOperator, Matrix.mulVec_apply_eq_sum] using h
    _ = _ := by
      rw [innerGapPoisson_deriv p hp]
      simp only [innerGapFluxMatrix, Fin.sum_univ_two]
      ring

theorem innerGapFluxOperator_pairing (w : ℝ → ℝ) (a b : ℝ)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (ξ η : EuclideanSpace ℝ (Fin 2)) :
    ⟪η, innerGapFluxOperator w a b p ξ⟫_ℝ =
      η 1 * (w b * deriv (innerGapPoisson p ξ) b) -
        η 0 * (w a * deriv (innerGapPoisson p ξ) a) := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, innerGapFluxOperator_apply w a b p hp,
    innerGapEndpoint, Statements.bufferSign] <;> ring

theorem innerGapPoisson_boundary_pairing {a b : ℝ} (w : ℝ → ℝ)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    innerRadialGapBoundary w (innerGapPoisson p ξ) a b =
      ⟪ξ, innerGapFluxOperator w a b p ξ⟫_ℝ := by
  have h0 := innerGapPoisson_boundary p hb ξ 0
  have h1 := innerGapPoisson_boundary p hb ξ 1
  simp only [innerGapEndpoint_zero, innerGapEndpoint_one] at h0 h1
  rw [innerGapFluxOperator_pairing w a b p hp, innerRadialGapBoundary, h0, h1]

/-- Exact equality of the physical energy and the boundary quadratic form. -/
theorem innerGapPoisson_energy_eq {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (p : Fin 2 → ℝ → ℝ)
    (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) w (p i) r = 0)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    innerRadialGapEnergy w (innerGapPoisson p ξ) j a b =
      ⟪ξ, innerGapFluxOperator w a b p ξ⟫_ℝ :=
  (innerRadialGap_energy_eq_boundary hab ha hw (innerGapPoisson_contDiff p hp ξ)
    (innerGapPoisson_homogeneous hw p hp heq ξ)).trans
      (innerGapPoisson_boundary_pairing w p hp hb ξ)

/-- Green symmetry follows from the actual Lagrange identity. -/
theorem innerGapFluxOperator_isSymmetric {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (p : Fin 2 → ℝ → ℝ)
    (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) w (p i) r = 0) :
    (innerGapFluxOperator w a b p).IsSymmetric := by
  intro ξ η
  have hξ := innerGapPoisson_homogeneous hw p hp heq ξ
  have hη := innerGapPoisson_homogeneous hw p hp heq η
  have h := innerRadialGap_lagrange (j := j) hab ha hw
    (innerGapPoisson_contDiff p hp ξ) (innerGapPoisson_contDiff p hp η)
  have hi : (∫ r in a..b,
      innerGapPoisson p η r * radialJacobi (j ^ 2) w (innerGapPoisson p ξ) r -
        innerGapPoisson p ξ r * radialJacobi (j ^ 2) w (innerGapPoisson p η) r) = 0 := by
    calc
      _ = ∫ _ in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr' : r ∈ Icc a b := by simpa only [uIcc_of_le hab] using hr
        dsimp only
        rw [hξ r hr', hη r hr', mul_zero, mul_zero, sub_self]
      _ = 0 := intervalIntegral.integral_zero
  rw [hi] at h
  have hξ0 := innerGapPoisson_boundary p hb ξ 0
  have hξ1 := innerGapPoisson_boundary p hb ξ 1
  have hη0 := innerGapPoisson_boundary p hb η 0
  have hη1 := innerGapPoisson_boundary p hb η 1
  simp only [innerGapEndpoint_zero, innerGapEndpoint_one] at hξ0 hξ1 hη0 hη1
  simp only [innerRadialGapMixedBoundary, hξ0, hξ1, hη0, hη1] at h
  calc
    ⟪innerGapFluxOperator w a b p ξ, η⟫_ℝ =
        ⟪η, innerGapFluxOperator w a b p ξ⟫_ℝ := real_inner_comm _ _
    _ = ⟪ξ, innerGapFluxOperator w a b p η⟫_ℝ := by
      rw [innerGapFluxOperator_pairing w a b p hp,
        innerGapFluxOperator_pairing w a b p hp]
      linarith only [h]

theorem innerGapFluxMatrix_isHermitian {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (p : Fin 2 → ℝ → ℝ)
    (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) w (p i) r = 0) :
    (innerGapFluxMatrix w a b p).IsHermitian := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  have h : ((innerGapFluxOperator w a b p :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)).IsSymmetric :=
    innerGapFluxOperator_isSymmetric hab ha hw p hp hb heq
  simpa only [innerGapFluxOperator, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using h

theorem innerRadialGap_energy_nonneg {a b : ℝ} (hab : a ≤ b) (ha : 0 < a)
    {w : ℝ → ℝ} (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv w r / w r) (j : ℝ) (u : ℝ → ℝ) :
    0 ≤ innerRadialGapEnergy w u j a b := by
  apply intervalIntegral.integral_nonneg hab
  intro r hr
  exact add_nonneg (mul_nonneg (hpos r hr).le (sq_nonneg _))
    (mul_nonneg (innerRadialGap_potential_nonneg ha hpos hslope j r hr) (sq_nonneg _))

/-- The actual outward flux matrix is positive semidefinite, with both
off-diagonal fluxes included. -/
theorem innerGapFluxMatrix_posSemidef {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (p : Fin 2 → ℝ → ℝ)
    (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) w (p i) r = 0)
    (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv w r / w r) :
    (innerGapFluxMatrix w a b p).PosSemidef := by
  have hpositive : (innerGapFluxOperator w a b p).IsPositive := by
    apply (ContinuousLinearMap.isPositive_iff _).mpr
    refine ⟨innerGapFluxOperator_isSymmetric hab ha hw p hp hb heq, ?_⟩
    intro ξ
    rw [real_inner_comm,
      ← innerGapPoisson_energy_eq hab ha hw p hp hb heq ξ]
    exact innerRadialGap_energy_nonneg hab ha hpos hslope j _
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  simpa only [innerGapFluxOperator, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
    hpositive.toLinearMap

/-- The actual physical Poisson mass estimate. The constant is independent
of the gap length and requires no off-diagonal decay hypothesis. -/
theorem innerGapPoisson_sqrt_mass_le {a b j s : ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (p : Fin 2 → ℝ → ℝ)
    (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) w (p i) r = 0)
    (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv w r / w r)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    Real.sqrt (innerRadialGapMass w (innerGapPoisson p ξ) a b) ≤
      (Real.sqrt (12 / s) / j) * Real.sqrt ⟪ξ, innerGapFluxOperator w a b p ξ⟫_ℝ := by
  have hM := innerRadialGapMass_nonneg hab (fun r hr => (hpos r hr).le)
    (innerGapPoisson p ξ)
  have hQ : 0 ≤ ⟪ξ, innerGapFluxOperator w a b p ξ⟫_ℝ := by
    rw [← innerGapPoisson_energy_eq hab ha hw p hp hb heq ξ]
    exact innerRadialGap_energy_nonneg hab ha hpos (fun r hr => hs.le.trans (hslope r hr)) j _
  have h := innerRadialGap_mass_le_boundary hab ha hj hs hw
    (innerGapPoisson_contDiff p hp ξ) hpos hslope
      (innerGapPoisson_homogeneous hw p hp heq ξ)
  rw [innerGapPoisson_boundary_pairing w p hp hb ξ] at h
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hj.le) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt hM, mul_pow, div_pow,
    Real.sq_sqrt (div_nonneg (by norm_num : (0 : ℝ) ≤ 12) hs.le), Real.sq_sqrt hQ]
  calc
    _ ≤ ⟪ξ, innerGapFluxOperator w a b p ξ⟫_ℝ / ((s / 12) * j ^ 2) := h
    _ = _ := by field_simp [hs.ne', hj.ne'] <;> ring

/-- Actual endpoint columns, obtained from the radial initial-value
construction and the nonvanishing Dirichlet determinant. -/
theorem exists_innerGapPoissonColumns {A l h B : ℝ}
    (hA : 0 < A) (hAl : A < l) (hlh : l < h) (hhB : h < B)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hwnonneg : ∀ x, 0 ≤ w x)
    (hwpos : ∀ x ∈ Ioo A B, 0 < w x)
    (hslope : ∀ x ∈ Icc l h, 0 ≤ x * deriv w x / w x) (j : ℝ) :
    ∃ p : Fin 2 → ℝ → ℝ,
      (∀ k, ContDiff ℝ ∞ (p k)) ∧
      (∀ i k, p k (innerGapEndpoint l h i) = if k = i then 1 else 0) ∧
      (∀ k r, r ∈ Icc l h → radialJacobi (j ^ 2) w (p k) r = 0) := by
  have hex : ∀ k : Fin 2, ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧
      u l = (if k = 0 then 1 else 0) ∧ u h = (if k = 1 then 1 else 0) ∧
      ∀ r ∈ Icc l h, radialJacobi (j ^ 2) w u r = 0 :=
    fun k => exists_innerRadialGap_boundary hA hAl hlh hhB hw hwnonneg hwpos hslope j
      (if k = 0 then 1 else 0) (if k = 1 then 1 else 0)
  choose p hp hleft hright heq using hex
  refine ⟨p, hp, ?_, heq⟩
  intro i k
  fin_cases i
  · simpa [innerGapEndpoint] using hleft k
  · simpa [innerGapEndpoint] using hright k

/-- Physical positive-gap data produces one Poisson map and its actual
positive semidefinite flux matrix, together with the exact energy and
the uniform frequency estimate. -/
theorem exists_innerGapPoissonMatrix {A l h B j s : ℝ}
    (hA : 0 < A) (hAl : A < l) (hlh : l < h) (hhB : h < B)
    (hj : 0 < j) (hs : 0 < s)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hwnonneg : ∀ x, 0 ≤ w x)
    (hwpos : ∀ x ∈ Ioo A B, 0 < w x)
    (hslope : ∀ x ∈ Icc l h, s ≤ x * deriv w x / w x) :
    ∃ p : Fin 2 → ℝ → ℝ,
      (∀ k, ContDiff ℝ ∞ (p k)) ∧
      (∀ i k, p k (innerGapEndpoint l h i) = if k = i then 1 else 0) ∧
      (∀ k r, r ∈ Icc l h → radialJacobi (j ^ 2) w (p k) r = 0) ∧
      (innerGapFluxMatrix w l h p).PosSemidef ∧
      ∀ ξ : EuclideanSpace ℝ (Fin 2),
        innerRadialGapEnergy w (innerGapPoisson p ξ) j l h =
          ⟪ξ, innerGapFluxOperator w l h p ξ⟫_ℝ ∧
        Real.sqrt (innerRadialGapMass w (innerGapPoisson p ξ) l h) ≤
          (Real.sqrt (12 / s) / j) * Real.sqrt ⟪ξ, innerGapFluxOperator w l h p ξ⟫_ℝ := by
  have hslope0 : ∀ x ∈ Icc l h, 0 ≤ x * deriv w x / w x :=
    fun x hx => hs.le.trans (hslope x hx)
  have hpos : ∀ x ∈ Icc l h, 0 < w x :=
    fun x hx => hwpos x ⟨hAl.trans_le hx.1, hx.2.trans_lt hhB⟩
  obtain ⟨p, hp, hb, heq⟩ := exists_innerGapPoissonColumns
    hA hAl hlh hhB hw hwnonneg hwpos hslope0 j
  refine ⟨p, hp, hb, heq,
    innerGapFluxMatrix_posSemidef hlh.le (hA.trans hAl) hw p hp hb heq hpos hslope0, ?_⟩
  intro ξ
  exact ⟨innerGapPoisson_energy_eq hlh.le (hA.trans hAl) hw p hp hb heq ξ,
    innerGapPoisson_sqrt_mass_le hlh.le (hA.trans hAl) hj hs hw p hp hb heq hpos hslope ξ⟩

end ContinuousFlexibility.Radial
