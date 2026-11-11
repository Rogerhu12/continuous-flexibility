import ContinuousFlexibility.Radial.InnerGapPoissonL2
import ContinuousFlexibility.Radial.InnerReferenceNormalization
import ContinuousFlexibility.Radial.InnerRadialFiniteWeakGraph

/-!
# Actual positive-gap blocks in the full reference interface

The data records positive radial intervals and their actual classical
Poisson columns. Matrix positivity, reference positivity, and the
quadratic-form identities are derived below. The two off-diagonal
entries of every gap matrix remain in the reference matrix.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

/-- Geometric and classical data of the actual positive gaps. No inverse,
matrix positivity, or operator estimate is a field of this structure. -/
structure InnerPositiveGapFamily (D : ReferenceData) (γ : Type*) (j s : ℝ) where
  left : γ → ℝ
  right : γ → ℝ
  ordered : ∀ c, left c ≤ right c
  left_pos : ∀ c, 0 < left c
  in_core : ∀ c, Ioo (left c) (right c) ⊆ radialCore D
  weight_pos : ∀ c r, r ∈ Icc (left c) (right c) → 0 < D.w r
  slope_lower : ∀ c r, r ∈ Icc (left c) (right c) → s ≤ r * deriv D.w r / D.w r
  columns : γ → Fin 2 → ℝ → ℝ
  columns_smooth : ∀ c i, ContDiff ℝ ∞ (columns c i)
  columns_boundary : ∀ c i k,
    columns c k (innerGapEndpoint (left c) (right c) i) = if k = i then 1 else 0
  columns_homogeneous : ∀ c i r, r ∈ Icc (left c) (right c) →
    radialJacobi (j ^ 2) D.w (columns c i) r = 0
  disjoint : Pairwise (fun c d => Disjoint (Ioo (left c) (right c)) (Ioo (left d) (right d)))

/-- The finite family is obtained from the actual scalar flux IVP
construction, rather than assuming Poisson solvability. -/
def innerPositiveGapFamilyOfCoefficients (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {γ : Type*} {j s : ℝ} (hs : 0 ≤ s) (A a b B : γ → ℝ)
    (hA : ∀ c, 0 < A c) (hAa : ∀ c, A c < a c) (hab : ∀ c, a c < b c)
    (hbB : ∀ c, b c < B c) (hcore : ∀ c, Ioo (a c) (b c) ⊆ radialCore D)
    (hwnonneg : ∀ r, 0 ≤ D.w r)
    (hwpos : ∀ c r, r ∈ Ioo (A c) (B c) → 0 < D.w r)
    (hslope : ∀ c r, r ∈ Icc (a c) (b c) → s ≤ r * deriv D.w r / D.w r)
    (hdis : Pairwise (fun c d => Disjoint (Ioo (a c) (b c)) (Ioo (a d) (b d)))) :
    InnerPositiveGapFamily D γ j s := by
  classical
  choose p hp hboundary heq using fun c =>
    exists_innerGapPoissonColumns (hA c) (hAa c) (hab c) (hbB c) hw hwnonneg (hwpos c)
      (fun r hr => hs.trans (hslope c r hr)) j
  exact
    { left := a
      right := b
      ordered := fun c => (hab c).le
      left_pos := fun c => (hA c).trans (hAa c)
      in_core := hcore
      weight_pos := fun c r hr => hwpos c r ⟨(hAa c).trans_le hr.1, hr.2.trans_lt (hbB c)⟩
      slope_lower := hslope
      columns := p
      columns_smooth := hp
      columns_boundary := hboundary
      columns_homogeneous := heq
      disjoint := hdis }

/-- The existing actual chain endpoint restriction, with its Euclidean
rather than maximum boundary norm. Outer endpoint values remain zero. -/
def innerChainBoundaryRestrictionL2 (n : ℕ) (p : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin 2) := by
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    { toFun := fun ξ => WithLp.toLp 2 (innerChainBoundaryRestriction n p ξ)
      map_add' := by
        intro ξ η
        apply PiLp.ext
        intro i
        simp only [PiLp.toLp_apply, PiLp.add_apply, map_add, Pi.add_apply]
      map_smul' := by
        intro c ξ
        apply PiLp.ext
        intro i
        simp only [PiLp.toLp_apply, PiLp.smul_apply, map_smul,
          Pi.smul_apply, RingHom.id_apply] }
  exact ⟨L, L.continuous_of_finiteDimensional⟩

theorem innerChainBoundaryRestrictionL2_apply (n : ℕ) (p : Fin (n + 1))
    (ξ : EuclideanSpace ℝ (Fin n)) (i : Fin 2) :
    innerChainBoundaryRestrictionL2 n p ξ i = innerChainBoundaryRestriction n p ξ i := rfl

theorem innerMatrix_toEuclideanCLM_isPositive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A).IsPositive := by
  apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  exact Matrix.isPositive_toEuclideanLin_iff.mpr hA

theorem innerMatrix_inner_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hAB : A ≤ B) (x : EuclideanSpace ℝ ι) :
    ⟪x, Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A x⟫_ℝ ≤
      ⟪x, Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) B x⟫_ℝ := by
  have h := (innerMatrix_toEuclideanCLM_isPositive (Matrix.le_iff.mp hAB)).inner_nonneg_right x
  simpa only [map_sub, sub_apply, inner_sub_right, sub_nonneg] using h

theorem innerMatrix_inverseSqrt_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (x : EuclideanSpace ℝ ι) :
    let J := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (innerInterfaceInverseSqrt A)
    ⟪J x, Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A (J x)⟫_ℝ = ‖x‖ ^ 2 := by
  let J := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (innerInterfaceInverseSqrt A)
  have hJ : J.adjoint = J := by
    rw [← innerMatrix_toEuclideanCLM_conjTranspose, (innerInterfaceInverseSqrt_isHermitian A).eq]
  have hmap := congrArg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ))
    (innerInterfaceInverseSqrt_normalizes A hA)
  simp only [map_mul, map_one] at hmap
  have hx := congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι => L x) hmap
  simp only [mul_apply_eq_comp, one_apply_eq_self] at hx
  calc
    ⟪J x, Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A (J x)⟫_ℝ =
        ⟪x, J (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A (J x))⟫_ℝ := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hJ]
    _ = ⟪x, x⟫_ℝ := congrArg (fun y => ⟪x, y⟫_ℝ) hx
    _ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x

namespace InnerPositiveGapFamily

variable {D : ReferenceData} {γ ι : Type*} {j s : ℝ}
  (F : InnerPositiveGapFamily D γ j s)

def poisson (hw : Continuous D.w) (c : γ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] RadialModeL2 D :=
  innerGapPoissonL2 D hw (F.left_pos c) (F.in_core c)
    (fun r hr => (F.weight_pos c r (Ioo_subset_Icc_self hr)).le)
    (F.columns c) (F.columns_smooth c)

def fluxMatrix (c : γ) : Matrix (Fin 2) (Fin 2) ℝ :=
  innerGapFluxMatrix D.w (F.left c) (F.right c) (F.columns c)

def flux (c : γ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  innerGapFluxOperator D.w (F.left c) (F.right c) (F.columns c)

theorem fluxMatrix_posSemidef (hw : ContDiff ℝ ∞ D.w) (hs : 0 ≤ s) (c : γ) :
    (F.fluxMatrix c).PosSemidef :=
  innerGapFluxMatrix_posSemidef (F.ordered c) (F.left_pos c) hw
    (F.columns c) (F.columns_smooth c) (F.columns_boundary c) (F.columns_homogeneous c)
    (F.weight_pos c) (fun r hr => hs.trans (F.slope_lower c r hr))

theorem flux_isPositive (hw : ContDiff ℝ ∞ D.w) (hs : 0 ≤ s) (c : γ) :
    (F.flux c).IsPositive :=
  innerMatrix_toEuclideanCLM_isPositive (F.fluxMatrix_posSemidef hw hs c)

variable [Fintype ι] [DecidableEq ι]

/-- The full actual local flux block, lifted by the actual boundary
restriction and represented in the global Euclidean cut coordinates. -/
def referenceBlock (R : γ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (c : γ) : Matrix ι ι ℝ :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).symm
    ((R c).adjoint ∘L F.flux c ∘L R c)

theorem referenceBlock_toEuclideanCLM
    (R : γ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin 2)) (c : γ) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (F.referenceBlock R c) =
      (R c).adjoint ∘L F.flux c ∘L R c :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).apply_symm_apply _

theorem referenceBlock_posSemidef (hw : ContDiff ℝ ∞ D.w) (hs : 0 ≤ s)
    (R : γ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin 2)) (c : γ) :
    (F.referenceBlock R c).PosSemidef := by
  have h : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (F.referenceBlock R c)).IsPositive := by
    rw [F.referenceBlock_toEuclideanCLM]
    exact (F.flux_isPositive hw hs c).adjoint_conj (R c)
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  simpa only [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
    (ContinuousLinearMap.isPositive_toLinearMap_iff _).mpr h

theorem referenceBlock_energy
    (R : γ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (c : γ) (x : EuclideanSpace ℝ ι) :
    ⟪x, Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (F.referenceBlock R c) x⟫_ℝ =
      ⟪R c x, F.flux c (R c x)⟫_ℝ := by
  rw [F.referenceBlock_toEuclideanCLM]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

variable [Fintype γ]

def referenceMatrix (κ : ι → ℝ)
    (R : γ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin 2)) : Matrix ι ι ℝ :=
  Matrix.diagonal κ + ∑ c, F.referenceBlock R c

theorem referenceMatrix_posDef (hw : ContDiff ℝ ∞ D.w) (hs : 0 ≤ s)
    (κ : ι → ℝ) (hκ : ∀ i, 0 < κ i)
    (R : γ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    (F.referenceMatrix κ R).PosDef :=
  innerReference_posDef_of_psd_gaps κ (F.referenceBlock R) hκ
    (F.referenceBlock_posSemidef hw hs R)

theorem diagonal_le_referenceMatrix (hw : ContDiff ℝ ∞ D.w) (hs : 0 ≤ s)
    (κ : ι → ℝ)
    (R : γ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    Matrix.diagonal κ ≤ F.referenceMatrix κ R :=
  innerReference_diagonal_le_of_psd_gaps κ (F.referenceBlock R)
    (F.referenceBlock_posSemidef hw hs R)

theorem gap_energy_le_reference (κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (R : γ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ ι) :
    (∑ c, ⟪R c x, F.flux c (R c x)⟫_ℝ) ≤
      ⟪x, Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (F.referenceMatrix κ R) x⟫_ℝ := by
  have hle : (∑ c, F.referenceBlock R c) ≤ F.referenceMatrix κ R :=
    le_add_of_nonneg_left (Matrix.posSemidef_diagonal_iff.mpr hκ).nonneg
  have h := innerMatrix_inner_mono hle x
  simpa only [map_sum, sum_apply, inner_sum, F.referenceBlock_energy] using h

end InnerPositiveGapFamily

end ContinuousFlexibility.Radial
