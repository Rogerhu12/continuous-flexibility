import ContinuousFlexibility.Radial.InnerActualUnweightedInverse
import ContinuousFlexibility.Radial.InnerHardyWeightedPoisson

/-!
# The actual finite-chain inverse with Hardy gap costs

Unit weights preserve the complete positive gap matrices. The genuine
Hardy bound and actual adjacent model endpoint energies replace a
uniform slope assumption, while the local model errors still control
the same physical Schur inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace Matrix.Norms.L2Operator

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (A : InnerRadialActualChain D G bordered j central column)

local notation "H" => InnerRadialPhysicalSource D G bordered

theorem exists_unweighted_inverse_of_local_bounds_hardy (hw : ContDiff ℝ ∞ D.w)
    {K L d η : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hd : 0 ≤ d) (hj : 0 < j)
    (hjhalf : (1 / 2 : ℝ) ≤ j ^ 2) (hκ : ∀ i, 0 < A.kappa i)
    (hsep : ∀ i : Fin n,
      (A.piece i.castSucc).kappa 1 = 0 ∨ (A.piece i.succ).kappa 0 = 0)
    (hmodels : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      A.piece p = .inl M → 0 < p.val ∧ p.val < n ∧ ∀ i, 0 < M.kappa i)
    (hη : 0 ≤ η) (hηsmall : η < 1 / 4)
    (herror : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      A.piece p = .inl M → ∀ sign : Bool,
        ‖innerTwoCutWeightedError M.kappa (fun _ => 1) M.errorMatrix sign‖ ≤ η)
    (hcolumns : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      A.piece p = .inl M → ∀ i,
        ‖(Real.sqrt (M.kappa i))⁻¹ • M.column i‖ ≤ K / j)
    (hendpoints : ∀ (i : Fin n) (Q : InnerRadialGapChart D G j central i.succ),
      A.piece i.succ = .inr Q → D.w (G.left i.succ) / G.left i.succ ≤ L * A.kappa i)
    (hdirichlet : ∀ p, ‖(A.piece p).dirichlet hw‖ ≤ d) :
    ∃ inverse : H →L[ℝ] H,
      (∀ u F, InnerRadialPhysicalWeakGraph D hw.continuous G bordered j central column
        u F ↔ inverse F = u) ∧
      ‖inverse‖ ≤ d + 2 * (max ((2 * K / j) ^ 2) 48 + 24 * L) ∧
      IsSelfAdjoint inverse := by
  let cost : ℝ := max ((2 * K / j) ^ 2) 48 + 24 * L
  have hcost : 0 ≤ cost := add_nonneg
    ((sq_nonneg _).trans (le_max_left _ _)) (mul_nonneg (by norm_num) hL)
  have hgapweight : ∀ p (Q : InnerRadialGapChart D G j central p),
      A.piece p = .inr Q → ∃ c : ℝ,
        (0 < p.val → innerChainScalarRestriction n p (fun _ => 1) 1 0 = c) ∧
        (p.val < n → innerChainScalarRestriction n p (fun _ => 1) 1 1 = c) := by
    intro p Q _
    exact ⟨1, fun _ => congrFun (innerChainScalarRestriction_one n p) 0,
      fun _ => congrFun (innerChainScalarRestriction_one n p) 1⟩
  have herror' : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      A.piece p = .inl M → ∀ sign : Bool,
        ‖innerTwoCutWeightedError M.kappa
          (innerChainScalarRestriction n p (fun _ => 1) 1) M.errorMatrix sign‖ ≤ η := by
    simpa only [innerChainScalarRestriction_one] using herror
  have hS := A.fluxMatrix_isUnit_of_local_errors hw hκ (fun _ => 1)
    (fun _ => zero_lt_one) hgapweight hsep hmodels hη hηsmall herror'
  have hPambient := A.weighted_poisson_bound_hardy hw (fun _ => 1) measurable_const 1
    (by simp) (fun _ => 1) (fun _ => zero_lt_one) hK hL hj hjhalf hκ
    (fun p M hp => (hmodels p M hp).2.2)
    (by
      intro p M hp i
      simpa only [innerChainScalarRestriction_one, one_mul,
        innerBorderFieldMap_weight_one, ContinuousLinearMap.id_apply] using hcolumns p M hp i)
    (by
      intro p Q _
      exact ⟨1, zero_lt_one, fun _ _ => rfl,
        fun _ => congrFun (innerChainScalarRestriction_one n p) 0,
        fun _ => congrFun (innerChainScalarRestriction_one n p) 1⟩)
    hendpoints
  have hP : ‖A.poisson hw ∘L Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (innerInterfaceInverseSqrt A.referenceMatrix)‖ ≤ Real.sqrt cost := by
    have h := (A.weighted_poisson_norm_le_ambient hw (fun _ => 1) measurable_const 1
      (by simp) (fun _ => 1)).trans hPambient
    simpa only [inv_one, innerSupportedWeightMultiplier_one, innerBorderFieldMap_weight_one,
      innerBoundaryDiagonal_one, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
      using h
  have hD : ‖A.dirichlet hw‖ ≤ d := by
    have h := A.dirichlet_weighted_piece_cost hw (fun _ => 1) (fun _ => 1)
      measurable_const measurable_const 1 1 (by simp) (by simp)
      (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (fun _ => zero_le_one) (fun _ => zero_le_one) (fun _ => zero_lt_one)
      (by norm_num) (by norm_num) (by simp) (by simp) hd
      (by simpa only [one_pow, one_mul] using hdirichlet)
    simpa only [innerRadialSupportedMultiplier, innerSupportedWeightMultiplier_one,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using h
  have hself : IsSelfAdjoint (ContinuousLinearEquiv.refl ℝ H : H →L[ℝ] H) := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    rfl
  have hΩ : innerMatrixEquiv (Matrix.diagonal (fun _ : Fin n => (1 : ℝ)))
      (Matrix.PosDef.isUnit (Matrix.posDef_diagonal_iff.mpr (fun _ => zero_lt_one))) =
      ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)) := by
    apply ContinuousLinearEquiv.ext
    funext ξ
    rw [innerMatrixEquiv_apply]
    change innerBoundaryDiagonal (fun _ : Fin n => (1 : ℝ)) ξ = ξ
    rw [innerBoundaryDiagonal_one, ContinuousLinearMap.id_apply]
  have hcancel : (j * Real.sqrt cost) / j = Real.sqrt cost := by
    field_simp [hj.ne'] <;> ring
  have hcorrection := A.correction_weighted_bound hw hκ (fun _ => 1)
    (fun _ => zero_lt_one) hgapweight hsep hmodels hη hηsmall herror'
    (ContinuousLinearEquiv.refl ℝ H) hself
    (mul_nonneg hj.le (Real.sqrt_nonneg cost)) hj
    (fun sign => by
      rw [hΩ, hcancel]
      cases sign <;> simpa [innerWeightedPoisson, innerHilbertWeight] using hP) true
  have hco : ‖innerCouplingCorrection (A.poisson hw)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A.fluxMatrix⁻¹)‖ ≤
        2 * (j * Real.sqrt cost) ^ 2 / j ^ 2 := by
    simpa [innerHilbertWeight] using hcorrection
  have hscalar : 2 * (j * Real.sqrt cost) ^ 2 / j ^ 2 = 2 * cost := by
    rw [mul_pow, Real.sq_sqrt hcost]
    field_simp [hj.ne'] <;> ring
  refine ⟨A.inverse hw hS, A.inverse_graph_iff hw hS, ?_, A.inverse_selfAdjoint hw hS⟩
  rw [A.inverse_eq_glued hw hS, innerGluedInverse]
  exact (norm_add_le _ _).trans (add_le_add hD (hco.trans_eq hscalar))

end InnerRadialActualChain

end ContinuousFlexibility.Radial
