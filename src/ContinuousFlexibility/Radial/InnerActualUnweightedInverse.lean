module

public import ContinuousFlexibility.Radial.InnerRadialWeightedInverse
public import ContinuousFlexibility.Radial.InnerRadialDirichletWeights
public import ContinuousFlexibility.Radial.MatchedInnerUnitWeights

/-!
# The actual finite-chain inverse with unit physical weights

The model errors and the complete positive gap matrices control the same
physical Schur inverse. Local normalized model columns and a uniform
positive gap slope give a norm bound independent of the number of pieces.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace Matrix.Norms.L2Operator

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (A : InnerRadialActualChain D G bordered j central column)

local notation "H" => InnerRadialPhysicalSource D G bordered

theorem exists_unweighted_inverse_of_local_bounds (hw : ContDiff ℝ ∞ D.w)
    {K s d η : ℝ} (hs : 0 < s) (hK : 0 ≤ K) (hd : 0 ≤ d) (hj : 0 < j)
    (hκ : ∀ i, 0 < A.kappa i)
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
    (hgaps : ∀ p (Q : InnerRadialGapChart D G j central p),
      A.piece p = .inr Q → s ≤ Q.slope)
    (hdirichlet : ∀ p, ‖(A.piece p).dirichlet hw‖ ≤ d) :
    ∃ inverse : H →L[ℝ] H,
      (∀ u F, InnerRadialPhysicalWeakGraph D hw.continuous G bordered j central column
        u F ↔ inverse F = u) ∧
      ‖inverse‖ ≤ d + 2 * (max (2 * K) (Real.sqrt (12 / s))) ^ 2 / j ^ 2 ∧
      IsSelfAdjoint inverse := by
  let cost : ℝ := max (2 * K) (Real.sqrt (12 / s))
  have hcost : 0 ≤ cost :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK).trans (le_max_left _ _)
  have hgapweight : ∀ p (Q : InnerRadialGapChart D G j central p),
      A.piece p = .inr Q → ∃ c : ℝ,
        (0 < p.val → innerChainScalarRestriction n p (fun _ => 1) 1 0 = c) ∧
        (p.val < n → innerChainScalarRestriction n p (fun _ => 1) 1 1 = c) := by
    intro p Q _
    exact ⟨1, fun _ => congrFun (innerChainScalarRestriction_one_unit n p) 0,
      fun _ => congrFun (innerChainScalarRestriction_one_unit n p) 1⟩
  have herror' : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      A.piece p = .inl M → ∀ sign : Bool,
        ‖innerTwoCutWeightedError M.kappa
          (innerChainScalarRestriction n p (fun _ => 1) 1) M.errorMatrix sign‖ ≤ η := by
    simpa only [innerChainScalarRestriction_one_unit] using herror
  have hS := A.fluxMatrix_isUnit_of_local_errors hw hκ (fun _ => 1)
    (fun _ => zero_lt_one) hgapweight hsep hmodels hη hηsmall herror'
  have hPambient := A.weighted_poisson_bound hw (fun _ => 1) measurable_const 1
    (by simp) (fun _ => 1) (fun _ => zero_lt_one) hK hs hj hκ
    (fun p M hp => (hmodels p M hp).2.2)
    (by
      intro p M hp i
      simpa only [innerChainScalarRestriction_one_unit, one_mul,
        innerBorderFieldMap_weight_one_unit, ContinuousLinearMap.id_apply] using hcolumns p M hp i)
    (by
      intro p Q hp
      exact ⟨hgaps p Q hp, 1, zero_lt_one, fun _ _ => rfl,
        fun _ => congrFun (innerChainScalarRestriction_one_unit n p) 0,
        fun _ => congrFun (innerChainScalarRestriction_one_unit n p) 1⟩)
  have hP : ‖A.poisson hw ∘L Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (innerInterfaceInverseSqrt A.referenceMatrix)‖ ≤ cost / j := by
    have h := (A.weighted_poisson_norm_le_ambient hw (fun _ => 1) measurable_const 1
      (by simp) (fun _ => 1)).trans hPambient
    simpa only [inv_one, innerSupportedWeightMultiplier_one_unit, innerBorderFieldMap_weight_one_unit,
      innerBoundaryDiagonal_one_unit, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
      using h
  have hD : ‖A.dirichlet hw‖ ≤ d := by
    have h := A.dirichlet_weighted_piece_cost hw (fun _ => 1) (fun _ => 1)
      measurable_const measurable_const 1 1 (by simp) (by simp)
      (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (fun _ => zero_le_one) (fun _ => zero_le_one) (fun _ => zero_lt_one)
      (by norm_num) (by norm_num) (by simp) (by simp) hd
      (by simpa only [one_pow, one_mul] using hdirichlet)
    simpa only [innerRadialSupportedMultiplier, innerSupportedWeightMultiplier_one_unit,
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
    rw [innerBoundaryDiagonal_one_unit, ContinuousLinearMap.id_apply]
  have hcorrection := A.correction_weighted_bound hw hκ (fun _ => 1)
    (fun _ => zero_lt_one) hgapweight hsep hmodels hη hηsmall herror'
    (ContinuousLinearEquiv.refl ℝ H) hself hcost hj
    (fun sign => by
      rw [hΩ]
      cases sign <;> simpa [innerWeightedPoisson, innerHilbertWeight] using hP) true
  have hco : ‖innerCouplingCorrection (A.poisson hw)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A.fluxMatrix⁻¹)‖ ≤
        2 * cost ^ 2 / j ^ 2 := by
    simpa [innerHilbertWeight] using hcorrection
  refine ⟨A.inverse hw hS, A.inverse_graph_iff hw hS, ?_, A.inverse_selfAdjoint hw hS⟩
  rw [A.inverse_eq_glued hw hS, innerGluedInverse]
  exact (norm_add_le _ _).trans (add_le_add hD hco)

end InnerRadialActualChain

end ContinuousFlexibility.Radial
