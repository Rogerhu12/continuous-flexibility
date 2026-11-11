import ContinuousFlexibility.Radial.InnerActualUnweightedInverse
import ContinuousFlexibility.Radial.InnerRadialGapChartConstruction

/-!
# One central model and two genuine positive gaps

The gap columns and inverses are constructed from the original profile.
The only model data are the already selected central chart.  A common
three-quarter logarithmic slope gives a bound independent of the two
gap lengths, hence of the subsequent retained-cone length.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace Matrix.Norms.L2Operator

variable {D : ReferenceData} (hD : RadialProfileGeometry D)
  (G : InnerRadialChainGeometry D 2) {bordered : Bool} {j : ℝ}
  {column : RadialModeL2 D} (hj : 0 < j)
  (A : InnerRadialModelChart D G bordered j (1 : Fin 3) column (1 : Fin 3))
  (hslope : ∀ p : Fin 3, p ≠ 1 → ∀ r ∈ Icc (G.left p) (G.right p),
    (3 : ℝ) / 4 ≤ r * deriv D.w r / D.w r)

/-- The same actual central chart with the two actual IVP gap charts. -/
def innerCentralThreePieceChain :
    InnerRadialActualChain D G bordered j (1 : Fin 3) column where
  piece p := if hp : p = 1 then by
      subst p
      exact .inl A
    else .inr (innerRadialGapChartOfProfile D hD G j 1 p hp hj
      (by norm_num : (0 : ℝ) < 3 / 4) (hslope p hp))

@[simp] theorem innerCentralThreePieceChain_center :
    (innerCentralThreePieceChain hD G hj A hslope).piece 1 = .inl A := by
  simp [innerCentralThreePieceChain]

@[simp] theorem innerCentralThreePieceChain_gap (p : Fin 3) (hp : p ≠ 1) :
    (innerCentralThreePieceChain hD G hj A hslope).piece p =
      .inr (innerRadialGapChartOfProfile D hD G j 1 p hp hj
        (by norm_num : (0 : ℝ) < 3 / 4) (hslope p hp)) := by
  simp [innerCentralThreePieceChain, hp]

theorem innerCentralThreePieceChain_kappa (i : Fin 2) :
    (innerCentralThreePieceChain hD G hj A hslope).kappa i = A.kappa i := by
  fin_cases i <;>
    simp [InnerRadialActualChain.kappa, innerChainAggregateKappa,
      innerCentralThreePieceChain, InnerRadialActualPiece.kappa]

theorem innerCentralThreePieceChain_separated (i : Fin 2) :
    ((innerCentralThreePieceChain hD G hj A hslope).piece i.castSucc).kappa 1 = 0 ∨
      ((innerCentralThreePieceChain hD G hj A hslope).piece i.succ).kappa 0 = 0 := by
  fin_cases i
  · left
    simp [innerCentralThreePieceChain, InnerRadialActualPiece.kappa]
  · right
    simp [innerCentralThreePieceChain, InnerRadialActualPiece.kappa]

include hj hslope in
/-- A genuine two-sided inverse on the original finite weak graph, with
a bound depending only on the selected central chart costs.  The outer
cut locations and both positive-gap lengths are absent from the bound. -/
theorem exists_innerCentralThreePieceInverse
    {K d η : ℝ} (hK : 0 ≤ K) (hd : 0 ≤ d) (hfrequency : 2 ≤ j)
    (hκ : ∀ i, 0 < A.kappa i)
    (hη : 0 ≤ η) (hηsmall : η < 1 / 4)
    (herror : ∀ sign : Bool,
      ‖innerTwoCutWeightedError A.kappa (fun _ => 1) A.errorMatrix sign‖ ≤ η)
    (hcolumns : ∀ i, ‖(Real.sqrt (A.kappa i))⁻¹ • A.column i‖ ≤ K / j)
    (hdirichlet : ‖A.dirichlet‖ ≤ d) :
    ∃ inverse : InnerRadialPhysicalSource D G bordered →L[ℝ]
        InnerRadialPhysicalSource D G bordered,
      (∀ u F, InnerRadialPhysicalWeakGraph D hD.2.2.1.1.continuous G bordered j 1 column
        u F ↔ inverse F = u) ∧
      ‖inverse‖ ≤ max d 4 + (max (2 * K) 4) ^ 2 / 2 ∧ IsSelfAdjoint inverse := by
  let C := innerCentralThreePieceChain hD G hj A hslope
  have hmodel : ∀ p (M : InnerRadialModelChart D G bordered j 1 column p),
      C.piece p = .inl M → 0 < p.val ∧ p.val < 2 ∧ ∀ i, 0 < M.kappa i := by
    intro p M hpM
    by_cases hp : p = 1
    · subst p
      have hAM : A = M := by simpa [C] using hpM
      subst M
      exact ⟨by decide, by decide, hκ⟩
    · simp [C, innerCentralThreePieceChain, hp] at hpM
  have hgap : ∀ p (Q : InnerRadialGapChart D G j 1 p), C.piece p = .inr Q →
      (3 : ℝ) / 4 ≤ Q.slope := by
    intro p Q hpQ
    by_cases hp : p = 1
    · subst p
      simp [C] at hpQ
    · have hQ : innerRadialGapChartOfProfile D hD G j 1 p hp hj
          (by norm_num : (0 : ℝ) < 3 / 4) (hslope p hp) = Q := by
        simpa [C, innerCentralThreePieceChain, hp] using hpQ
      rw [← hQ]
      exact le_rfl
  have hcost : ∀ p, ‖(C.piece p).dirichlet hD.2.2.1.1‖ ≤ max d 4 := by
    intro p
    cases hp : C.piece p with
    | inl M =>
      have hp1 : p = 1 := by
        by_contra hne
        simp [C, innerCentralThreePieceChain, hne] at hp
      subst p
      have hAM : A = M := by simpa [C] using hp
      subst M
      simpa only [hp, InnerRadialActualPiece.dirichlet] using
        hdirichlet.trans (le_max_left d 4)
    | inr Q =>
      have hsq : (4 : ℝ) ≤ j ^ 2 := by nlinarith only [hfrequency]
      have hden : (3 : ℝ) ≤ (3 / 4) * j ^ 2 := by nlinarith only [hsq]
      have hbound : 12 / ((3 / 4) * j ^ 2) ≤ (4 : ℝ) := by
        apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 3 / 4)
          (sq_pos_of_pos hj))).mpr
        nlinarith only [hden]
      have h := (Q.dirichlet_norm_le_uniform hD.2.2.1.1
        (by norm_num : (0 : ℝ) < 3 / 4) (hgap p Q hp)).trans hbound
      simpa only [hp, InnerRadialActualPiece.dirichlet] using h.trans (le_max_right d 4)
  obtain ⟨inverse, hgraph, hnorm, hself⟩ :=
    C.exists_unweighted_inverse_of_local_bounds hD.2.2.1.1
      (by norm_num : (0 : ℝ) < 3 / 4) hK (hd.trans (le_max_left d 4)) hj
      (fun i => by simpa [C, innerCentralThreePieceChain_kappa] using hκ i)
      (innerCentralThreePieceChain_separated hD G hj A hslope) hmodel hη hηsmall
      (by
        intro p M hpM sign
        have hp : p = 1 := by
          by_contra hne
          simp [C, innerCentralThreePieceChain, hne] at hpM
        subst p
        have hAM : A = M := by simpa [C] using hpM
        subst M
        exact herror sign)
      (by
        intro p M hpM i
        have hp : p = 1 := by
          by_contra hne
          simp [C, innerCentralThreePieceChain, hne] at hpM
        subst p
        have hAM : A = M := by simpa [C] using hpM
        subst M
        exact hcolumns i)
      hgap hcost
  refine ⟨inverse, hgraph, hnorm.trans ?_, hself⟩
  have hsqrt : Real.sqrt (12 / ((3 : ℝ) / 4)) = 4 := by
    rw [show 12 / ((3 : ℝ) / 4) = (4 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  rw [hsqrt]
  apply add_le_add (le_refl _)
  have hsq : (4 : ℝ) ≤ j ^ 2 := by nlinarith only [hfrequency]
  have h := div_le_div_of_nonneg_left
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (max (2 * K) 4)))
    (by norm_num : (0 : ℝ) < 4) hsq
  convert h using 1 <;> ring

end ContinuousFlexibility.Radial
