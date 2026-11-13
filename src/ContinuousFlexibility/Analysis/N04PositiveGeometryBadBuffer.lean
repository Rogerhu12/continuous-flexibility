import ContinuousFlexibility.Analysis.N04PositiveGeometryBufferFreedom
import ContinuousFlexibility.Analysis.N04PositiveGeometryDiagonalCost
import ContinuousFlexibility.Analysis.N04PositiveGeometryInfiniteComponents
import ContinuousFlexibility.Analysis.N04PositiveGeometryRightSource
import ContinuousFlexibility.Analysis.N04PositiveGeometryCircleVariation

/-!
# A legal normalization buffer with no uniform endpoint cost

The buffer is chosen before the state neighborhood, transport family,
derivative loss and material exponent. Its normalization region is the
original region. Infinitely many actual positive components allow the
right transition widths to be diagonalized against every pair of a
material exponent and a derivative loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- Some legal buffer cannot satisfy the necessary endpoint cost for
any fixed loss and any component-uniform material power. -/
theorem n04PositiveGeometry_exists_bad_buffer
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (Y H : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (hreference : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H)
    (B₀ : N04PositiveNormalizationBuffer W.D.a W.D.b (deriv W.D.w) (tsupport W.D.chi)) :
    ∃ B : N04PositiveNormalizationBuffer W.D.a W.D.b (deriv W.D.w) (tsupport W.D.chi),
      B.normalizationLeft = B₀.normalizationLeft ∧
      B.normalizationRight = B₀.normalizationRight ∧
      ¬ ∃ loss : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
          1 ≤ C * W.U.E0 (W.U.sample (X.cell i)) ^ C *
            W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ) *
            parameterGrading W.S (1 + loss)
              (n04PositiveGeometry_circleDirection W.hS
                (n04PositiveGeometry_rightSource W X i), 0) *
            (1 - Y i (B.centerRight i)) := by
  classical
  let I := n04PositiveGeometry_pairEmbedding W
  let E : ℕ × ℕ → ℝ := fun j => W.U.E0 (W.U.sample (X.cell (I j)))
  let Hm : ℕ × ℕ → ℝ := fun j => W.U.H (W.U.sample (X.cell (I j)))
  let K : (ℕ × ℕ) → ℕ → ℝ := fun j loss =>
    parameterGrading W.S (1 + loss)
      (n04PositiveGeometry_circleDirection W.hS
        (n04PositiveGeometry_rightSource W X (I j)), 0)
  have hD : IsAccumulatingProfile W.D := W.radial.1
  have hU : IsMaterialData W.D W.U := isMaterialData_enlargedMaterialData hD W.hT
  have hE (j : ℕ × ℕ) : 1 ≤ E j :=
    (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH (j : ℕ × ℕ) : 0 ≤ Hm j :=
    (hU.2.1 _ (materialSample_mem_interval hD hU (X.cell (I j)))).2.1.le
  have hK (j : ℕ × ℕ) (loss : ℕ) : 0 ≤ K j loss := apply_nonneg _ _
  have hδ := n04PositiveGeometry_exists_diagonal_width E Hm K hE hH hK
  let δ := hδ.choose
  have hδpos : ∀ j, 0 < δ j := hδ.choose_spec.1
  have hδbad := hδ.choose_spec.2
  let gap : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ :=
    fun i => δ (Function.invFun I i)
  have hgap (j : ℕ × ℕ) : gap (I j) = δ j := by
    change δ (Function.invFun I (I j)) = δ j
    rw [Function.leftInverse_invFun I.injective j]
  have hB := n04PositiveGeometry_buffer_arbitrarily_small_right_canonical_gap
    B₀ Y H (fun i => (hreference i).1) gap (fun i => hδpos _)
  let B := hB.choose
  have hBprop := hB.choose_spec
  refine ⟨B, hBprop.2.1, hBprop.2.2.1, ?_⟩
  intro hcost
  apply hcost.elim
  intro loss hloss
  apply hloss.elim
  intro C hC
  apply hδbad C hC.1 loss
  intro j
  have hwidth : 1 - Y (I j) (B.centerRight (I j)) ≤ δ j := by
    exact ((hBprop.2.2.2 (I j)).2.2.trans_le (by rw [hgap])).le
  have hc := hC.2 (I j)
  have hnonneg : 0 ≤ C * E j ^ C * Hm j ^ (3 / 4 : ℝ) * K j loss := by
    have he0 : 0 ≤ E j := zero_le_one.trans (hE j)
    have hh0 := hH j
    have hk0 := hK j loss
    positivity
  exact hc.trans (mul_le_mul_of_nonneg_left hwidth hnonneg)

end ContinuousFlexibility.Analysis
