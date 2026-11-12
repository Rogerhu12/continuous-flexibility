import ContinuousFlexibility.Radial.MatchedInnerPhysicalGraph
import ContinuousFlexibility.Radial.InnerRadialActualInverse

/-!
# The actual finite-chain inverse is the existing matching inverse

The finite-chain inverse is the original `InnerRadialActualChain.inverse`.
Its proved physical weak graph, followed by the frozen graph bridge and
matching uniqueness, identifies its value with the same matching operator.
No second inverse or source space is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements
open scoped ContDiff Matrix.Norms.L2Operator

section Identification

variable {D : ReferenceData}
  (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
  (hw : ContDiff ℝ ∞ D.w) {n : ℕ} (G : InnerRadialChainGeometry D n)
  (M : RadialMatchingData D)
  (hleft : M.innerLeft = G.left 0) (hright : M.innerRight = G.right (Fin.last n))
  (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
  (central : Fin (n + 1)) (column : RadialModeL2 D)
  (hcolumn : column = matchingBorderVector D hD hB)
  (hcolfix : innerL2PieceProjection (radialHilbertMeasure D)
    (Ioo (G.left central) (G.right central)) column = column)
  (C : InnerRadialActualChain D G (decide (M.frequency = 2))
    (M.frequency : ℝ) central column)
  (hS : IsUnit C.fluxMatrix) (hM : MatchingLocalRealizations D M)

local notation "H" => InnerRadialPhysicalSource D G (decide (M.frequency = 2))

include hD hB hw G M hleft hright hsub central column hcolumn hcolfix C hS hM

/-- Identification on the original supported source, including its
single admissible scalar when the frequency is two. -/
theorem matchedInnerActualInverse_eq_innerInverse (F : H) :
    M.innerInverse (F.val.fst, F.val.snd) =
      ((C.inverse hw hS F).val.fst, (C.inverse hw hS F).val.snd) := by
  apply hM.2.1
  exact matchedInnerPhysicalWeakGraph_to_modeGraph hD hB hw G M hleft hright hsub
    central column hcolumn hcolfix (C.inverse_right hw hS F)

/-- The matching value has exactly the ambient Schur formula of the
same actual finite chain. -/
theorem matchedInnerActualInverse_ambient (F : H) :
    WithLp.toLp 2 (M.innerInverse (F.val.fst, F.val.snd)) =
      C.ambientDirichlet hw F.val + C.ambientPoisson hw
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.fluxMatrix⁻¹
          ((C.ambientPoisson hw).adjoint F.val)) := by
  rw [matchedInnerActualInverse_eq_innerInverse hD hB hw G M hleft hright hsub
    central column hcolumn hcolfix C hS hM F]
  change WithLp.toLp 2 (WithLp.ofLp (C.inverse hw hS F).val) = _
  rw [WithLp.toLp_ofLp]
  exact C.inverse_ambient hw hS F

end Identification

end ContinuousFlexibility.Radial
