module

public import ContinuousFlexibility.Radial.InnerSelectedPhysicalModels
public import ContinuousFlexibility.Radial.InnerRadialActualInverse

/-!
# One selected physical inverse for every weight

The operator below is defined from the single actual model-gap
dictionary and its actual flux matrix. Neither a weight exponent nor a
weight sign enters its definition. Matrix invertibility is the internal
construction input; the outer quantitative construction derives it
from the same selected models.

Both inverse identities concern the full physical weak graph, including
the one central scalar equation and the actual matching fluxes. The
Schur formula and Green reciprocity use this very same operator.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)
  {a CC KC CM KM η : ℝ}
  (hCentralFamily : InnerCentralPhysicalFamily CC KC X₀ η)
  (hMorseFamily : InnerMorsePhysicalFamily a S.Cstar S.chain.index CM KM η)
  (hX : 8 ≤ X₀) (hsupport : innerCentralModelBorderRadius < X₀)
  (K q : ℕ) (hq : 1 ≤ q)
  (hband : radialFrequencyBand S.chain S.Cstar (S.chain.index + K) (2 * q))
  (hS : IsUnit
    (P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).fluxMatrix)

/-- The same physical inverse is used for every weight and both signs. -/
def inverse :
    InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)) →L[ℝ]
      InnerRadialPhysicalSource D (P.chain K) (decide (q = 1)) :=
  (P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).inverse
    P.geometry.2.2.1.1 hS

/-- The proof used to establish interface invertibility does not
change the resulting physical operator. -/
theorem inverse_proof_irrel
    (hS' : IsUnit
      (P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).fluxMatrix) :
    P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS =
      P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS' := rfl

/-- The exact plus-sign Schur formula, with the adjoint of the same
actual Poisson operator used by the physical estimates. -/
theorem inverse_apply
    (F : InnerRadialPhysicalSource D (P.chain K) (decide (q = 1))) :
    let C := P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband
    P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS F =
      C.dirichlet P.geometry.2.2.1.1 F +
        C.poisson P.geometry.2.2.1.1
          (Matrix.toEuclideanCLM (n := Fin (2 * (2 * K + 1))) (𝕜 := ℝ) C.fluxMatrix⁻¹
            ((C.poisson P.geometry.2.2.1.1).adjoint F)) :=
  (P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).inverse_apply
    P.geometry.2.2.1.1 hS F

theorem inverse_eq_schur :
    let C := P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband
    P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS =
      C.dirichlet P.geometry.2.2.1.1 +
        C.poisson P.geometry.2.2.1.1 ∘L
          Matrix.toEuclideanCLM (n := Fin (2 * (2 * K + 1))) (𝕜 := ℝ) C.fluxMatrix⁻¹ ∘L
            (C.poisson P.geometry.2.2.1.1).adjoint := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro F
  rw [P.inverse_apply hCentralFamily hMorseFamily hX hsupport K q hq hband hS F]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]

/-- Every supported L² source has the actual matched weak solution,
including the scalar row in the mode-two case. -/
theorem inverse_right
    (F : InnerRadialPhysicalSource D (P.chain K) (decide (q = 1))) :
    InnerRadialPhysicalWeakGraph D P.geometry.2.2.1.1.continuous
      (P.chain K) (decide (q = 1)) ((2 : ℝ) * q)
      (innerModelChainPiece (innerMorseInnerCenter K)) (P.centralColumn q hsupport)
      (P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS F) F :=
  (P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).inverse_right
    P.geometry.2.2.1.1 hS F

/-- The same operator recovers every element of the actual physical
weak graph; no smoothness of the source is assumed. -/
theorem inverse_left
    {u F : InnerRadialPhysicalSource D (P.chain K) (decide (q = 1))}
    (hu : InnerRadialPhysicalWeakGraph D P.geometry.2.2.1.1.continuous
      (P.chain K) (decide (q = 1)) ((2 : ℝ) * q)
      (innerModelChainPiece (innerMorseInnerCenter K)) (P.centralColumn q hsupport) u F) :
    P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS F = u :=
  (P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).inverse_left
    P.geometry.2.2.1.1 hS hu

theorem inverse_graph_iff
    (u F : InnerRadialPhysicalSource D (P.chain K) (decide (q = 1))) :
    InnerRadialPhysicalWeakGraph D P.geometry.2.2.1.1.continuous
      (P.chain K) (decide (q = 1)) ((2 : ℝ) * q)
      (innerModelChainPiece (innerMorseInnerCenter K)) (P.centralColumn q hsupport) u F ↔
        P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS F = u :=
  (P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).inverse_graph_iff
    P.geometry.2.2.1.1 hS u F

theorem inverse_selfAdjoint :
    IsSelfAdjoint (P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS) :=
  (P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).inverse_selfAdjoint
    P.geometry.2.2.1.1 hS

/-- Green reciprocity holds for the same two solved L² sources. -/
theorem inverse_green
    (F H : InnerRadialPhysicalSource D (P.chain K) (decide (q = 1))) :
    ⟪P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS F, H⟫_ℝ =
      ⟪F, P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS H⟫_ℝ := by
  have hg := innerRadialPhysicalWeakGraph_green D P.geometry.2.2.1.1.continuous
    (P.chain K) (decide (q = 1)) ((2 : ℝ) * q)
    (innerModelChainPiece (innerMorseInnerCenter K)) (P.centralColumn q hsupport)
    (P.inverse_right hCentralFamily hMorseFamily hX hsupport K q hq hband hS F)
    (P.inverse_right hCentralFamily hMorseFamily hX hsupport K q hq hband hS H)
  calc
    _ = ⟪H, P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS F⟫_ℝ :=
      real_inner_comm _ _
    _ = _ := hg.symm

/-- In the ambient physical Hilbert space the same solution is the
same local Dirichlet sum plus the same Poisson-adjoint correction. -/
theorem inverse_ambient
    (F : InnerRadialPhysicalSource D (P.chain K) (decide (q = 1))) :
    let C := P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband
    (P.inverse hCentralFamily hMorseFamily hX hsupport K q hq hband hS F).val =
      C.ambientDirichlet P.geometry.2.2.1.1 F.val +
        C.ambientPoisson P.geometry.2.2.1.1
          (Matrix.toEuclideanCLM (n := Fin (2 * (2 * K + 1))) (𝕜 := ℝ) C.fluxMatrix⁻¹
            ((C.ambientPoisson P.geometry.2.2.1.1).adjoint F.val)) :=
  (P.actualChain hCentralFamily hMorseFamily hX hsupport K q hq hband).inverse_ambient
    P.geometry.2.2.1.1 hS F

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
