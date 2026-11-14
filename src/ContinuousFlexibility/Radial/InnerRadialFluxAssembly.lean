module

public import ContinuousFlexibility.Radial.InnerRadialDirichletPoisson
public import ContinuousFlexibility.Radial.InnerChainBoundaryHilbert

/-!
# The actual finite conormal matrix

Actual local affine-hat fluxes assemble by the same two-cut restriction
as the weak graph. This identifies the canonical Poisson conormal
functional with the full sum of restricted local DtN operators. No
off-diagonal gap entry or central scalar contribution is discarded.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped InnerProductSpace BigOperators

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n) {H : Type*}
  [AddCommGroup H] [Module ℝ H]
  (forcing : H →ₗ[ℝ] (Fin (n + 1) → RadialModeL2 D))
  (rowSource : H →ₗ[ℝ] ℝ) (bordered : Bool) (j : ℝ)
  (central : Fin (n + 1)) (column : RadialModeL2 D)

/-- Local actual conormal coordinates give their genuine Euclidean
boundary pairing on the same matched field. -/
theorem innerRadialAssemblePieces_flux_inner
    (F : H) (ξ η : EuclideanSpace ℝ (Fin n))
    (s : ∀ p, InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p)
    (outgoing : Fin (n + 1) → EuclideanSpace ℝ (Fin 2))
    (hflux : ∀ p i,
      innerRadialWeakResidual D (s p).q (s p).potential (forcing F p)
        (if p = central then column else 0) (s p).borderScalar
        (innerRadialAffineUnitPair D hw (G.left_pos p) (G.in_core p) (G.weight_pos p) i) =
        outgoing p i) :
    innerRadialDomainFlux D hw G forcing rowSource bordered j central column
      (innerRadialAssemblePieces D hw G forcing rowSource bordered j central column F ξ s) η =
      ∑ p, ⟪outgoing p, innerChainBoundaryCLM n p η⟫_ℝ := by
  rw [innerRadialAssemblePieces_flux]
  apply Finset.sum_congr rfl
  intro p _
  rw [hflux p 0, hflux p 1]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
    conj_trivial, innerChainBoundaryCLM_apply]

/-- The same canonical Poisson fields have the actual finite sum of
full local conormal blocks. The local flux identities are supplied by
the already proved physical model and gap realizations. -/
theorem innerRadialPoissonRealization_flux_blockSum
    (hunique : ∀ p, InnerRadialPieceKernelUnique D G bordered j central column p)
    (hex : ∀ F ξ p, Nonempty
      (InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p))
    (blocks : Fin (n + 1) →
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (solutions : ∀ ξ p, InnerRadialPieceSolution D hw G forcing rowSource
      bordered j central column 0 ξ p)
    (hblocks : ∀ ξ p i,
      innerRadialWeakResidual D (solutions ξ p).q (solutions ξ p).potential 0
        (if p = central then column else 0) (solutions ξ p).borderScalar
        (innerRadialAffineUnitPair D hw (G.left_pos p) (G.in_core p) (G.weight_pos p) i) =
        blocks p (innerChainBoundaryCLM n p ξ) i)
    (ξ η : EuclideanSpace ℝ (Fin n)) :
    innerRadialDomainFlux D hw G forcing rowSource bordered j central column
      (innerRadialPoissonRealization D hw G forcing rowSource bordered j central column
        hunique hex ξ) η =
      ⟪innerInterfaceBlockSum (innerChainBoundaryCLM n) blocks ξ, η⟫_ℝ := by
  rw [innerRadialPoissonRealization_eq_assembled D hw G forcing rowSource
    bordered j central column hunique hex ξ (solutions ξ)]
  calc
    _ = ∑ p, ⟪blocks p (innerChainBoundaryCLM n p ξ),
        innerChainBoundaryCLM n p η⟫_ℝ := by
      apply innerRadialAssemblePieces_flux_inner D hw G forcing rowSource
        bordered j central column 0 ξ η (solutions ξ)
      intro p i
      simpa only [map_zero, Pi.zero_apply] using hblocks ξ p i
    _ = ⟪innerInterfaceBlockSum (innerChainBoundaryCLM n) blocks ξ, η⟫_ℝ :=
      (innerInterfaceBlockSum_inner (innerChainBoundaryCLM n) blocks ξ η).symm

end ContinuousFlexibility.Radial
