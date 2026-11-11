import ContinuousFlexibility.Radial.InnerRadialLocalRealization

/-!
# Canonical actual Dirichlet and Poisson realizations

Both maps are restrictions of the same source/trace inverse on the
concrete broken weak graph. Their values agree with every corresponding
family of actual local witnesses. The weak conormal functional is
expanded on the same fixed physical affine hats, so local Green flux
identities assemble without changing the Dirichlet or Poisson maps.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

section CanonicalRealizations

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n) {H : Type*}
  [AddCommGroup H] [Module ℝ H]
  (forcing : H →ₗ[ℝ] (Fin (n + 1) → RadialModeL2 D))
  (rowSource : H →ₗ[ℝ] ℝ) (bordered : Bool) (j : ℝ)
  (central : Fin (n + 1)) (column : RadialModeL2 D)
  (hunique : ∀ p, InnerRadialPieceKernelUnique D G bordered j central column p)
  (hex : ∀ F ξ p, Nonempty
    (InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p))

local notation "B" => EuclideanSpace ℝ (Fin n)
local notation "W" =>
  InnerRadialDomain D hw G forcing rowSource bordered j central column

/-- The same actual local Dirichlet solutions, selected linearly. -/
def innerRadialDirichletRealization : H →ₗ[ℝ] W :=
  (innerRadialSourceTraceEquiv D hw G forcing rowSource bordered j central column
    hunique hex).symm.toLinearMap.comp (LinearMap.inl ℝ H B)

/-- The same actual homogeneous local Poisson fields, selected linearly. -/
def innerRadialPoissonRealization : B →ₗ[ℝ] W :=
  (innerRadialSourceTraceEquiv D hw G forcing rowSource bordered j central column
    hunique hex).symm.toLinearMap.comp (LinearMap.inr ℝ H B)

theorem innerRadialDirichletRealization_apply (F : H) :
    innerRadialDirichletRealization D hw G forcing rowSource bordered j central column
      hunique hex F =
      (innerRadialSourceTraceEquiv D hw G forcing rowSource bordered j central column
        hunique hex).symm (F, 0) := by
  simp only [innerRadialDirichletRealization, LinearMap.comp_apply,
    LinearMap.inl_apply, LinearEquiv.coe_coe]

theorem innerRadialPoissonRealization_apply (ξ : B) :
    innerRadialPoissonRealization D hw G forcing rowSource bordered j central column
      hunique hex ξ =
      (innerRadialSourceTraceEquiv D hw G forcing rowSource bordered j central column
        hunique hex).symm (0, ξ) := by
  simp only [innerRadialPoissonRealization, LinearMap.comp_apply,
    LinearMap.inr_apply, LinearEquiv.coe_coe]

theorem innerRadialDirichletRealization_source_trace (F : H) :
    innerRadialDomainSource D hw G forcing rowSource bordered j central column
      (innerRadialDirichletRealization D hw G forcing rowSource bordered j central column
        hunique hex F) = F ∧
    innerRadialDomainTrace D hw G forcing rowSource bordered j central column
      (innerRadialDirichletRealization D hw G forcing rowSource bordered j central column
        hunique hex F) = 0 := by
  rw [innerRadialDirichletRealization_apply]
  have he := (innerRadialSourceTraceEquiv D hw G forcing rowSource bordered j central column
    hunique hex).apply_symm_apply (F, 0)
  rw [innerRadialSourceTraceEquiv_apply] at he
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

theorem innerRadialPoissonRealization_source_trace (ξ : B) :
    innerRadialDomainSource D hw G forcing rowSource bordered j central column
      (innerRadialPoissonRealization D hw G forcing rowSource bordered j central column
        hunique hex ξ) = 0 ∧
    innerRadialDomainTrace D hw G forcing rowSource bordered j central column
      (innerRadialPoissonRealization D hw G forcing rowSource bordered j central column
        hunique hex ξ) = ξ := by
  rw [innerRadialPoissonRealization_apply]
  have he := (innerRadialSourceTraceEquiv D hw G forcing rowSource bordered j central column
    hunique hex).apply_symm_apply (0, ξ)
  rw [innerRadialSourceTraceEquiv_apply] at he
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

/-- Identity with the existing actual local Dirichlet witnesses. -/
theorem innerRadialDirichletRealization_eq_assembled (F : H)
    (s : ∀ p, InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F 0 p) :
    innerRadialDirichletRealization D hw G forcing rowSource bordered j central column
      hunique hex F =
      innerRadialAssemblePieces D hw G forcing rowSource bordered j central column F 0 s := by
  rw [innerRadialDirichletRealization_apply]
  exact innerRadialSourceTraceEquiv_symm_eq_assembled D hw G forcing rowSource
    bordered j central column hunique hex F 0 s

/-- Identity with the existing actual local Poisson witnesses. -/
theorem innerRadialPoissonRealization_eq_assembled (ξ : B)
    (s : ∀ p, InnerRadialPieceSolution D hw G forcing rowSource bordered j central column 0 ξ p) :
    innerRadialPoissonRealization D hw G forcing rowSource bordered j central column
      hunique hex ξ =
      innerRadialAssemblePieces D hw G forcing rowSource bordered j central column 0 ξ s := by
  rw [innerRadialPoissonRealization_apply]
  exact innerRadialSourceTraceEquiv_symm_eq_assembled D hw G forcing rowSource
    bordered j central column hunique hex 0 ξ s

end CanonicalRealizations

section FluxAssembly

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n) {H : Type*}
  [AddCommGroup H] [Module ℝ H]
  (forcing : H →ₗ[ℝ] (Fin (n + 1) → RadialModeL2 D))
  (rowSource : H →ₗ[ℝ] ℝ) (bordered : Bool) (j : ℝ)
  (central : Fin (n + 1)) (column : RadialModeL2 D)

/-- The same common scalar gives each piece its original weak residual:
away from the center the column is zero. -/
theorem innerRadialAssemblePieces_residual
    (F : H) (ξ : EuclideanSpace ℝ (Fin n))
    (s : ∀ p, InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p)
    (p : Fin (n + 1)) (r : InnerRadialH1Pair D) :
    innerRadialChainResidual D central column
      (fun k => (s k).q) (fun k => (s k).potential) (forcing F)
      (s central).borderScalar p r =
      innerRadialWeakResidual D (s p).q (s p).potential (forcing F p)
        (if p = central then column else 0) (s p).borderScalar r := by
  by_cases hp : p = central
  · subst p
    rfl
  · simp only [innerRadialChainResidual, innerRadialWeakResidual_apply, if_neg hp,
      inner_zero_left, mul_zero, add_zero]

/-- The true total flux is the finite sum of the actual local outgoing
fluxes paired with restrictions of the same internal boundary vector. -/
theorem innerRadialAssemblePieces_flux
    (F : H) (ξ η : EuclideanSpace ℝ (Fin n))
    (s : ∀ p, InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p) :
    innerRadialDomainFlux D hw G forcing rowSource bordered j central column
      (innerRadialAssemblePieces D hw G forcing rowSource bordered j central column F ξ s) η =
      ∑ p, (innerChainBoundaryRestriction n p η 0 *
        innerRadialWeakResidual D (s p).q (s p).potential (forcing F p)
          (if p = central then column else 0) (s p).borderScalar
          (innerRadialAffineUnitPair D hw (G.left_pos p) (G.in_core p) (G.weight_pos p) 0) +
        innerChainBoundaryRestriction n p η 1 *
        innerRadialWeakResidual D (s p).q (s p).potential (forcing F p)
          (if p = central then column else 0) (s p).borderScalar
          (innerRadialAffineUnitPair D hw (G.left_pos p) (G.in_core p) (G.weight_pos p) 1)) := by
  rw [innerRadialDomainFlux_apply, innerRadialBrokenFlux_eq]
  change innerRadialChainFlux D hw G central column (fun p => (s p).q)
    (fun p => (s p).potential) (forcing F) (s central).borderScalar η = _
  rw [innerRadialChainFlux, innerMatchedWeakFlux_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [innerRadialChainLift, LinearMap.comp_apply, innerRadialAffineLift_apply,
    map_add, map_smul, map_smul]
  simp only [RingHom.id_apply, smul_eq_mul,
    innerRadialAssemblePieces_residual D hw G forcing rowSource bordered j central column F ξ s p]

end FluxAssembly

end ContinuousFlexibility.Radial
