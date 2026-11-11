import ContinuousFlexibility.Radial.InnerRadialReferenceAssembly
import ContinuousFlexibility.Radial.InnerRadialPhysicalSchur
import ContinuousFlexibility.Radial.InnerInterfaceHilbertInverse
import ContinuousFlexibility.Radial.InnerIsometricRestriction

/-!
# The actual finite-chain inverse from its actual interface matrix

The source, domain, local Dirichlet sum, Poisson map and conormal matrix
are all those constructed from one model/gap dictionary. Inverting that
same finite matrix gives both inverse identities on the physical weak
graph and Green self-adjointness. The ambient formula uses the adjoint
of exactly the ambient Poisson map used by the weighted estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace Matrix.Norms.L2Operator

theorem innerMatrixEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : IsUnit S) (ξ : EuclideanSpace ℝ ι) :
    innerMatrixEquiv S hS ξ = Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) S ξ := by
  simpa only [ContinuousLinearEquiv.coe_coe] using
    congrArg (fun A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι => A ξ)
      (innerMatrixEquiv_toCLM S hS)

theorem innerMatrixEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : IsUnit S) (ξ : EuclideanSpace ℝ ι) :
    (innerMatrixEquiv S hS).symm ξ =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) S⁻¹ ξ := by
  simpa only [ContinuousLinearEquiv.coe_coe] using
    congrArg (fun A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι => A ξ)
      (innerMatrixEquiv_symm_toCLM S hS)

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "B" => EuclideanSpace ℝ (Fin n)
local notation "forcing" => innerRadialPhysicalForcing D G bordered
local notation "rowSource" => (innerRadialPhysicalRow D G bordered).toLinearMap

theorem interfaceEquiv_flux (hw : ContDiff ℝ ∞ D.w) (hS : IsUnit C.fluxMatrix)
    (ξ η : B) :
    innerRadialDomainFlux D hw.continuous G forcing rowSource bordered j central column
      (innerRadialPoissonRealization D hw.continuous G forcing rowSource bordered j
        central column (C.kernelUnique hw) (C.solution_nonempty hw) ξ) η =
      ⟪(innerMatrixEquiv C.fluxMatrix hS).toLinearEquiv ξ, η⟫_ℝ := by
  rw [ContinuousLinearEquiv.coe_toLinearEquiv, innerMatrixEquiv_apply]
  exact C.poisson_flux hw ξ η

/-- This is D+P S⁻¹ P† on the same supported physical Hilbert space. -/
def inverse (hw : ContDiff ℝ ∞ D.w) (hS : IsUnit C.fluxMatrix) : H →L[ℝ] H :=
  innerRadialPhysicalSchur D hw.continuous G bordered j central column
    (C.kernelUnique hw) (C.solution_nonempty hw) (C.dirichlet hw)
      (innerMatrixEquiv C.fluxMatrix hS).toLinearEquiv

theorem inverse_apply (hw : ContDiff ℝ ∞ D.w) (hS : IsUnit C.fluxMatrix) (F : H) :
    C.inverse hw hS F = C.dirichlet hw F + C.poisson hw
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.fluxMatrix⁻¹
        ((C.poisson hw).adjoint F)) := by
  rw [inverse, innerRadialPhysicalSchur_apply]
  simp only [← ContinuousLinearEquiv.toLinearEquiv_symm,
    ContinuousLinearEquiv.coe_toLinearEquiv, innerMatrixEquiv_symm_apply, poisson]

theorem inverse_right (hw : ContDiff ℝ ∞ D.w) (hS : IsUnit C.fluxMatrix) (F : H) :
    InnerRadialPhysicalWeakGraph D hw.continuous G bordered j central column
      (C.inverse hw hS F) F :=
  innerRadialPhysicalSchur_right_inverse D hw.continuous G bordered j central column
    (C.kernelUnique hw) (C.solution_nonempty hw) (C.dirichlet hw)
    (C.dirichlet_apply hw) (innerMatrixEquiv C.fluxMatrix hS).toLinearEquiv
    (C.interfaceEquiv_flux hw hS) F

theorem inverse_left (hw : ContDiff ℝ ∞ D.w) (hS : IsUnit C.fluxMatrix)
    {u F : H} (hu : InnerRadialPhysicalWeakGraph D hw.continuous G bordered j central column u F) :
    C.inverse hw hS F = u :=
  innerRadialPhysicalSchur_left_inverse D hw.continuous G bordered j central column
    (C.kernelUnique hw) (C.solution_nonempty hw) (C.dirichlet hw)
    (C.dirichlet_apply hw) (innerMatrixEquiv C.fluxMatrix hS).toLinearEquiv
    (C.interfaceEquiv_flux hw hS) hu

theorem inverse_graph_iff (hw : ContDiff ℝ ∞ D.w) (hS : IsUnit C.fluxMatrix) (u F : H) :
    InnerRadialPhysicalWeakGraph D hw.continuous G bordered j central column u F ↔
      C.inverse hw hS F = u :=
  innerRadialPhysicalSchur_graph_iff D hw.continuous G bordered j central column
    (C.kernelUnique hw) (C.solution_nonempty hw) (C.dirichlet hw)
    (C.dirichlet_apply hw) (innerMatrixEquiv C.fluxMatrix hS).toLinearEquiv
    (C.interfaceEquiv_flux hw hS) u F

theorem inverse_selfAdjoint (hw : ContDiff ℝ ∞ D.w) (hS : IsUnit C.fluxMatrix) :
    IsSelfAdjoint (C.inverse hw hS) :=
  innerRadialPhysicalSchur_selfAdjoint D hw.continuous G bordered j central column
    (C.kernelUnique hw) (C.solution_nonempty hw) (C.dirichlet hw)
    (C.dirichlet_apply hw) (innerMatrixEquiv C.fluxMatrix hS).toLinearEquiv
    (C.interfaceEquiv_flux hw hS)

/-- Exact identity with the ambient Schur formula. Its adjoint is the
adjoint of the same actual ambient Poisson sum, with no pairing premise. -/
theorem inverse_ambient (hw : ContDiff ℝ ∞ D.w) (hS : IsUnit C.fluxMatrix) (F : H) :
    (C.inverse hw hS F).val = C.ambientDirichlet hw F.val + C.ambientPoisson hw
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.fluxMatrix⁻¹
        ((C.ambientPoisson hw).adjoint F.val)) := by
  rw [C.inverse_apply]
  have h := innerIsometricSchur_apply (innerRadialPhysicalInclusion D G bordered)
    (C.dirichlet hw) (C.ambientDirichlet hw) (C.poisson hw) (C.ambientPoisson hw)
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.fluxMatrix⁻¹)
    (fun f => by simpa only [innerRadialPhysicalInclusion_apply] using C.dirichlet_ambient hw f)
    (fun ξ => by simpa only [innerRadialPhysicalInclusion_apply] using C.poisson_ambient hw ξ) F
  simpa only [innerRadialPhysicalInclusion_apply] using h

/-- The actual normalized interface hypotheses produce the matrix
invertibility needed above; no inverse existence is an input. -/
theorem fluxMatrix_isUnit (hw : ContDiff ℝ ∞ D.w)
    (hκ : ∀ i, 0 < C.kappa i) (Ω : Matrix (Fin n) (Fin n) ℝ)
    (hΩ : Ω.PosDef) (hcomm : Commute Ω C.referenceMatrix)
    (hsmall : ∀ sign : Bool,
      ‖innerInterfaceWeightedError C.referenceMatrix
        (innerInterfaceWeight Ω sign) C.errorMatrix‖ < 1 / 2) :
    IsUnit C.fluxMatrix :=
  (innerInterface_inverse_both_weights C.referenceMatrix Ω C.errorMatrix
    (C.referenceMatrix_posDef hw hκ) hΩ hcomm hsmall).1

end InnerRadialActualChain

end ContinuousFlexibility.Radial
