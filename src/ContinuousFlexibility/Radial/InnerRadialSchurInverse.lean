import ContinuousFlexibility.Radial.InnerRadialDirichletPoisson

/-!
# Both inverse identities on the actual finite weak inner domain

The same local source/trace realization supplies Dirichlet and Poisson
maps. An invertible identification of its actual Poisson flux with the
interface operator then gives a global weak solution. The reverse
identity holds on the true zero-total-flux domain by the proved local
uniqueness kernel, not by an assumed global inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

section ActualSchur

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
  ↥(innerRadialBrokenSpace D hw G forcing rowSource bordered j central column)
local notation "Src" =>
  innerRadialDomainSource D hw G forcing rowSource bordered j central column
local notation "Tr" =>
  innerRadialDomainTrace D hw G forcing rowSource bordered j central column
local notation "Flux" =>
  innerRadialDomainFlux D hw G forcing rowSource bordered j central column
local notation "Dir" =>
  innerRadialDirichletRealization D hw G forcing rowSource bordered j central column hunique hex
local notation "Pois" =>
  innerRadialPoissonRealization D hw G forcing rowSource bordered j central column hunique hex

/-- One solution of the actual finite-piece weak inner problem. -/
def innerRadialSchurInverse (S : B ≃ₗ[ℝ] (B →ₗ[ℝ] ℝ)) : H →ₗ[ℝ] W :=
  innerWeakSchurSolution Dir Pois Flux S

theorem innerRadialSchurInverse_source (S : B ≃ₗ[ℝ] (B →ₗ[ℝ] ℝ)) (F : H) :
    Src (innerRadialSchurInverse D hw G forcing rowSource bordered j central column
      hunique hex S F) = F :=
  innerWeakSchurSolution_source Src Dir Pois Flux S
    (fun f => (innerRadialDirichletRealization_source_trace D hw G forcing rowSource
      bordered j central column hunique hex f).1)
    (fun ξ => (innerRadialPoissonRealization_source_trace D hw G forcing rowSource
      bordered j central column hunique hex ξ).1) F

theorem innerRadialSchurInverse_flux (S : B ≃ₗ[ℝ] (B →ₗ[ℝ] ℝ))
    (hS : ∀ ξ, Flux (Pois ξ) = S ξ) (F : H) :
    Flux (innerRadialSchurInverse D hw G forcing rowSource bordered j central column
      hunique hex S F) = 0 :=
  innerWeakSchurSolution_flux Dir Pois Flux S hS F

/-- The actual weak equation, matching traces, physical signed potential,
and single central row all hold for this same assembled inverse. -/
theorem innerRadialSchurInverse_globalGraph (S : B ≃ₗ[ℝ] (B →ₗ[ℝ] ℝ))
    (hS : ∀ ξ, Flux (Pois ξ) = S ξ) (F : H) :
    let x := innerRadialSchurInverse D hw G forcing rowSource bordered j central column
      hunique hex S F
    InnerRadialChainWeakGraph D hw G bordered j central column
      x.val.1.1 x.val.1.2.1 (forcing F) x.val.1.2.2 (rowSource F) := by
  dsimp only
  let x := innerRadialSchurInverse D hw G forcing rowSource bordered j central column
    hunique hex S F
  have hsource : x.val.2 = F := by
    simpa only [innerRadialDomainSource_apply] using
      innerRadialSchurInverse_source D hw G forcing rowSource bordered j central column
        hunique hex S F
  have hflux : innerRadialBrokenFlux D hw G forcing central column x.val = 0 := by
    simpa only [innerRadialDomainFlux_apply] using
      innerRadialSchurInverse_flux D hw G forcing rowSource bordered j central column
        hunique hex S hS F
  have hg := (innerRadialBrokenSpace_global_iff D hw G forcing rowSource bordered j
    central column x.val).mpr ⟨x.property, hflux⟩
  simpa only [hsource] using hg

/-- The same assembled inverse is the left inverse on every actual
global weak-domain element. -/
theorem innerRadialSchurInverse_left_inverse (S : B ≃ₗ[ℝ] (B →ₗ[ℝ] ℝ))
    (hS : ∀ ξ, Flux (Pois ξ) = S ξ) (x : W)
    (hx : InnerRadialChainWeakGraph D hw G bordered j central column
      x.val.1.1 x.val.1.2.1 (forcing x.val.2) x.val.1.2.2 (rowSource x.val.2)) :
    innerRadialSchurInverse D hw G forcing rowSource bordered j central column
      hunique hex S (Src x) = x := by
  have hflux : Flux x = 0 := by
    simpa only [innerRadialDomainFlux_apply] using
      ((innerRadialBrokenSpace_global_iff D hw G forcing rowSource bordered j
        central column x.val).mp hx).2
  exact innerWeakSchurSolution_left_inverse Src Tr Dir Pois Flux S
    (fun F => (innerRadialDirichletRealization_source_trace D hw G forcing rowSource
      bordered j central column hunique hex F).1)
    (fun F => (innerRadialDirichletRealization_source_trace D hw G forcing rowSource
      bordered j central column hunique hex F).2)
    (fun ξ => (innerRadialPoissonRealization_source_trace D hw G forcing rowSource
      bordered j central column hunique hex ξ).1)
    (fun ξ => (innerRadialPoissonRealization_source_trace D hw G forcing rowSource
      bordered j central column hunique hex ξ).2)
    hS (innerRadialDomain_kernel D hw G forcing rowSource bordered j central column hunique)
    x hflux

end ActualSchur

end ContinuousFlexibility.Radial
