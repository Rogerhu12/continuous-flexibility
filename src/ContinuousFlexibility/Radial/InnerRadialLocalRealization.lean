import ContinuousFlexibility.Radial.InnerRadialBrokenTrace
import ContinuousFlexibility.Radial.InnerWeakSchur

/-!
# Actual local solutions and the common source/trace realization

A local witness contains only an actual physical H¹ field, its signed
potential product, the local weak equation, and its prescribed trace.
The scalar row is attached to the central piece exactly once. Finite
assembly produces an element of the concrete broken graph.

Actual local existence and zero-Dirichlet uniqueness then construct one
linear source/trace inverse. Equality with every assembled family of
local witnesses identifies its value with the very same local
Dirichlet/Poisson fields, without assuming linearity of chosen gradients.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

section LocalRealization

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n) {H : Type*}
  [AddCommGroup H] [Module ℝ H]
  (forcing : H →ₗ[ℝ] (Fin (n + 1) → RadialModeL2 D))
  (rowSource : H →ₗ[ℝ] ℝ) (bordered : Bool) (j : ℝ)
  (central : Fin (n + 1)) (column : RadialModeL2 D)

local notation "B" => EuclideanSpace ℝ (Fin n)
local notation "W" =>
  ↥(innerRadialBrokenSpace D hw G forcing rowSource bordered j central column)

/-- A true local solution on one actual piece. These are the clauses
proved by the local retained-cell and positive-gap realizations. -/
structure InnerRadialPieceSolution (F : H) (ξ : B) (p : Fin (n + 1)) where
  q : InnerRadialH1Pair D
  potential : RadialModeL2 D
  borderScalar : ℝ
  domain : q ∈ innerRadialH1Domain D hw (G.left_pos p) (G.in_core p) (G.weight_pos p)
  trace : innerRadialH1Trace D hw (G.left_pos p) (G.in_core p) (G.weight_pos p) q =
    innerChainBoundaryRestriction n p ξ
  potential_relation : InnerRadialPotentialClass D j (G.left p) (G.right p) q.1 potential
  row : if p = central then
      if bordered then ⟪column, q.1⟫_ℝ = rowSource F
        else borderScalar = 0 ∧ rowSource F = 0
      else borderScalar = 0
  weak : ∀ r ∈ innerRadialH1Zero D (G.left p) (G.right p),
    innerRadialWeakResidual D q potential (forcing F p)
      (if p = central then column else 0) borderScalar r = 0

def innerRadialDomainSource : W →ₗ[ℝ] H :=
  (innerRadialBrokenSource D).comp
    (innerRadialBrokenSpace D hw G forcing rowSource bordered j central column).subtype

def innerRadialDomainTrace : W →ₗ[ℝ] B :=
  (innerRadialBrokenTrace D hw G).comp
    (innerRadialBrokenSpace D hw G forcing rowSource bordered j central column).subtype

def innerRadialDomainFlux : W →ₗ[ℝ] (B →ₗ[ℝ] ℝ) :=
  (innerRadialBrokenFlux D hw G forcing central column).comp
    (innerRadialBrokenSpace D hw G forcing rowSource bordered j central column).subtype

@[simp] theorem innerRadialDomainSource_apply (x : W) :
    innerRadialDomainSource D hw G forcing rowSource bordered j central column x = x.val.2 := rfl

@[simp] theorem innerRadialDomainTrace_apply (x : W) :
    innerRadialDomainTrace D hw G forcing rowSource bordered j central column x =
      innerRadialChainTrace D hw G x.val.1.1 := rfl

@[simp] theorem innerRadialDomainFlux_apply (x : W) :
    innerRadialDomainFlux D hw G forcing rowSource bordered j central column x =
      innerRadialBrokenFlux D hw G forcing central column x.val := rfl

/-- Assemble the actual local witnesses. Only the central witness
supplies the common scalar; all other columns are identically zero. -/
def innerRadialAssemblePieces (F : H) (ξ : B)
    (s : ∀ p, InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p) :
    W := by
  refine ⟨((fun p => (s p).q, (fun p => (s p).potential, (s central).borderScalar)), F), ?_⟩
  apply (mem_innerRadialBrokenSpace D hw G forcing rowSource bordered j central column _).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (innerRadialChainDomain_trace_iff D hw G _).mpr
    exact ⟨ξ, fun p => ⟨(s p).domain, (s p).trace⟩⟩
  · exact fun p => (s p).potential_relation
  · simpa only [if_pos rfl, ite_true] using (s central).row
  · intro p r hr
    have he := (s p).weak r hr
    by_cases hp : p = central
    · subst p
      simpa only [innerRadialChainResidual] using he
    · simpa only [innerRadialChainResidual, if_neg hp, innerRadialWeakResidual_apply,
        inner_zero_left, mul_zero, add_zero] using he

theorem innerRadialAssemblePieces_source (F : H) (ξ : B)
    (s : ∀ p, InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p) :
    innerRadialDomainSource D hw G forcing rowSource bordered j central column
      (innerRadialAssemblePieces D hw G forcing rowSource bordered j central column F ξ s) = F := rfl

theorem innerRadialAssemblePieces_trace (F : H) (ξ : B)
    (s : ∀ p, InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p) :
    innerRadialDomainTrace D hw G forcing rowSource bordered j central column
      (innerRadialAssemblePieces D hw G forcing rowSource bordered j central column F ξ s) = ξ := by
  rw [innerRadialDomainTrace_apply]
  exact innerRadialChainTrace_eq D hw G (fun p => (s p).trace)

/-- Actual per-piece existence gives surjectivity of the whole
source/trace map. No global weak equation or interface inverse is used. -/
theorem innerRadialDomain_source_trace_exists
    (hex : ∀ F ξ p, Nonempty
      (InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p))
    (F : H) (ξ : B) :
    ∃ x : W,
      innerRadialDomainSource D hw G forcing rowSource bordered j central column x = F ∧
      innerRadialDomainTrace D hw G forcing rowSource bordered j central column x = ξ := by
  let s := fun p => Classical.choice (hex F ξ p)
  exact ⟨innerRadialAssemblePieces D hw G forcing rowSource bordered j central column F ξ s,
    innerRadialAssemblePieces_source D hw G forcing rowSource bordered j central column F ξ s,
    innerRadialAssemblePieces_trace D hw G forcing rowSource bordered j central column F ξ s⟩

theorem innerRadialDomain_kernel
    (hunique : ∀ p, InnerRadialPieceKernelUnique D G bordered j central column p)
    (x : W)
    (hsource : innerRadialDomainSource D hw G forcing rowSource bordered j central column x = 0)
    (htrace : innerRadialDomainTrace D hw G forcing rowSource bordered j central column x = 0) :
    x = 0 := by
  apply Subtype.ext
  apply innerRadialBrokenSpace_kernel D hw G forcing rowSource bordered j central column
    hunique x.val x.property
  · simpa only [innerRadialDomainSource_apply] using hsource
  · simpa only [innerRadialBrokenTrace_apply, innerRadialDomainTrace_apply] using htrace

/-- The same concrete broken graph, identified linearly by its actual
source and internal trace. -/
def innerRadialSourceTraceEquiv
    (hunique : ∀ p, InnerRadialPieceKernelUnique D G bordered j central column p)
    (hex : ∀ F ξ p, Nonempty
      (InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p)) :
    W ≃ₗ[ℝ] (H × B) :=
  innerWeakSourceTraceEquiv
    (innerRadialDomainSource D hw G forcing rowSource bordered j central column)
    (innerRadialDomainTrace D hw G forcing rowSource bordered j central column)
    (innerRadialDomain_kernel D hw G forcing rowSource bordered j central column hunique)
    (innerRadialDomain_source_trace_exists D hw G forcing rowSource bordered j central column hex)

@[simp] theorem innerRadialSourceTraceEquiv_apply
    (hunique : ∀ p, InnerRadialPieceKernelUnique D G bordered j central column p)
    (hex : ∀ F ξ p, Nonempty
      (InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p))
    (x : W) :
    innerRadialSourceTraceEquiv D hw G forcing rowSource bordered j central column hunique hex x =
      (innerRadialDomainSource D hw G forcing rowSource bordered j central column x,
       innerRadialDomainTrace D hw G forcing rowSource bordered j central column x) := rfl

/-- Every actual family of local witnesses is the same source/trace
inverse. This identifies the canonical realization with the existing
local G and Poisson fields, including their derivative and scalar. -/
theorem innerRadialSourceTraceEquiv_symm_eq_assembled
    (hunique : ∀ p, InnerRadialPieceKernelUnique D G bordered j central column p)
    (hex : ∀ F ξ p, Nonempty
      (InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p))
    (F : H) (ξ : B)
    (s : ∀ p, InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p) :
    (innerRadialSourceTraceEquiv D hw G forcing rowSource bordered j central column hunique hex).symm
      (F, ξ) = innerRadialAssemblePieces D hw G forcing rowSource bordered j central column F ξ s := by
  apply (innerRadialSourceTraceEquiv D hw G forcing rowSource bordered j central column
    hunique hex).injective
  rw [LinearEquiv.apply_symm_apply]
  change (F, ξ) =
    (innerRadialDomainSource D hw G forcing rowSource bordered j central column
      (innerRadialAssemblePieces D hw G forcing rowSource bordered j central column F ξ s),
     innerRadialDomainTrace D hw G forcing rowSource bordered j central column
      (innerRadialAssemblePieces D hw G forcing rowSource bordered j central column F ξ s))
  rw [innerRadialAssemblePieces_source, innerRadialAssemblePieces_trace]

end LocalRealization

end ContinuousFlexibility.Radial
