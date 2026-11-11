import ContinuousFlexibility.Radial.InnerRadialActualRealization
import ContinuousFlexibility.Radial.InnerRadialFluxAssembly
import ContinuousFlexibility.Radial.InnerRadialPhysicalDirichlet
import ContinuousFlexibility.Radial.InnerBorderDirichletBound
import ContinuousFlexibility.Radial.InnerChainErrorAssembly

/-!
# One actual finite-chain Dirichlet/Poisson/interface assembly

The sole input is the actual model-or-gap dictionary on the fixed
physical chain. Proved local realizations construct its canonical weak
domain maps. Their physical values equal the exact ambient sums used by
the estimates, including the one central scalar. The conormal matrix is
the same full reference plus the same model error.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

structure InnerRadialActualChain (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) (bordered : Bool) (j : ℝ)
    (central : Fin (n + 1)) (column : RadialModeL2 D) where
  piece : ∀ p, InnerRadialActualPiece D G bordered j central column p

section Fields

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (hw : Continuous D.w)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "forcing" => innerRadialPhysicalForcing D G bordered
local notation "rowSource" => (innerRadialPhysicalRow D G bordered).toLinearMap

theorem innerRadialPieceSolution_projection_fixed {F : H}
    {ξ : EuclideanSpace ℝ (Fin n)} {p : Fin (n + 1)}
    (s : InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p) :
    innerBorderPieceProjection (radialHilbertMeasure D)
      (fun p => Ioo (G.left p) (G.right p)) central p
        (WithLp.toLp 2 (s.q.1, s.borderScalar)) =
      WithLp.toLp 2 (s.q.1, s.borderScalar) := by
  have hfield := innerRadialH1Domain_piece_projection D hw
    (G.left_pos p) (G.in_core p) (G.weight_pos p) s.domain
  rw [innerBorderPieceProjection_apply, WithLp.toLp_fst, WithLp.toLp_snd, hfield]
  apply congrArg (fun c : ℝ => (WithLp.toLp 2 (s.q.1, c) :
    InnerBorderL2 (radialHilbertMeasure D)))
  by_cases hp : p = central
  · rw [if_pos hp]
  · rw [if_neg hp]
    exact (by simpa only [if_neg hp] using s.row : s.borderScalar = 0).symm

/-- Local scalar coordinates sum to the one central coordinate. -/
theorem innerRadialPieceSolution_sum_fields {F : H}
    {ξ : EuclideanSpace ℝ (Fin n)}
    (s : ∀ p, InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p) :
    (∑ p, (WithLp.toLp 2 ((s p).q.1, (s p).borderScalar) :
      InnerBorderL2 (radialHilbertMeasure D))) =
      WithLp.toLp 2 (∑ p, (s p).q.1, (s central).borderScalar) := by
  rw [← WithLp.toLp_sum]
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · simp only [Prod.fst_sum]
  · simp only [Prod.snd_sum]
    apply Finset.sum_eq_single central
    · intro p _ hp
      simpa only [if_neg hp] using (s p).row
    · intro hc
      exact (hc (Finset.mem_univ central)).elim

end Fields

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "B" => EuclideanSpace ℝ (Fin n)
local notation "ambient" => InnerBorderL2 (radialHilbertMeasure D)
local notation "forcing" => innerRadialPhysicalForcing D G bordered
local notation "rowSource" => (innerRadialPhysicalRow D G bordered).toLinearMap
local notation "sets" => (fun p : Fin (n + 1) => Ioo (G.left p) (G.right p))
local notation "projection" => innerBorderPieceProjection (radialHilbertMeasure D) sets central

theorem kernelUnique (hw : ContDiff ℝ ∞ D.w) :
    ∀ p, InnerRadialPieceKernelUnique D G bordered j central column p :=
  fun p => (C.piece p).kernelUnique hw

theorem solution_nonempty (hw : ContDiff ℝ ∞ D.w) :
    ∀ F ξ p, Nonempty (InnerRadialPieceSolution D hw.continuous G forcing rowSource
      bordered j central column F ξ p) :=
  fun F ξ p => (C.piece p).solution_nonempty hw F ξ

/-- The same local Dirichlet operators, restricted and zero extended
on the actual physical Hilbert space. -/
def ambientDirichlet (hw : ContDiff ℝ ∞ D.w) : ambient →L[ℝ] ambient :=
  innerBorderDirichletSum (radialHilbertMeasure D) sets central
    (fun p => (C.piece p).dirichlet hw)

/-- The same local model and gap Poisson fields on the actual cuts. -/
def ambientPoisson (hw : ContDiff ℝ ∞ D.w) : B →L[ℝ] ambient :=
  ∑ p, projection p ∘L (C.piece p).poisson hw.continuous ∘L innerChainBoundaryCLM n p

def dirichletLinear (hw : ContDiff ℝ ∞ D.w) : H →ₗ[ℝ] H :=
  innerRadialPhysicalDirichlet D hw.continuous G bordered j central column
    (C.kernelUnique hw) (C.solution_nonempty hw)

def poisson (hw : ContDiff ℝ ∞ D.w) : B →L[ℝ] H :=
  innerRadialPhysicalPoisson D hw.continuous G bordered j central column
    (C.kernelUnique hw) (C.solution_nonempty hw)

/-- The canonical weak Dirichlet field is exactly the ambient direct
sum built from the original local inverses. -/
theorem dirichletLinear_ambient (hw : ContDiff ℝ ∞ D.w) (F : H) :
    (C.dirichletLinear hw F).val = C.ambientDirichlet hw F.val := by
  choose s hs using fun p => (C.piece p).exists_solution hw F (0 : B)
  have hlocal (p : Fin (n + 1)) :
      (WithLp.toLp 2 ((s p).q.1, (s p).borderScalar) : ambient) =
        (C.piece p).dirichlet hw (projection p F.val) := by
    simpa only [map_zero, add_zero] using hs p
  calc
    (C.dirichletLinear hw F).val =
        WithLp.toLp 2 (∑ p, (s p).q.1, (s central).borderScalar) :=
      innerRadialPhysicalDirichlet_value_eq_assembled D hw.continuous G bordered j
        central column (C.kernelUnique hw) (C.solution_nonempty hw) F s
    _ = ∑ p, (WithLp.toLp 2 ((s p).q.1, (s p).borderScalar) : ambient) :=
      (innerRadialPieceSolution_sum_fields hw.continuous s).symm
    _ = ∑ p, projection p ((C.piece p).dirichlet hw (projection p F.val)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← hlocal p]
      exact (innerRadialPieceSolution_projection_fixed hw.continuous (s p)).symm
    _ = C.ambientDirichlet hw F.val := by
      simp only [ambientDirichlet, innerBorderDirichletSum, innerProjectedDirichletSum,
        sum_apply, ContinuousLinearMap.comp_apply]

/-- The canonical weak Poisson field is exactly the same ambient
model-plus-gap sum used by the two weighted estimates. -/
theorem poisson_ambient (hw : ContDiff ℝ ∞ D.w) (ξ : B) :
    (C.poisson hw ξ).val = C.ambientPoisson hw ξ := by
  choose s hs _hflux using fun p => (C.piece p).exists_poisson hw ξ
  calc
    (C.poisson hw ξ).val =
        WithLp.toLp 2 (∑ p, (s p).q.1, (s central).borderScalar) :=
      innerRadialPhysicalPoisson_value_eq_assembled D hw.continuous G bordered j
        central column (C.kernelUnique hw) (C.solution_nonempty hw) ξ s
    _ = ∑ p, (WithLp.toLp 2 ((s p).q.1, (s p).borderScalar) : ambient) :=
      (innerRadialPieceSolution_sum_fields hw.continuous s).symm
    _ = ∑ p, projection p ((C.piece p).poisson hw.continuous
        (innerChainBoundaryCLM n p ξ)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← hs p]
      exact (innerRadialPieceSolution_projection_fixed hw.continuous (s p)).symm
    _ = C.ambientPoisson hw ξ := by
      simp only [ambientPoisson, sum_apply, ContinuousLinearMap.comp_apply]

/-- Continuity follows from that exact finite sum; it is not an input
to the weak source/trace construction. -/
def dirichlet (hw : ContDiff ℝ ∞ D.w) : H →L[ℝ] H :=
  innerRadialPhysicalDirichletCLMOfAmbient D hw.continuous G bordered j central column
    (C.kernelUnique hw) (C.solution_nonempty hw) (C.ambientDirichlet hw)
      (fun F => (C.dirichletLinear_ambient hw F).symm)

@[simp] theorem dirichlet_apply (hw : ContDiff ℝ ∞ D.w) (F : H) :
    C.dirichlet hw F = C.dirichletLinear hw F := by
  simp only [dirichlet, innerRadialPhysicalDirichletCLMOfAmbient_apply, dirichletLinear]

theorem dirichlet_ambient (hw : ContDiff ℝ ∞ D.w) (F : H) :
    (C.dirichlet hw F).val = C.ambientDirichlet hw F.val := by
  rw [C.dirichlet_apply]
  exact C.dirichletLinear_ambient hw F

theorem dirichlet_norm_le_ambient (hw : ContDiff ℝ ∞ D.w) :
    ‖C.dirichlet hw‖ ≤ ‖C.ambientDirichlet hw‖ :=
  norm_innerRadialPhysicalDirichletCLMOfAmbient_le D hw.continuous G bordered j
    central column (C.kernelUnique hw) (C.solution_nonempty hw) (C.ambientDirichlet hw)
      (fun F => (C.dirichletLinear_ambient hw F).symm)

def referenceMatrix : Matrix (Fin n) (Fin n) ℝ :=
  innerChainErrorMatrix n (fun p => (C.piece p).referenceMatrix)

def errorMatrix : Matrix (Fin n) (Fin n) ℝ :=
  innerChainErrorMatrix n (fun p => (C.piece p).errorMatrix)

def fluxMatrix : Matrix (Fin n) (Fin n) ℝ := C.referenceMatrix + C.errorMatrix

theorem fluxMatrix_toCLM :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.fluxMatrix =
      innerInterfaceBlockSum (innerChainBoundaryCLM n) (fun p =>
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
          ((C.piece p).referenceMatrix + (C.piece p).errorMatrix)) := by
  simp only [fluxMatrix, referenceMatrix, errorMatrix, map_add,
    innerChainErrorMatrix_toEuclideanCLM, innerInterfaceBlockSum,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    Finset.sum_add_distrib]

/-- The actual canonical Poisson conormal is precisely S0+E, with the
full positive-gap blocks retained in S0. -/
theorem poisson_flux (hw : ContDiff ℝ ∞ D.w) (ξ η : B) :
    innerRadialDomainFlux D hw.continuous G forcing rowSource bordered j central column
      (innerRadialPoissonRealization D hw.continuous G forcing rowSource bordered j
        central column (C.kernelUnique hw) (C.solution_nonempty hw) ξ) η =
      ⟪Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.fluxMatrix ξ, η⟫_ℝ := by
  choose solutions _hfields hflux using fun ξ p => (C.piece p).exists_poisson hw ξ
  rw [C.fluxMatrix_toCLM]
  exact innerRadialPoissonRealization_flux_blockSum D hw.continuous G forcing rowSource
    bordered j central column (C.kernelUnique hw) (C.solution_nonempty hw)
    (fun p => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
      ((C.piece p).referenceMatrix + (C.piece p).errorMatrix)) solutions hflux ξ η

end InnerRadialActualChain

end ContinuousFlexibility.Radial
