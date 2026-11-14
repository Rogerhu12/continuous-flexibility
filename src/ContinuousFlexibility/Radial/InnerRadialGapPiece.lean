module

public import ContinuousFlexibility.Radial.InnerRadialPhysicalSource
public import ContinuousFlexibility.Radial.InnerGapPhysicalRealization
public import ContinuousFlexibility.Radial.InnerChainBoundaryHilbert

/-!
# Actual positive-gap solutions in the finite weak chain

The physical coercive gap inverse and the actual classical Poisson
columns supply the local source/trace witness. The same witness has the
full outgoing matrix flux, including both off-diagonal entries.
Zero-Dirichlet uniqueness is derived from the constructed gap inverse.

A positive gap is not the central bordered piece, so it introduces no
extra scalar. The global source and boundary values are the actual
orthogonal source restriction and the actual two-cut restriction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

section GapPiece

variable (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n) (bordered : Bool) (j : ℝ)
  (central : Fin (n + 1)) (column : RadialModeL2 D)
  (piece : Fin (n + 1)) (hpiece : piece ≠ central)
  (hj : 0 < j) (s : ℝ) (hs : 0 < s)
  (hslope : ∀ r ∈ Icc (G.left piece) (G.right piece),
    s ≤ r * deriv D.w r / D.w r)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "forcing" => innerRadialPhysicalForcing D G bordered
local notation "rowSource" => innerRadialPhysicalRowLinear D G bordered
local notation "GapD" =>
  innerGapDirichletInverse D hw (le_of_lt (G.left_lt_right piece)) (G.left_pos piece)
    hj hs (G.in_core piece) (G.weight_pos piece) hslope

include hw hpiece hj hs hslope

/-- Actual zero-source gap uniqueness on the common physical domain. -/
theorem innerRadialGapPieceKernelUnique :
    InnerRadialPieceKernelUnique D G bordered j central column piece := by
  apply innerRadialPieceKernelUnique_of_value_unique D G bordered j central column piece
  intro q v borderScalar hq hv _ hweak
  have he : ∀ r ∈ innerRadialH1Zero D (G.left piece) (G.right piece),
      innerRadialWeakResidual D (q.1, q.2) v 0 0 0 r = 0 := by
    intro r hr
    simpa only [if_neg hpiece, innerRadialWeakResidual_apply, inner_zero_left,
      mul_zero, zero_mul, add_zero] using hweak r hr
  have hvalue := innerGapDirichletInverse_eq_of_weakResidual D hw
    (G.left_lt_right piece).le (G.left_pos piece) hj hs (G.in_core piece)
    (G.weight_pos piece) hslope q.1 q.2 v 0 hq hv he
  refine ⟨?_, fun hp => (hpiece hp).elim⟩
  simpa only [map_zero] using hvalue.symm

variable (columns : Fin 2 → ℝ → ℝ)
  (hcolumns : ∀ i, ContDiff ℝ ∞ (columns i))
  (hboundary : ∀ i k, columns k (innerGapEndpoint (G.left piece) (G.right piece) i) =
    if k = i then 1 else 0)
  (hhomogeneous : ∀ i r, r ∈ Icc (G.left piece) (G.right piece) →
    radialJacobi (j ^ 2) D.w (columns i) r = 0)

include columns hcolumns hboundary hhomogeneous

local notation "GapP" =>
  innerGapPoissonL2 D hw.continuous (G.left_pos piece) (G.in_core piece)
    (fun r hr => le_of_lt (G.weight_pos piece r (Ioo_subset_Icc_self hr))) columns hcolumns

/-- The same actual gap D/P solve the real local weak problem for every
physical source, with their true trace and full conormal flux. -/
theorem exists_innerRadialGapPieceSolution (F : H)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    ∃ solution : InnerRadialPieceSolution D hw.continuous G forcing rowSource
        bordered j central column F ξ piece,
      solution.q.1 = GapD (forcing F piece) + GapP (innerChainBoundaryCLM n piece ξ) ∧
      solution.borderScalar = 0 ∧
      ∀ i : Fin 2,
        innerRadialWeakResidual D solution.q solution.potential (forcing F piece)
          (if piece = central then column else 0) solution.borderScalar
          (innerRadialAffineUnitPair D hw.continuous (G.left_pos piece)
            (G.in_core piece) (G.weight_pos piece) i) =
          (innerGapFluxOperator D.w (G.left piece) (G.right piece) columns
              (innerChainBoundaryCLM n piece ξ) -
            (GapP).adjoint (forcing F piece)) i := by
  obtain ⟨d, v, hdomain, htrace, hpotential, hweak, hflux⟩ :=
    exists_innerGapDirichletPoisson_physical D hw (G.left_lt_right piece)
      (G.left_pos piece) hj hs (G.in_core piece) (G.weight_pos piece) hslope
      columns hcolumns hboundary hhomogeneous (forcing F piece)
      (innerChainBoundaryCLM n piece ξ)
  let solution : InnerRadialPieceSolution D hw.continuous G forcing rowSource
      bordered j central column F ξ piece :=
    { q := (GapD (forcing F piece) + GapP (innerChainBoundaryCLM n piece ξ), d)
      potential := v
      borderScalar := 0
      domain := hdomain
      trace := by
        funext i
        exact (congrFun htrace i).trans (innerChainBoundaryCLM_apply n piece ξ i)
      potential_relation := hpotential
      row := by simp only [if_neg hpiece]
      weak := by
        intro r hr
        rw [if_neg hpiece]
        exact hweak r hr }
  refine ⟨solution, rfl, rfl, ?_⟩
  intro i
  simpa only [solution, if_neg hpiece] using! hflux i

/-- The homogeneous witness uses exactly the actual Poisson field and
the full gap DtN block, with no forced or scalar remainder. -/
theorem exists_innerRadialGapPoissonPiece
    (ξ : EuclideanSpace ℝ (Fin n)) :
    ∃ solution : InnerRadialPieceSolution D hw.continuous G forcing rowSource
        bordered j central column 0 ξ piece,
      solution.q.1 = GapP (innerChainBoundaryCLM n piece ξ) ∧
      solution.borderScalar = 0 ∧
      ∀ i : Fin 2,
        innerRadialWeakResidual D solution.q solution.potential 0
          (if piece = central then column else 0) solution.borderScalar
          (innerRadialAffineUnitPair D hw.continuous (G.left_pos piece)
            (G.in_core piece) (G.weight_pos piece) i) =
          innerGapFluxOperator D.w (G.left piece) (G.right piece) columns
            (innerChainBoundaryCLM n piece ξ) i := by
  obtain ⟨solution, hvalue, hscalar, hflux⟩ :=
    exists_innerRadialGapPieceSolution D hw G bordered j central column piece hpiece
      hj s hs hslope columns hcolumns hboundary hhomogeneous 0 ξ
  refine ⟨solution, ?_, hscalar, ?_⟩
  · simpa only [map_zero, Pi.zero_apply, zero_add] using hvalue
  · intro i
    simpa only [map_zero, Pi.zero_apply, sub_zero] using hflux i

/-- Forgetting the proved field/flux identities gives the local
existence input for the same actual finite weak graph. -/
theorem innerRadialGapPieceSolution_nonempty (F : H)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    Nonempty (InnerRadialPieceSolution D hw.continuous G forcing rowSource
      bordered j central column F ξ piece) := by
  obtain ⟨solution, _⟩ :=
    exists_innerRadialGapPieceSolution D hw G bordered j central column piece hpiece
      hj s hs hslope columns hcolumns hboundary hhomogeneous F ξ
  exact ⟨solution⟩

end GapPiece

end ContinuousFlexibility.Radial
