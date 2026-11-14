module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryAtomDirections
public import ContinuousFlexibility.Analysis.N04RealizationMovingPointMixedBounds
public import ContinuousFlexibility.Analysis.WholePositiveReferenceGauge

/-!
# Genuine joint towers in the fixed positive reference gauge

All three fields are the literal composites used by the whole atlas.
The forward chart uses the actual inverse transport, the inverse chart
uses the actual transport at the fixed reference inverse, and the height
is the actual moving quotient. These constructions also give the pulled
height without changing the inverse point at which it is evaluated.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {U : Set E}

/-- Compose at the same moving physical point, retaining the original
state coordinate in the graph. -/
def n04PositiveGeometry_movingPointDirections
    {f : E × PolarPoint → ℝ} (J : SmoothDirections (U ×ˢ univ) f)
    {φ : E × PolarPoint → PolarPoint} (K : SmoothDirections (U ×ˢ univ) φ) :
    SmoothDirections (U ×ˢ univ) (fun z => f (z.1, φ z)) := by
  let L : (E × PolarPoint) →L[ℝ] E := ContinuousLinearMap.fst ℝ E PolarPoint
  let G := smoothDirectionsUniformProd
    ((smoothDirectionsLinear L).restrict K.open_domain (subset_univ _)) K
  have hmap : MapsTo (fun z => (L z, φ z)) (U ×ˢ univ) (U ×ˢ univ) :=
    fun z hz => ⟨hz.1, mem_univ _⟩
  exact (smoothDirections_realCompTVS G J hmap).congrOn (fun _ _ => rfl)

/-- The actual forward chart, inverse chart and height in the fixed
reference gauge have joint towers built from the three relative fields. -/
def n04PositiveGeometry_referenceGaugeDirections
    (hU : IsOpen U)
    {ψ χ : PolarPoint → PolarPoint} {h₀ : PolarPoint → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) (hh₀ : ContDiff ℝ ∞ h₀)
    {τ σ : E → PolarPoint → PolarPoint} {Q : E → PolarPoint → ℝ}
    (Jτ : SmoothDirections (U ×ˢ univ) (fun z => τ z.1 z.2))
    (Jσ : SmoothDirections (U ×ˢ univ) (fun z => σ z.1 z.2))
    (JQ : SmoothDirections (U ×ˢ univ) (fun z => Q z.1 z.2))
    (hQ : ∀ x ∈ U, ∀ p, 0 < Q x p) :
    SmoothDirections (U ×ˢ univ)
      (fun z => wholePositiveReferenceGaugeChart ψ (σ z.1) z.2) ×
    SmoothDirections (U ×ˢ univ)
      (fun z => wholePositiveReferenceGaugeInverse (τ z.1) χ z.2) ×
    SmoothDirections (U ×ˢ univ)
      (fun z => wholePositiveReferenceGaugeHeight h₀ (σ z.1) (Q z.1) z.2) := by
  let Jψ := Jσ.comp_contDiff isOpen_univ hψ.contDiffOn (fun _ _ => mem_univ _)
  let P : (E × PolarPoint) →L[ℝ] PolarPoint := ContinuousLinearMap.snd ℝ E PolarPoint
  let Jp := (smoothDirectionsLinear P).restrict (hU.prod isOpen_univ) (subset_univ _)
  let Jχ := Jp.comp_contDiff isOpen_univ hχ.contDiffOn (fun _ _ => mem_univ _)
  let Jτr := solveSmoothDirectionsPostcomp Jτ (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let Jτθ := solveSmoothDirectionsPostcomp Jτ (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let JG := smoothDirectionsProd (n04PositiveGeometry_movingPointDirections Jτr Jχ)
    (n04PositiveGeometry_movingPointDirections Jτθ Jχ)
  let JQinv := JQ.comp_contDiff isOpen_Ioi
    (contDiffOn_id.inv (fun t (ht : t ∈ Ioi (0 : ℝ)) => ht.ne'))
    (fun z hz => hQ z.1 hz.1 z.2)
  let Jden := n04PositiveGeometry_movingPointDirections JQinv Jσ
  let Jnum := Jσ.comp_contDiff isOpen_univ hh₀.contDiffOn (fun _ _ => mem_univ _)
  refine ⟨Jψ.congrOn (fun _ _ => rfl), JG.congrOn (fun _ _ => rfl),
    (Jnum.mul Jden).congrOn ?_⟩
  intro z _
  exact (div_eq_mul_inv _ _).symm.trans
    (wholePositiveReferenceGaugeHeight_eq h₀ (σ z.1) (Q z.1) z.2).symm

/-- The pulled height is composed with the same genuine inverse-chart
tower. No independent tower or replacement inverse is used. -/
def n04PositiveGeometry_pulledHeightDirections
    {h : E → PolarPoint → ℝ} {G : E → PolarPoint → PolarPoint}
    (Jh : SmoothDirections (U ×ˢ univ) (fun z => h z.1 z.2))
    (JG : SmoothDirections (U ×ˢ univ) (fun z => G z.1 z.2)) :
    SmoothDirections (U ×ˢ univ) (fun z => h z.1 (G z.1 z.2)) :=
  n04PositiveGeometry_movingPointDirections Jh JG

end ContinuousFlexibility.Analysis
