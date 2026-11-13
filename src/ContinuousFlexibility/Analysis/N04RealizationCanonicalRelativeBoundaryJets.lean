import ContinuousFlexibility.Analysis.N04RealizationBoundaryCompositionJets
import ContinuousFlexibility.Analysis.N04RealizationPlaneJetDirections
import ContinuousFlexibility.Analysis.N04RealizationCanonicalBoundaryInverseJets
import ContinuousFlexibility.Analysis.CanonicalClosedTransport

/-!
# Finite boundary jets of the stored relative chart

The stored reference chart is kept fixed. The actual inverse jets come
from the raw forward jets at the same inverse point, and the finite chain
rule produces the jets of canonicalCurrentPoint itself. All parameter
towers use the original state-and-angle domain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

private theorem contDiff_planeJet_on_axis
    {f : PolarPoint → PolarPoint} {r : ℝ}
    (hf : ∀ θ, ContDiffAt ℝ ∞ f (r, θ)) (n : ℕ) (v : Fin n → PolarPoint) :
    ContDiff ℝ ∞ (fun θ => iteratedFDeriv ℝ n f (r, θ) v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have hjet : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ n f) (r, θ) :=
    (hf θ).iteratedFDeriv_right (by simp)
  have hslice : ContDiffAt ℝ ∞
      (fun η => iteratedFDeriv ℝ n f (r, η)) θ :=
    hjet.comp θ (contDiffAt_const.prodMk contDiffAt_id)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => PolarPoint)
    PolarPoint v).contDiff.contDiffAt.comp θ hslice

/-- Only the raw forward boundary prefix is a parameter input. The
inverse and relative maps are the actual stored canonical functions. -/
def n04Realization_canonicalRelative_boundaryJet_directions
    {P : Type*} [TopologicalSpace P] [AddCommGroup P] [Module ℝ P]
    [IsTopologicalAddGroup P] [ContinuousSMul ℝ P]
    {U : Set P} (hU : IsOpen U)
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (ζ : P → AnnularState S × ℝ)
    (hζ : ∀ z ∈ U, ζ z ∈ stateNeighborhood S C base ε)
    (hsector : ∀ z ∈ U, stateSector S (ζ z).1)
    (m : ℕ) (r : ℝ)
    (haxis : ∀ θ, (r, θ) ∈ physicalPieceClosed S K (C.referenceState, 0) m)
    (N : ℕ)
    (J1 : SmoothDirections (U ×ˢ univ) (fun p : P × ℝ =>
      fderiv ℝ (K.chart (ζ p.1) m) (canonicalCurrentPoint C K (ζ p.1) m (r, p.2))))
    (JF : ∀ j, 2 ≤ j → j ≤ N →
      SmoothDirections (U ×ˢ univ) (fun p : P × ℝ =>
        iteratedFDeriv ℝ j (K.chart (ζ p.1) m)
          (canonicalCurrentPoint C K (ζ p.1) m (r, p.2))))
    (n : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) (v : Fin n → PolarPoint) :
    SmoothDirections (U ×ˢ univ) (fun p : P × ℝ =>
      iteratedFDeriv ℝ n (canonicalCurrentPoint C K (ζ p.1) m) (r, p.2) v) := by
  let F : PolarPoint → PolarPoint := K.chart (C.referenceState, 0) m
  let G : P × ℝ → PolarPoint → PolarPoint := fun p => K.inverseChart (ζ p.1) m
  let q : P × ℝ → PolarPoint := fun p => F (r, p.2)
  have hdomain : IsOpen (U ×ˢ (univ : Set ℝ)) := hU.prod isOpen_univ
  have hclosed := hA.boundary (C.referenceState, 0) href hsref m
  have hq (p : P × ℝ) (_hp : p ∈ U ×ˢ univ) : q p ∈ canonicalClosed S K m :=
    hclosed.1 (haxis p.2)
  have hF (θ : ℝ) : ContDiffAt ℝ ∞ F (r, θ) :=
    (hclosed.2.2.2.2.1 _ (haxis θ)).1
  have hG (p : P × ℝ) (hp : p ∈ U ×ˢ univ) :
      ContDiffAt ℝ ∞ (G p) (F (r, p.2)) :=
    n04b_inverseChart_contDiffAt_closed hA (hζ p.1 hp.1) (hsector p.1 hp.1) m (hq p hp)
  let Jinv (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
      SmoothDirections (U ×ˢ univ) (fun p : P × ℝ =>
        iteratedFDeriv ℝ j (G p) (q p)) :=
    n04Realization_planeMultilinear_directions j _ (fun w =>
      n04Realization_canonicalClosed_inverseJet_directions hdomain hA
        (fun p : P × ℝ => ζ p.1)
        (fun p hp => hζ p.1 hp.1) (fun p hp => hsector p.1 hp.1)
        m q hq J1 N JF j hj (hjn.trans hN) w)
  let Jθ : SmoothDirections (U ×ˢ univ) (fun p : P × ℝ => p.2) :=
    (smoothDirectionsLinearOn (ContinuousLinearMap.snd ℝ P ℝ) hdomain).congrOn
      (fun _ _ => by simp only [ContinuousLinearMap.coe_snd'])
  let JR (j : ℕ) (_hj : 1 ≤ j) (_hjn : j ≤ n) (w : Fin j → PolarPoint) :
      SmoothDirections (U ×ˢ univ) (fun p : P × ℝ =>
        iteratedFDeriv ℝ j F (r, p.2) w) :=
    smoothDirections_contDiff_comp Jθ isOpen_univ
      (contDiff_planeJet_on_axis hF j w).contDiffOn (fun _ _ => mem_univ _)
  let J := n04Realization_composedBoundaryJet_directions
    (f := G) (g := fun _ => F) (p := fun p : P × ℝ => (r, p.2))
    hdomain hG (fun p _ => hF p.2) n hn Jinv JR v
  refine J.congr (fun p _ => ?_)
  have he : G p ∘ F = canonicalCurrentPoint C K (ζ p.1) m := by
    funext x
    rfl
  change iteratedFDeriv ℝ n (G p ∘ F) (r, p.2) v =
    iteratedFDeriv ℝ n (canonicalCurrentPoint C K (ζ p.1) m) (r, p.2) v
  rw [he]

end ContinuousFlexibility.Analysis
