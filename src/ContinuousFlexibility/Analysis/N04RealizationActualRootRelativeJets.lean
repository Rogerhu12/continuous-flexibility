import ContinuousFlexibility.Analysis.N04RealizationCanonicalRelativeBoundaryJets
import ContinuousFlexibility.Analysis.N04RealizationRootBoundaryDirections
import ContinuousFlexibility.Analysis.N01cPhysicalFlowGraph

/-!
# Relative boundary jets from the actual fixed-root forward packet

The root label inverse has already been constructed from the retained
N01 circle. Its graph evaluates each raw forward boundary jet at the
literal stored inverse point. Finite operator reconstruction and the
closed inverse chain rule then give the actual relative chart jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04ActualRelativeStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

/-- A finite raw forward packet on the original root axis gives the
same relative chart packet, including its zeroth point tower. -/
def n04Realization_actualRoot_relativeJet_directions
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    (hK : K = n04bActualTypedAtlas hT hS hN hfield e)
    (k m : ℕ) (side : Bool) (hi : e k = .inl (m, side))
    (N : ℕ)
    (Jraw : ∀ j, 1 ≤ j → j ≤ N → ∀ w : Fin j → Fin 2,
      SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
        (fun p : (StateDirections S × ℝ) × ℝ =>
          iteratedFDeriv ℝ j (K.chart (liftSectorParameter S C p.1) k)
            (if side then C.right m else C.left m, p.2)
            (fun i => cylinderBasisVector (w i))))
    (n : ℕ) (hNn : n ≤ N) (v : Fin n → PolarPoint) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ =>
        iteratedFDeriv ℝ n (canonicalCurrentPoint C K
          (liftSectorParameter S C p.1) k)
          (if side then C.right m else C.left m, p.2) v) := by
  let U : Set (StateDirections S × ℝ) := sectorNeighborhood S base ε ε
  let c : ℝ := if side then C.right m else C.left m
  have hU : IsOpen U := sectorNeighborhood_isOpen S base ε ε
  have hdomain : IsOpen (U ×ˢ (univ : Set ℝ)) := hU.prod isOpen_univ
  by_cases hn : n = 0
  · subst n
    let J0 : SmoothDirections (U ×ˢ univ)
        (fun p : (StateDirections S × ℝ) × ℝ =>
          canonicalCurrentPoint C K (liftSectorParameter S C p.1) k (c, p.2)) := by
      simpa only [hK] using
        n04Realization_actualRoot_currentPoint_jointDirections hT hS hN hfield e k m side hi
    exact J0.congr (fun _ _ => by simp only [iteratedFDeriv_zero_apply])
  · have hnpos : 1 ≤ n := by omega
    let Θ : (StateDirections S × ℝ) × ℝ → ℝ := fun p =>
      Function.invFun (n01RootLabel S C (liftSectorParameter S C p.1) m side) p.2
    let Jθ : SmoothDirections (U ×ˢ univ) Θ :=
      n04Realization_rootLabel_inverseJointDirections hT hS hN.1.1 m side
    let Jgraph := smoothDirections_stateFlowGraph Jθ
    have hmap : MapsTo (fun p => (p.1, Θ p)) (U ×ˢ univ) (U ×ˢ univ) :=
      fun p hp => ⟨hp.1, mem_univ _⟩
    have hpoint (p : (StateDirections S × ℝ) × ℝ) (hp : p ∈ U ×ˢ univ) :
        canonicalCurrentPoint C K (liftSectorParameter S C p.1) k (c, p.2) =
          (c, Θ p) := by
      rw [hK]
      exact n04Realization_actualRoot_currentPoint_eq hT hS hN hfield e
        (liftSectorParameter_mem_stateNeighborhood hp.1 le_rfl)
        (hN.1.1.2.2.1.liftSectorParameter_sector p.1) k m side hi p.2
    let JP (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) :
        SmoothDirections (U ×ˢ univ)
          (fun p : (StateDirections S × ℝ) × ℝ =>
            iteratedFDeriv ℝ j (K.chart (liftSectorParameter S C p.1) k) (c, p.2)) :=
      n04Realization_planeMultilinear_basis_directions j _ (Jraw j hj hjN)
    let JE (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) (w : Fin j → PolarPoint) :
        SmoothDirections (U ×ˢ univ)
          (fun p : (StateDirections S × ℝ) × ℝ =>
            iteratedFDeriv ℝ j (K.chart (liftSectorParameter S C p.1) k) (c, p.2) w) :=
      solveSmoothDirectionsPostcomp (JP j hj hjN)
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => PolarPoint) PolarPoint w)
    let JM (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) (w : Fin j → PolarPoint) :
        SmoothDirections (U ×ˢ univ)
          (fun p : (StateDirections S × ℝ) × ℝ =>
            iteratedFDeriv ℝ j (K.chart (liftSectorParameter S C p.1) k)
              (canonicalCurrentPoint C K (liftSectorParameter S C p.1) k (c, p.2)) w) := by
      let Jr := smoothDirections_realCompTVS Jgraph
        (solveSmoothDirectionsPostcomp (JE j hj hjN w)
          (ContinuousLinearMap.fst ℝ ℝ ℝ)) hmap
      let Ja := smoothDirections_realCompTVS Jgraph
        (solveSmoothDirectionsPostcomp (JE j hj hjN w)
          (ContinuousLinearMap.snd ℝ ℝ ℝ)) hmap
      let Jpair := smoothDirectionsUniformProd Jr Ja
      refine Jpair.congr (fun p hp => ?_)
      simp only [Function.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd']
      rw [hpoint p hp]
    let A : ((StateDirections S × ℝ) × ℝ) → PolarPoint →L[ℝ] PolarPoint := fun p =>
      fderiv ℝ (K.chart (liftSectorParameter S C p.1) k)
        (canonicalCurrentPoint C K (liftSectorParameter S C p.1) k (c, p.2))
    let Jfirst (d : PolarPoint) : SmoothDirections (U ×ˢ univ) (fun p => A p d) :=
      (JM 1 le_rfl (hnpos.trans hNn) (fun _ => d)).congr (fun _ _ => by
        simp only [iteratedFDeriv_one_apply])
    let J1 := n04Realization_planeLinear_directions A (Jfirst (1, 0)) (Jfirst (0, 1))
    let JF (j : ℕ) (hj : 2 ≤ j) (hjN : j ≤ N) :
        SmoothDirections (U ×ˢ univ)
          (fun p : (StateDirections S × ℝ) × ℝ =>
            iteratedFDeriv ℝ j (K.chart (liftSectorParameter S C p.1) k)
              (canonicalCurrentPoint C K (liftSectorParameter S C p.1) k (c, p.2))) :=
      n04Realization_planeMultilinear_directions j _ (JM j (by omega) hjN)
    have hA : CanonicalGeometry D S C K base ε := by
      simpa only [hK] using n04b_actualTypedAtlas_partA hT hS hN hfield e
    have href := n04b_reference_valid_of_through03 hN
    have haxis (θ : ℝ) : (c, θ) ∈ physicalPieceClosed S K (C.referenceState, 0) k := by
      rw [hK]
      exact (n04Realization_actualRoot_chart_data hT hS hN hfield e
        href.1 href.2 k m side hi θ).1
    exact n04Realization_canonicalRelative_boundaryJet_directions hU hA
      href.1 href.2 (liftSectorParameter S C)
      (fun _ hz => liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (fun z _ => hN.1.1.2.2.1.liftSectorParameter_sector z)
      k c haxis N J1 JF n hnpos hNn v

end ContinuousFlexibility.Analysis
