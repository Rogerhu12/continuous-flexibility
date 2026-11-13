import ContinuousFlexibility.Analysis.N04RealizationRootBoundaryDirections
import ContinuousFlexibility.Analysis.WholePositiveEndpointFields
import ContinuousFlexibility.Analysis.N01cAngularJetTowers
import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Genuine towers of the actual positive endpoint values

The positive source at an interior endpoint is the stored relative point
of its original negative neighbour. Its boundary value is therefore the
inverse of the original root label. The source subtype also admits an
ambient endpoint; that branch is the identity and is handled by the same
statement. No new source or root coordinate is selected.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04PositiveGeometryEndpointStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

/-- The actual positive source value has joint state-and-angle towers at
its original endpoint, for either source constructor and either side. -/
def n04PositiveGeometry_sourceBoundary_jointDirections
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (j : N04PositiveEndpointSource C i side) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ =>
        n04PositiveSourceMap j K (liftSectorParameter S C p.1)
          (n04PositiveEndpoint i side, p.2)) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let U := sectorNeighborhood S base ε ε
  have hU : IsOpen (U ×ˢ (univ : Set ℝ)) :=
    (isOpen_sectorNeighborhood S base ε ε).prod isOpen_univ
  rcases j with ⟨o, ho⟩
  cases o with
  | none =>
      let Jθ := smoothDirectionsLinearOn
        (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) ℝ) hU
      have hpair : ContDiff ℝ ∞ (fun θ : ℝ => (n04PositiveEndpoint i side, θ)) :=
        contDiff_const.prodMk contDiff_id
      apply (smoothDirections_contDiff_comp Jθ isOpen_univ hpair.contDiffOn
        (fun _ _ => mem_univ _)).congr
      intro p _
      rfl
  | some m =>
      let k : ℕ := if side then (K.cutPair m).1 else (K.cutPair m).2
      have hpair : K.cutPair m =
          (e.symm (.inl (m, false)), e.symm (.inl (m, true))) := rfl
      have hki : k = e.symm (.inl (m, !side)) := by
        dsimp only [k]
        rw [hpair]
        cases side <;> rfl
      have hi : e k = .inl (m, !side) := by
        rw [hki]
        exact e.apply_symm_apply _
      let J := n04Realization_actualRoot_currentPoint_jointDirections
        hT hS hN hfield e k m (!side) hi
      apply J.congr
      intro p _
      change n04PositiveEndpoint i side =
        (if side then C.left m else C.right m) at ho
      change canonicalCurrentPoint C K (liftSectorParameter S C p.1) k
          (if !side then C.right m else C.left m, p.2) =
        canonicalCurrentPoint C K (liftSectorParameter S C p.1) k
          (n04PositiveEndpoint i side, p.2)
      rw [ho]
      cases side <;> rfl

/-- The angular displacement of the actual endpoint source has its
genuine joint tower. Subtracting the unwrapped angle retains periodic
input data for the finite angular interpolation. -/
def n04PositiveGeometry_sourceBoundaryAngleDefect_jointDirections
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (j : N04PositiveEndpointSource C i side) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun p : (StateDirections S × ℝ) × ℝ =>
        (n04PositiveSourceMap j K (liftSectorParameter S C p.1)
          (n04PositiveEndpoint i side, p.2)).2 - p.2) := by
  let JP := n04PositiveGeometry_sourceBoundary_jointDirections hT hS hN hfield e j
  let JA := smoothDirections_postcompCLM JP (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let Jθ := smoothDirectionsLinearOn
    (ContinuousLinearMap.snd ℝ (StateDirections S × ℝ) ℝ) JP.open_domain
  apply (smoothDirectionsAdd JA (smoothDirections_realConstMul (-1 : ℝ) Jθ)).congr
  intro p _
  simp only [Function.comp_apply, ContinuousLinearMap.coe_snd', neg_one_mul,
    sub_eq_add_neg]

/-- All angular orders of the zeroth raw radial trace now have parameter
towers on the original neighborhood. This is the literal `j = 0` input
of `n04Realization_oneSidedTransport_jointDirections`. -/
def n04PositiveGeometry_sourceBoundaryAngleDefect_parameterDirections
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    {i : N04PositiveComponent D.a D.b (deriv D.w)} {side : Bool}
    (j : N04PositiveEndpointSource C i side) (b : ℕ) (θ : ℝ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun x : StateDirections S × ℝ => iteratedDeriv b
        (fun α => radialBoundaryJet
          (fun q => (n04PositiveSourceMap j K (liftSectorParameter S C x) q).2)
          (n04PositiveEndpoint i side) 0 α - α) θ) := by
  let J := n04PositiveGeometry_sourceBoundaryAngleDefect_jointDirections
    hT hS hN hfield e j
  apply (smoothDirections_angularStateSlice J b θ).congr
  intro x _
  simp only [radialBoundaryJet, iteratedDeriv_zero]

end ContinuousFlexibility.Analysis
