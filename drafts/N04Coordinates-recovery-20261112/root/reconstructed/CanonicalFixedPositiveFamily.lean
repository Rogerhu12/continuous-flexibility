import ContinuousFlexibility.Analysis.CanonicalActualPositiveFiniteFactory
import ContinuousFlexibility.Analysis.N04PositiveNormalizationBuffer

/-!
# One fixed positive family from the actual endpoint data

All scalar parameters are selected before the state. The functions below
are the existing displayed transport, its inverse and the existing height
interpolation, with degree fixed by the caller. The parameter certificate
retains the chosen low bounds and the exact height-width reciprocal for
later estimates. It does not assert material growth of these constants.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

def n04FixedPositiveTransport
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (K : CanonicalData S)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi))
    (n : ℕ) (κ M Mσ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    (z : AnnularState S × ℝ) (i : N04PositiveComponent D.a D.b (deriv D.w)) :
    PolarPoint → PolarPoint :=
  oneSidedWholeComponentTransport n
    (fun side p => (n04PositiveSourceMap (j i side) K z p).2)
    (fun side p => (n04PositiveSourceMap (j i side) K z p).1)
    (n04PositiveLeft i) (n04PositiveRight i) (B.centerLeft i) (B.centerRight i)
    (κ i) (κ i) (M i) (Mσ i)

def n04FixedPositiveInverse
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (K : CanonicalData S)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi))
    (n : ℕ) (κ M Mσ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    (z : AnnularState S × ℝ) (i : N04PositiveComponent D.a D.b (deriv D.w)) :
    PolarPoint → PolarPoint :=
  oneSidedWholeComponentTransportInverse n
    (fun side p => (n04PositiveSourceMap (j i side) K z p).2)
    (fun side p => (n04PositiveSourceMap (j i side) K z p).1)
    (n04PositiveLeft i) (n04PositiveRight i) (B.centerLeft i) (B.centerRight i)
    (κ i) (κ i) (M i) (Mσ i)

def n04FixedPositiveHeight
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (K : CanonicalData S)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (n : ℕ) (δ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    (z : AnnularState S × ℝ) (i : N04PositiveComponent D.a D.b (deriv D.w)) :
    PolarPoint → ℝ :=
  positiveHeightTaylorInterpolation n (n04PositiveLeft i) (n04PositiveRight i)
    (δ i) (fun _ => 1) (fun side => n04PositiveSourceHeight (j i side) K z)

def N04FixedPositiveFamilyControls
    {D : ReferenceData}
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi))
    (n : ℕ) (κ M H Clog Mσ δ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ) : Prop :=
  ∀ i,
    let l := n04PositiveLeft i
    let r := n04PositiveRight i
    let ρ := min ((r - l) / 4) (min (B.centerLeft i - l) (r - B.centerRight i))
    0 < κ i ∧ κ i ≤ 1 ∧ (κ i)⁻¹ ≤ M i ∧ 1 ≤ M i ∧ 1 ≤ H i ∧
      0 < Clog i ∧ 1 ≤ Mσ i ∧ 0 < δ i ∧ δ i ≤ ρ ∧ δ i ≤ 1 ∧
      (δ i)⁻¹ = ρ⁻¹ + 1 + ((n + 1 : ℕ) : ℝ) * (Clog i * H i ^ (2 * n + 1) + 1) ∧
      0 < endpointFiberLower n l r (B.centerLeft i) (B.centerRight i) (κ i) (Mσ i)

/-- The common neighborhood precedes every component parameter. Each
actual function is then fixed for all states and all future output orders. -/
theorem n04Coordinates_exists_fixed_positive_family
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e : ℕ ≃ N04PieceIndex D)
    (j : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi)) (n : ℕ) :
    ∃ newBase : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∃ κ M H Clog Mσ δ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ,
        N04FixedPositiveFamilyControls B n κ M H Clog Mσ δ ∧
        let K := n04bActualTypedAtlas hT hS hN hfield e
        let τ := n04FixedPositiveTransport K j B n κ M Mσ
        let σ := n04FixedPositiveInverse K j B n κ M Mσ
        let Q := n04FixedPositiveHeight K j n δ
        (∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 → ∀ i,
          WholePositiveTransportMatching n
            (fun side => n04PositiveSourceMap (j i side) K z)
            (fun side => n04PositiveSourceHeight (j i side) K z)
            (τ z i) (σ z i) (Q z i) (n04PositiveLeft i) (n04PositiveRight i)
            (B.centerLeft i) (B.centerRight i)
            (endpointFiberLower n (n04PositiveLeft i) (n04PositiveRight i)
              (B.centerLeft i) (B.centerRight i) (κ i) (Mσ i) * (κ i / 2))
            (Real.exp 2 * H i ^ 2)) ∧
          ∀ i, τ (C.referenceState, 0) i = id ∧ σ (C.referenceState, 0) i = id ∧
            Q (C.referenceState, 0) i = (fun _ => (1 : ℝ)) := by
  classical
  obtain ⟨newBase, ε', hb, hε', hε'ε, hfamily⟩ :=
    n04Coordinates_exists_actual_wholePositive_families hT hS hN hfield e n
  choose κ M H hκ hκone hκinv hM hH hnext using fun i => hfamily i (j i)
  have hcenters (i : N04PositiveComponent D.a D.b (deriv D.w)) :
      B.centerLeft i < B.centerRight i :=
    (B.ordered i).2.1.trans ((B.ordered i).2.2.1.trans (B.ordered i).2.2.2.1)
  have hwhole := fun i => hnext i (B.centerLeft i) (B.centerRight i)
    (B.ordered i).1 (hcenters i) (B.ordered i).2.2.2.2
  dsimp only at hwhole
  choose Clog Mσ δ hClog hMσ hδ hδρ hδone hrecip hJ hmatched using hwhole
  refine ⟨newBase, ε', hb, hε', hε'ε, κ, M, H, Clog, Mσ, δ, ?_, ?_⟩
  · exact fun i => ⟨hκ i, hκone i, hκinv i, hM i, hH i, hClog i, hMσ i,
      hδ i, hδρ i, hδone i, hrecip i, hJ i⟩
  · dsimp only
    constructor
    · exact fun z hz hs i => (hmatched i z hz hs).1
    · intro i
      exact (hmatched i (C.referenceState, 0)
        (reference_mem_stateNeighborhood S C newBase hε')
        hN.1.1.2.2.1.stateSector).2 rfl

end ContinuousFlexibility.Analysis
