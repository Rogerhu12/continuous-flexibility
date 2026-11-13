import ContinuousFlexibility.Analysis.N04RealizationFixedPositiveLogBounds
import ContinuousFlexibility.Analysis.N04RealizationPositiveHeightParameterPrefix
import ContinuousFlexibility.Analysis.N04RealizationPositiveHeightTaylorJets

/-!
# Raw endpoint jets give the same actual positive height jets

The original typed atlas, source selectors, and selected collar are kept.
Actual root geometry supplies smoothness and positivity. The retained
low logarithmic certificate supplies the exponential margin. The only
quantitative inputs are the raw endpoint jets, their reciprocal values,
and the cost of the already selected collar.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04Realization_actualFixedPositiveHeight_shifted_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    {newBase : ℕ} {ε' : ℝ} (hb : base ≤ newBase) (hε : ε' ≤ ε)
    (src : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    {B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) (tsupport D.chi)}
    {κ M H Clog Mσ δ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ}
    (hcontrols : N04FixedPositiveFamilyControls B 3 κ M H Clog Mσ δ)
    (hlog : ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
      ∀ i side j, 0 < j → j ≤ 3 → ∀ θ,
        |positiveHeightTaylorData (n04PositiveLeft i) (n04PositiveRight i) (fun _ => 1)
          (fun side => n04PositiveSourceHeight (src i side)
            (n04bActualTypedAtlas hT hS hN hfield e) z) side j θ| ≤
          Clog i * H i ^ 7)
    (k a b : ℕ) (RH : ℝ) :
    ∃ C₀ : ℝ, ∃ d : ℕ, 1 ≤ C₀ ∧ 1 ≤ d ∧
      ∀ U : Set X, IsOpen U → ∀ state : X → AnnularState S × ℝ,
      (∀ x ∈ U, state x ∈ stateNeighborhood S C newBase ε') →
      (∀ x ∈ U, stateSector S (state x).1) →
      ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ JH : ∀ side, ∀ j : ℕ, j ≤ 3 → ∀ u θ,
        SmoothDirections U (fun x => iteratedDeriv u
          (radialBoundaryJet (n04PositiveSourceHeight (src i side)
            (n04bActualTypedAtlas hT hS hN hfield e) (state x))
            (n04PositiveEndpoint i side) j) θ),
      ∀ inv : Bool,
      ∃ RQ : MixedJetRegularity U univ (fun y q => if inv then
          (n04FixedPositiveHeight (n04bActualTypedAtlas hT hS hN hfield e)
            src 3 δ (state y) i q)⁻¹
          else n04FixedPositiveHeight (n04bActualTypedAtlas hT hS hN hfield e)
            src 3 δ (state y) i q),
        ∀ x ∈ U, ∀ (P : X → Prop) (v : Fin k → X), (∀ t, P (v t)) →
        ∀ W Mjet scale : ℝ, 0 ≤ W → W ≤ RH → 1 ≤ Mjet → 1 ≤ scale →
        (δ i)⁻¹ ≤ Mjet → ∀ budget shift : ℕ,
        (∀ side θ, (n04PositiveSourceHeight (src i side)
          (n04bActualTypedAtlas hT hS hN hfield e) (state x)
          (n04PositiveEndpoint i side, θ))⁻¹ ≤ Mjet) →
        (∀ side, ∀ j : ℕ, ∀ hj : j ≤ 3, ∀ t : ℕ, t ≤ k →
          ∀ u : ℕ, u ≤ a + b → ∀ θ, ∀ w : Fin t → X, (∀ l, P (w l)) →
          ‖(JH side j hj u θ).D t x w‖ ≤ Mjet * parameterHeightWeight W t *
            scale ^ (((u + shift * t : ℕ) : ℝ) / ((budget : ℝ) + 1))) →
        ∀ q : PolarPoint,
          ‖(RQ.parameter a b q (mem_univ q)).D k x v‖ ≤
            C₀ * Mjet ^ d * parameterHeightWeight W k *
              scale ^ (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) := by
  obtain ⟨C₀, d, hC₀, hd, hbound⟩ :=
    n04Realization_positiveHeightTaylor_shifted_parameter_bound (X := X) 3 k a b RH
  refine ⟨C₀, d, hC₀, hd, ?_⟩
  intro U hU state hstate hsector i JH inv
  have hstate₀ (y : X) (hy : y ∈ U) : state y ∈ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C hb hε (hstate y hy)
  have hroot (y : X) (hy : y ∈ U) (side : Bool) (θ : ℝ) :=
    (n04Coordinates_actualAtlas_positiveEndpoint_of_source
      hT hS hN hfield e (src i side) (hstate₀ y hy) (hsector y hy)).height_root θ
  obtain ⟨_hκ, _hκone, _hκinv, _hM, _hH, _hClog, _hMσ,
      hδ, _hδρ, hδone, _hrecip, _hJ⟩ := hcontrols i
  have hlow := n04Realization_actualFixedPositiveHeight_log_data
    (K := n04bActualTypedAtlas hT hS hN hfield e)
    src hcontrols hlog U state hstate hsector i
  let RQ : MixedJetRegularity U univ (fun y q => if inv then
      (n04FixedPositiveHeight (n04bActualTypedAtlas hT hS hN hfield e)
        src 3 δ (state y) i q)⁻¹
      else n04FixedPositiveHeight (n04bActualTypedAtlas hT hS hN hfield e)
        src 3 δ (state y) i q) :=
    n04Realization_actualFixedPositiveHeight_mixedJetRegularity
      hT hS hN hfield e hU state hstate₀ hsector src δ i JH inv
  refine ⟨RQ, ?_⟩
  intro x hx P v hv W Mjet scale hW hWR hMjet hscale hδM budget shift hinv hraw q
  exact hbound U hU (n04PositiveLeft i) (n04PositiveRight i) (δ i) hδ hδone
    (fun y side => n04PositiveSourceHeight (src i side)
      (n04bActualTypedAtlas hT hS hN hfield e) (state y))
    (fun y hy side θ => (hroot y hy side θ).1)
    (fun y hy side θ => (hroot y hy side θ).2)
    JH x hx P v hv W Mjet scale hW hWR hMjet hscale hδM budget shift hinv hraw
    (Clog i * H i ^ 7) hlow.1 (hlow.2.1 x hx) hlow.2.2 inv q
    (RQ.parameter a b q (mem_univ q))

end ContinuousFlexibility.Analysis
