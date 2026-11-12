import ContinuousFlexibility.Analysis.N06FiniteCorePieceGreen
import ContinuousFlexibility.Analysis.N06AtlasTransmissionJets
import ContinuousFlexibility.Analysis.N06CurrentFiniteGreenRelation

/-!
# Actual finite-core Green data from the original graph

The original N05 graph supplies a common finite set of actual H2 modal
representatives and both signed local Green formulas. Genuine forward
atlas first jets then give every endpoint matching condition. The current
test traces are constructed from the original N04 forward chart itself.

Thus the existing finite Green data are obtained without taking modes,
weak modal equations, Green formulas, or modal transmission as inputs.
The remaining geometric inputs are the explicit radial reference bounds
and actual forward atlas first jets required of the chosen construction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The actual finite angular core of the same original graph yields all
local data needed by the full physical weak assembly. The source is the
literal relative source, characterized by its genuine compact-test cubic
pairing; no global physical equation is assumed. -/
theorem n06N05_finiteCore_greenData
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {Vol : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
    {B : CanonicalDomainData S K Vol b} {z : AnnularState S × ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (a c pot q : ℕ → ℝ → ℝ) (κ : ℕ → ℝ) (Cref : ℝ)
    (hgeometry : N06PositiveUnitGeometry T K a c pot q κ Cref)
    (hea : ∀ m, K.positive m = true → EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun p => a m p.1) (canonicalOpen S K m))
    (heb : ∀ m, K.positive m = true → EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hec : ∀ m, K.positive m = true → EqOn (K.coefficients (C.referenceState, 0) m).c
      (fun p => c m p.1) (canonicalOpen S K m))
    (hepot : ∀ m, K.positive m = true → EqOn (K.potential (C.referenceState, 0) m)
      (fun p => pot m p.1) (canonicalOpen S K m))
    (hcd : ∀ m, K.positive m = true → ∀ y ∈ Ioo (K.left m) (K.right m),
      DifferentiableAt ℝ (c m) y)
    (hreg : ∀ m, K.positive m = true →
      ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    {scale : ℕ → ℝ} {δ : ℝ}
    (hcoeff : N06PositiveCubicControl K b scale δ
      (fun n => (K.dividedDifference z n).a) (fun n => (K.dividedDifference z n).b)
      (fun n => (K.dividedDifference z n).c))
    (reverse : ℕ → Bool) (J : N06AtlasTransmissionJets S C K z reverse)
    (u : B.Space) (hu : u ∈ n06CanonicalGraphFiniteAngularCore B)
    (G Fcur : CanonicalSequence S K)
    (hsource : ∀ m, (Fcur m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06CurrentRelativeSourceField D S C L K z u.val.1
        (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) G m)
    (hweak : ∀ m ψ, CanonicalTest S K m ψ →
      (∫ p, G m p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, u.val.1.1 m p * n06PositiveCubicTestOperator K
          (fun n => (K.dividedDifference z n).a) (fun n => (K.dividedDifference z n).b)
          (fun n => (K.dividedDifference z n).c) m ψ p ∂canonicalMeasure S K m) :
    ∀ φ, RadialTest D φ →
      Nonempty (N06CurrentFiniteGreenData D S C L K z u.val.1 Fcur φ) := by
  classical
  obtain ⟨s, v, hv, hmode, hvalue, hregular, hgreen⟩ :=
    n06N05_finiteCore_pieceGreen hT hS h hcoordinates hz hs a c pot q κ Cref
      hgeometry hea heb hec hepot hcd hcoeff u hu G Fcur hsource hweak
  intro φ hφ
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2
  have havg : ContDiff ℝ ∞ (n06_radialTestAverage φ) :=
    (n06_radialTestAverage_test hφ).1
  let Q (m : ℕ) : N06CurrentHeightTestTraces S K z m (n06_radialTestAverage φ) :=
    Classical.choice (n06_currentHeightTest_exists_traces h04 hz hs m havg)
  refine ⟨{
    test := Q
    value := fun m => r11bFiniteSynthesis s (v m) referenceAngularBasis
    radialCoefficient := fun m y => if K.positive m = true then a m y else 1
    reverse := reverse
    regular := hregular
    represents := hvalue
    endpointJets := J.endpoints
    green := hgreen φ hφ Q
    matching := ?_
  }⟩
  intro ml mr hjoin θ hθ
  exact n06N05_finite_atlas_orientedMatching hT hS h hcoordinates hz hs a
    (fun m hm => (hgeometry.a_smooth m hm).continuous) hea heb hreg reverse J u s v
    (fun m n _ => hv m n) (fun m n _ => hmode m n) havg Q ml mr hjoin hθ

end ContinuousFlexibility.Statements
