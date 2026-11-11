import ContinuousFlexibility.Analysis.N06PhysicalPairingLimits
import ContinuousFlexibility.Analysis.N06CurrentPhysicalTests
import ContinuousFlexibility.Analysis.N06ControlledPieceFiniteness
import ContinuousFlexibility.Analysis.N06NamedPhysicalRelation

/-!
# From actual finite approximants to the named physical weak equation

Approximants may lie outside the original N05 graph. Their actual global
weak equations, piecewise L2 limits, and three scalar limits imply the
equation of the original named graph/source representatives. The test
transforms and finite support set are derived from the current geometry.
This is the limit step after finite endpoint terms have cancelled; it
neither assumes nor asserts convergence of full boundary traces.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology

/-- Actual weak equations pass from canonical approximants to the original
named graph and source, without putting the approximants in that graph. -/
theorem n06_namedPhysicalWeakRelation_of_piecewise_limit
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {base loss b : ℕ} {ε : ℝ}
    {B : CanonicalDomainData S K V b} {z : AnnularState S × ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hThrough : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : B.Space) (f : V.level (3 / 4 : ℝ) 0 b)
    (U : ℕ → CanonicalUnknown S K) (F : ℕ → CanonicalSequence S K)
    (hU : ∀ m, Tendsto (fun n => (U n).1 m) atTop (𝓝 (u.val.1.1 m)))
    (hleft : Tendsto (fun n => (U n).2.1) atTop (𝓝 u.val.1.2.1))
    (hmu : Tendsto (fun n => (U n).2.2.1) atTop (𝓝 u.val.1.2.2.1))
    (homega : Tendsto (fun n => (U n).2.2.2) atTop (𝓝 u.val.1.2.2.2))
    (hF : ∀ m, Tendsto (fun n => F n m) atTop
      (𝓝 (V.forget (3 / 4 : ℝ) 0 b f m)))
    (hweak : ∀ n φ, RadialTest D φ →
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06PhysicalHeight K z (fun m => ((U n).1 m : PolarPoint → ℝ))
          (U n).2.1 (r, θ) * divergenceOperator (L.coefficients z) φ (r, θ))) +
        (U n).2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
          nuColumnField D S C z (r, θ) * φ (r, θ))) +
        (U n).2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
          (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) * φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06PhysicalSource K z (fun m => (F n m : PolarPoint → ℝ)) (r, θ) *
          φ (r, θ))) :
    N06NamedPhysicalWeakRelation D C L B z u f := by
  intro φ hφ
  have h01 : N01Properties D T S C base loss ε := hThrough.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := hThrough.2.2.2.2
  have hab : D.a ≤ D.b := by
    obtain ⟨x, hxL, hxR⟩ := exists_between (h04.2.2.2.1 0).1
    have hx := (h04.2.2.2.1 0).2.2 ⟨hxL, hxR⟩
    exact (hx.1.trans hx.2).le
  obtain ⟨J, hJ, hJD, hφsupport, hLsupport, htests⟩ :=
    n06_current_physical_tests hT hS hThrough hz hs hφ
  have hfinite : {m : ℕ |
      (Ioo (K.physicalLeft m) (K.physicalRight m) ∩ J).Nonempty}.Finite :=
    n06_controlledReferencePieces_finite_on_compact h01.1.1 hcoordinates hJ hJD
  have hheight := n06_tendsto_physicalHeight_pairing hS h04 hz hs
    hU hleft hfinite (g := divergenceOperator (L.coefficients z) φ)
    (fun m => (htests m).1) (fun m => (htests m).2.1) hLsupport
  have hsource := n06_tendsto_physicalSource_pairing hab h04 hz hs
    hF hfinite (φ := φ)
    (fun m => (htests m).2.2.1) (fun m => (htests m).2.2.2) hφsupport
  have hnu := hmu.mul_const (∫ r in D.a..D.b,
    radialAngularMean (fun θ => nuColumnField D S C z (r, θ) * φ (r, θ)))
  have hpsi := homega.mul_const (∫ r in D.a..D.b,
    radialAngularMean (fun θ => (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) * φ (r, θ)))
  exact tendsto_nhds_unique_of_eventuallyEq ((hheight.add hnu).add hpsi) hsource
    (Filter.Eventually.of_forall (fun n => hweak n φ hφ))

end ContinuousFlexibility.Statements
