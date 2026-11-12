import ContinuousFlexibility.Analysis.WholePositiveCanonicalFields
import ContinuousFlexibility.Analysis.CanonicalWholePositiveRootMatching
import ContinuousFlexibility.Analysis.CanonicalWholeNegativeBoundary
import ContinuousFlexibility.Analysis.AdjugateInversePrincipalField
import ContinuousFlexibility.Analysis.AdjugatePrincipalFiniteJets
import ContinuousFlexibility.Analysis.FiniteFullJetBoundary

/-!
# Actual positive principal jets at a negative neighbor

The genuine inverse-chart field equals its forward adjugate formula.
The existing coordinate and height matching therefore transfers full
principal jets from the actual neighboring negative transport. No
coefficient matching or vanishing remainder is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem wholePositiveCanonicalCoefficients_eq_reverse
    (A : SymmetricCoefficients) (τ σ : PolarPoint → PolarPoint)
    (Q : PolarPoint → ℝ) :
    wholePositiveCanonicalCoefficients A τ σ Q =
      reverseCoordinatePrincipalCoefficients A τ σ Q := by
  simp only [wholePositiveCanonicalCoefficients, reverseCoordinatePrincipalCoefficients,
    wholePositiveChartHeight, one_div]

theorem wholePositiveCanonicalCoefficient_component_eq_adjugate
    (A : SymmetricCoefficients) {τ σ : PolarPoint → PolarPoint}
    {Q : PolarPoint → ℝ} {l r c d : ℝ}
    (H : WholePositiveChartGeometry σ τ (wholePositiveChartHeight σ Q) l r c d)
    (i : Fin 3) :
    canonicalCoefficientComponent i (wholePositiveCanonicalCoefficients A τ σ Q) =
      canonicalCoefficientComponent i (adjugateCoordinatePrincipalCoefficients A τ Q) := by
  funext p
  have hQ : 0 < (Q p)⁻¹ := by
    simpa only [wholePositiveChartHeight, H.right_inverse p] using
      H.height_positive (τ p)
  have hi : σ ∘ τ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) :=
    Filter.Eventually.of_forall H.right_inverse
  have he := reverseCoordinatePrincipalCoefficients_eq_adjugate A
    (F := τ) (G := σ) (h := Q) (x := p)
    (H.inverse_smooth.differentiable (by simp) p)
    (H.chart_smooth.differentiable (by simp) (τ p)) hi (inv_pos.mp hQ).ne'
  rw [wholePositiveCanonicalCoefficients_eq_reverse]
  simp only [canonicalCoefficientComponent, ite_apply]
  split_ifs
  · exact he.1
  · exact he.2.1
  · exact he.2.2

/-- This consumes the already constructed coordinate and height jets;
the output concerns the actual inverse-chart coefficient function. -/
theorem finiteFullJetMatch_wholePositiveCanonicalCoefficient
    {A : SymmetricCoefficients} {T τ σ : PolarPoint → PolarPoint}
    {q Q : PolarPoint → ℝ} {p : PolarPoint} {n : ℕ} {l r c d : ℝ}
    (H : WholePositiveChartGeometry σ τ (wholePositiveChartHeight σ Q) l r c d)
    (hTτ : FiniteFullJetMatch (n + 1) p T τ)
    (hqQ : FiniteFullJetMatch n p q Q)
    (ha : ContDiffAt ℝ ∞ A.a (T p)) (hb : ContDiffAt ℝ ∞ A.b (T p))
    (hc : ContDiffAt ℝ ∞ A.c (T p))
    (hq : q p ≠ 0) (hJ : planeJacobian T p ≠ 0) (i : Fin 3) :
    FiniteFullJetMatch n p
      (canonicalCoefficientComponent i (adjugateCoordinatePrincipalCoefficients A T q))
      (canonicalCoefficientComponent i (wholePositiveCanonicalCoefficients A τ σ Q)) := by
  rw [wholePositiveCanonicalCoefficient_component_eq_adjugate A H i]
  exact finiteFullJetMatch_adjugatePrincipal hTτ hqQ ha hb hc hq hJ i

/-- The true negative index and the coefficient evaluation point come
from the actual atlas and its closed-component range. -/
theorem n04Coordinates_wholePositivePrincipal_negative_root_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss n : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    {i : N04PositiveComponent D.a D.b (deriv D.w)}
    (j : ∀ side, N04PositiveEndpointSource C i side)
    {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ} {c d J H : ℝ}
    (hm : WholePositiveTransportMatching n
      (fun side => n04PositiveSourceMap (j side) (n04bActualTypedAtlas hT hS hN hfield e) z)
      (fun side => n04PositiveSourceHeight (j side) (n04bActualTypedAtlas hT hS hN hfield e) z)
      τ σ Q (n04PositiveLeft i) (n04PositiveRight i) c d J H)
    (m : ℕ) (side : Bool)
    (hadj : n04PositiveEndpoint i (!side) = (if side then C.right m else C.left m))
    (θ : ℝ) (v : Fin 3) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    FiniteFullJetMatch n (if side then C.right m else C.left m, θ)
      (canonicalCoefficientComponent v (adjugateCoordinatePrincipalCoefficients
        (L.coefficients z) (canonicalWholeNegativeTransport C K z m)
        (canonicalWholeNegativeHeightRatio C K z m)))
      (canonicalCoefficientComponent v (wholePositiveCanonicalCoefficients
        (L.coefficients z) τ σ Q)) := by
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let p : PolarPoint := (if side then C.right m else C.left m, θ)
  have hends := hN.1.1.2.2.2.1.1 m
  have hp : p ∈ Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := by
    refine ⟨?_, mem_univ _⟩
    cases side
    · exact ⟨le_rfl, hends.2.1.le⟩
    · exact ⟨hends.2.1.le, le_rfl⟩
  have hreg := canonicalWholeNegativeTransport_closed_regular
    hT hS hN hfield e hz hs m (p := p) hp
  have hj := wholePositiveTransportMatching_negative_root_jets hN.1.1 j hm
  have hTτ : FiniteFullJetMatch (n + 1) p
      (canonicalWholeNegativeTransport C K z m) τ :=
    ⟨hreg.1, hm.geometry.smooth.contDiffAt,
      fun k hk => (hj m side hadj).1 θ k hk⟩
  have hqQ : FiniteFullJetMatch n p
      (canonicalWholeNegativeHeightRatio C K z m) Q :=
    ⟨hreg.2.1, hm.height_smooth.contDiffAt,
      fun k hk => (hj m side hadj).2 θ k hk⟩
  have hJ : planeJacobian (canonicalWholeNegativeTransport C K z m) p ≠ 0 := by
    have hpos : 0 < planeJacobian (canonicalWholeNegativeTransport C K z m) p := by
      simpa only [planeJacobian, hTτ.fderiv.value] using hm.geometry.jacobian_positive p
    exact hpos.ne'
  have himage := canonicalWholeNegativeTransport_mapsTo_closed
    hT hS hN hfield e hz hs m (x := p) hp
  have hcore : canonicalWholeNegativeTransport C K z m p ∈ annularOpen D :=
    ⟨⟨hends.1.trans_le himage.1.1, himage.1.2.trans_lt hends.2.2⟩, mem_univ _⟩
  have hnhds : annularOpen D ∈ 𝓝 (canonicalWholeNegativeTransport C K z m p) :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds hcore
  have hA := hfield.smooth_coefficients z hz hs
  exact finiteFullJetMatch_wholePositiveCanonicalCoefficient
    (wholePositiveChartGeometry_of_matching hm) hTτ hqQ
    (hA.1.contDiffAt hnhds) (hA.2.1.contDiffAt hnhds) (hA.2.2.contDiffAt hnhds)
    hreg.2.2.ne' hJ v

theorem radialBoundaryJet_sub_eq_zero_of_finiteFullJetMatch
    {f g : PolarPoint → ℝ} {c θ : ℝ} {n k : ℕ}
    (h : FiniteFullJetMatch n (c, θ) f g) (hk : k ≤ n) :
    radialBoundaryJet (fun p => f p - g p) c k θ = 0 := by
  have hl : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) c :=
    contDiffAt_id.prodMk contDiffAt_const
  have hf : ContDiffAt ℝ ∞ (fun r : ℝ => f (r, θ)) c :=
    h.left_smooth.comp c hl
  have hg : ContDiffAt ℝ ∞ (fun r : ℝ => g (r, θ)) c :=
    h.right_smooth.comp c hl
  change iteratedDeriv k (fun r : ℝ => f (r, θ) - g (r, θ)) c = 0
  rw [iteratedDeriv_fun_sub
    (hf.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))
    (hg.of_le (show (k : ℕ∞ω) ≤ ∞ by simp))]
  exact sub_eq_zero.mpr (radialBoundaryJet_eq_of_finiteFullJetMatch h hk)

end ContinuousFlexibility.Analysis
