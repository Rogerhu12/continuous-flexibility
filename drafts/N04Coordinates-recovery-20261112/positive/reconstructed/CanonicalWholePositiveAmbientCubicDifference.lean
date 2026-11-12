import ContinuousFlexibility.Analysis.CanonicalWholePositiveCubicDifference
import ContinuousFlexibility.Analysis.CanonicalWholePositiveAmbientFields
import ContinuousFlexibility.Analysis.WholePositiveFlatPrincipalPatch
import ContinuousFlexibility.Analysis.WholePositiveAmbientBuffer
import ContinuousFlexibility.Analysis.IntervalCubicOpenGermDivision

/-!
# Actual cubic division on every whole positive component

Interior endpoints use the actual negative reference equation and the
constructed matching jets. Ambient endpoints use the same interpolation's
identity collar and the flat zero extension of the actual N01 physical
coefficient difference. A single smooth representative retains the actual
numerator on the open component. Its removable quotient has the fixed
six-radial-derivative estimate, without conditions on totalized ambient
values of the stored physical coefficients.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

/-- The ambient side fields are the local outputs of the actual
interpolation. They are discharged by the construction in the theorem
below; no coefficient vanishing or principal matching is an input. -/
theorem n04Coordinates_wholePositivePrincipal_smooth_flat_representative
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
    (hn : 2 ≤ n) (hlc : n04PositiveLeft i < c) (hcd : c < d)
    (hdr : d < n04PositiveRight i)
    (hambient : ∀ side : Bool,
      n04PositiveEndpoint i side = (if side then D.b else D.a) →
      ∀ p : PolarPoint, (if side then d ≤ p.1 else p.1 ≤ c) →
        τ p = p ∧ σ p = p ∧ Q p = 1) :
    ∃ F : Fin 3 → PolarPoint → ℝ, (∀ v, ContDiff ℝ ∞ (F v)) ∧
      (∀ v p, p ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ) →
        F v =ᶠ[𝓝 p] wholePositivePrincipalDifference (L.coefficients z)
          (L.coefficients (C.referenceState, 0)) τ σ Q v) ∧
      ∀ side : Bool, ∀ v θ k, k ≤ 2 →
        radialBoundaryJet (F v) (n04PositiveEndpoint i side) k θ = 0 := by
  have hD := n04b_profileGeometry_of_through03 hN
  have hcontinuous : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  have hbounds := n04PositiveComponent_bounds hcontinuous i
  have hgeometry := wholePositiveChartGeometry_of_matching hm
  obtain ⟨u, v, hau, huv, hvb, hmap, hinterior, houtside⟩ :=
    exists_wholePositive_ambient_buffer hbounds.1 hlc hcd hdr hbounds.2.2
      hm.geometry.left_inverse.injective hm.geometry.maps_closed hambient
  have href := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hrefS := hN.1.1.2.2.1.stateSector
  have hA := hfield.smooth_coefficients z hz hs
  have hAref := hfield.smooth_coefficients (C.referenceState, 0) href hrefS
  let E := n01OriginalCoefficientDifferenceExtension D S C z
  have hE (w : Fin 3) :=
    n01OriginalCoefficientDifferenceExtension_smooth_flat hT hS hN.1.1 hz hs w
  obtain ⟨F, hF, hcentral, hidentity, hambientF⟩ :=
    exists_wholePositivePrincipal_flat_patch
      (E := E) hau huv hvb hgeometry hmap
      hA.1 hA.2.1 hA.2.2 hAref.1 hAref.2.1 hAref.2.2 (fun w => (hE w).1)
  have hphysical (w : Fin 3) (p : PolarPoint)
      (hp : p ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ)) :
      E w =ᶠ[𝓝 p] (fun q => canonicalCoefficientComponent w (L.coefficients z) q -
        canonicalCoefficientComponent w (L.coefficients (C.referenceState, 0)) q) := by
    have hpann : p ∈ annularOpen D :=
      ⟨n04PositiveComponent_interval_subset hcontinuous i hp.1, mem_univ _⟩
    have hpos := n04PositiveComponent_interval_pos hcontinuous i hp.1
    have hcurrent := n03CoefficientComponent_positive_germ hN.2 hz hs hpann hpos w
    have hreference := n03CoefficientComponent_positive_germ hN.2 href hrefS hpann hpos w
    exact (n01OriginalCoefficientDifferenceExtension_germ D S C z w hpann).trans
      (hcurrent.sub hreference).symm
  refine ⟨F, hF, ?_, ?_⟩
  · intro w p hp
    by_cases hmiddle : p.1 ∈ Icc u v
    · exact hcentral w p ⟨hmiddle, mem_univ _⟩
    · have hid := houtside p hp hmiddle
      exact hidentity w p hid.1 hid.2.1 hid.2.2 (hphysical w p hp)
  · intro side w θ k hk
    by_cases hroot : n04PositiveEndpoint i side = (if side then D.b else D.a)
    · have hid : τ =ᶠ[𝓝 (n04PositiveEndpoint i side, θ)] (id : PolarPoint → PolarPoint) ∧
          σ =ᶠ[𝓝 (n04PositiveEndpoint i side, θ)] (id : PolarPoint → PolarPoint) ∧
          Q =ᶠ[𝓝 (n04PositiveEndpoint i side, θ)] (fun _ => (1 : ℝ)) := by
        cases side
        · exact identityFields_germ_of_halfPlane false c (hambient false hroot)
            (p := (n04PositiveLeft i, θ)) hlc
        · exact identityFields_germ_of_halfPlane true d (hambient true hroot)
            (p := (n04PositiveRight i, θ)) hdr
      have hnot : (n04PositiveEndpoint i side, θ).1 ∉ Ioo D.a D.b := by
        change n04PositiveEndpoint i side ∉ Ioo D.a D.b
        rw [hroot]
        cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_Ioo,
          lt_self_iff_false, false_and, and_false, not_false_eq_true]
      have hg := hambientF w (n04PositiveEndpoint i side, θ) hnot
        hid.1 hid.2.1 hid.2.2
      have hmatch : FiniteFullJetMatch k (n04PositiveEndpoint i side, θ)
          (F w) (fun _ : PolarPoint => (0 : ℝ)) := by
        refine ⟨(hF w).contDiffAt, contDiffAt_const, ?_⟩
        intro t _
        have ht := (hg.iteratedFDeriv ℝ t).eq_of_nhds.trans
          ((hE w).2 t (n04PositiveEndpoint i side, θ) hnot)
        simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using ht
      calc
        radialBoundaryJet (F w) (n04PositiveEndpoint i side) k θ =
            radialBoundaryJet (fun _ : PolarPoint => (0 : ℝ))
              (n04PositiveEndpoint i side) k θ :=
          radialBoundaryJet_eq_of_finiteFullJetMatch hmatch le_rfl
        _ = 0 := by simp only [radialBoundaryJet, iteratedDeriv_fun_const_zero]
    · have hpoint : (n04PositiveEndpoint i side, θ) ∈ Icc u v ×ˢ (univ : Set ℝ) :=
        ⟨hinterior side hroot, mem_univ _⟩
      have hg := (hcentral w (n04PositiveEndpoint i side, θ) hpoint).comp_tendsto
        ((continuous_id.prodMk continuous_const).tendsto (n04PositiveEndpoint i side))
      exact (hg.iteratedDeriv k).eq_of_nhds.trans
        (n04Coordinates_wholePositivePrincipal_difference_endpoint_jets
          hT hS hN hfield e hz hs j hm side hroot θ w k (hk.trans hn))

/-- The displayed interpolation, with its same matching certificate and
same width, has a smooth cubic quotient on every positive component.
The actual numerator is required only on the open physical component. -/
theorem n04Coordinates_wholePositivePrincipal_all_components_cubic_difference
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
    {c d κφ κX M Mσ δ J H : ℝ}
    (hn : 2 ≤ n) (hlc : n04PositiveLeft i < c) (hcd : c < d)
    (hdr : d < n04PositiveRight i)
    (hκφ : 0 < κφ) (hκX : 0 < κX) (hM : 0 ≤ M) (hMσ : 0 ≤ Mσ)
    (hδ : 0 < δ)
    (hδρ : δ ≤ min ((n04PositiveRight i - n04PositiveLeft i) / 4)
      (min (c - n04PositiveLeft i) (n04PositiveRight i - d))) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let l := n04PositiveLeft i
    let r := n04PositiveRight i
    let F := fun side => n04PositiveSourceMap (j side) K z
    let q := fun side => n04PositiveSourceHeight (j side) K z
    let ψ := fun side p => (F side p).2
    let X := fun side p => (F side p).1
    let τ := oneSidedWholeComponentTransport n ψ X l r c d κφ κX M Mσ
    let σ := oneSidedWholeComponentTransportInverse n ψ X l r c d κφ κX M Mσ
    let Q := positiveHeightTaylorInterpolation n l r δ (fun _ => 1) q
    WholePositiveTransportMatching n F q τ σ Q l r c d J H →
    ∃ divided : Fin 3 → PolarPoint → ℝ, (∀ v, ContDiff ℝ ∞ (divided v)) ∧
      (∀ v p, p ∈ Ioo l r ×ˢ (univ : Set ℝ) →
        wholePositivePrincipalDifference (L.coefficients z)
          (L.coefficients (C.referenceState, 0)) τ σ Q v p =
            ((p.1 - l) * (r - p.1)) ^ 3 * divided v p) ∧
      ∀ v (a b : ℕ) (B : ℝ) p, p ∈ Icc l r ×ˢ (univ : Set ℝ) →
        (∀ x ∈ Ioo l r, |mixedDerivative (a + 6) b
          (wholePositivePrincipalDifference (L.coefficients z)
            (L.coefficients (C.referenceState, 0)) τ σ Q v) (x, p.2)| ≤ B) →
        |mixedDerivative a b (divided v) p| ≤ B / 36 := by
  dsimp only
  intro hm
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let l := n04PositiveLeft i
  let r := n04PositiveRight i
  let F := fun side => n04PositiveSourceMap (j side) K z
  let q := fun side => n04PositiveSourceHeight (j side) K z
  let ψ : Bool → PolarPoint → ℝ := fun side p => (F side p).2
  let X : Bool → PolarPoint → ℝ := fun side p => (F side p).1
  let τ := oneSidedWholeComponentTransport n ψ X l r c d κφ κX M Mσ
  let σ := oneSidedWholeComponentTransportInverse n ψ X l r c d κφ κX M Mσ
  let Q := positiveHeightTaylorInterpolation n l r δ (fun _ => 1) q
  have hambient (side : Bool)
      (hroot : n04PositiveEndpoint i side = (if side then D.b else D.a))
      (p : PolarPoint) (hp : if side then d ≤ p.1 else p.1 ≤ c) :
      τ p = p ∧ σ p = p ∧ Q p = 1 := by
    have hfields := (n04PositiveSource_ambient_interpolation_fields
      hN.1.1.2.2.2.1 K z n j hlc hcd hdr hκφ hκX hM hMσ hδ hδρ
      hm side hroot).1 p hp
    exact ⟨hfields.1, hfields.2.1, hfields.2.2.1⟩
  obtain ⟨G, hG, hgerm, hzero⟩ :=
    n04Coordinates_wholePositivePrincipal_smooth_flat_representative
      hT hS hN hfield e hz hs j hm hn hlc hcd hdr hambient
  have hcontinuous : Continuous (deriv D.w) :=
    (n04b_profileGeometry_of_through03 hN).2.2.1.1.continuous_deriv (by simp)
  have hlr := (n04PositiveComponent_bounds hcontinuous i).2.1
  have hout (v : Fin 3) := intervalRadialCubicQuotient_of_open_germs
    (hG v) hlr (hgerm v)
    (by simpa only [n04PositiveEndpoint, Bool.false_eq_true, ↓reduceIte] using hzero false v)
    (by simpa only [n04PositiveEndpoint, ↓reduceIte] using hzero true v)
  refine ⟨fun v => intervalRadialCubicQuotient (G v) l r,
    fun v => (hout v).1, ?_, ?_⟩
  · intro v p hp
    exact (hout v).2.1 p hp
  · intro v a b B p hp hbound
    exact (hout v).2.2 a b B p hp hbound

end ContinuousFlexibility.Analysis
