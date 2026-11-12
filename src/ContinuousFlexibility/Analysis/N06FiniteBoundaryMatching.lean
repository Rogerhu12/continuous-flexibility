import ContinuousFlexibility.Analysis.N06OrientedRootDensity
import ContinuousFlexibility.Analysis.N06AdjacentPieceClassification

/-!
# Actual finite modal matching in the finite-atlas orientation

The original N05 graph determines the physical value and conormal traces
of its actual modes. True common forward first jets transport those traces
to the current charts. Their radial signs are fixed by the original chart
map, and their common angular map covers the whole half-period.

Consequently the oriented rows in the finite Green assembly match at
every angular point. At a turning interface the actual principal density
is used; at a negative cut the two genuine affine trace laws cancel.
The shared and affine first-jet records below are precise geometric
inputs, not conclusions asserted from the bare N04 transmission clause.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {Vol : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K Vol b} {z : AnnularState S × ℝ}
  {φ : PolarPoint → ℝ}

/-- A true common reference/current root germ gives the pointwise
matching required by finite Green gluing. One adjacent positive piece
supplies the nonnegative reference slope at the interface. -/
theorem n06N05_finite_current_root_orientedMatching
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (a : ℕ → ℝ → ℝ)
    (ha : ∀ m, K.positive m = true → Continuous (a m))
    (hea : ∀ m, K.positive m = true → EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun p => a m p.1) (canonicalOpen S K m))
    (heb : ∀ m, K.positive m = true → EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hreg : ∀ m, K.positive m = true →
      ContDiffOn ℝ ∞ (K.coefficients z m).a (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).b (canonicalOpen S K m) ∧
      ContDiffOn ℝ ∞ (K.coefficients z m).c (canonicalOpen S K m))
    (u : B.Space) (ml mr : ℕ) (s : Finset ℕ) (vl vr : ℕ → ℝ → ℝ)
    (reverseL reverseR : Bool)
    (hjoin : K.physicalRight ml = K.physicalLeft mr)
    (hpositive : K.positive ml = true ∨ K.positive mr = true)
    {σl σr : ℝ} {β₀ H₀ ρ₀ κ₀ Hr₀ β H ρ κ Hr : ℝ → ℝ}
    (Jl₀ : N06RootFirstJets (K.chart (C.referenceState, 0) ml)
      (K.height (C.referenceState, 0) ml) (K.physicalRight ml)
      (n06Endpoint (K.left ml) (K.right ml) (if reverseL then !true else true))
        σl β₀ H₀ ρ₀ κ₀ Hr₀)
    (Jr₀ : N06RootFirstJets (K.chart (C.referenceState, 0) mr)
      (K.height (C.referenceState, 0) mr) (K.physicalRight ml)
      (n06Endpoint (K.left mr) (K.right mr) (if reverseR then !false else false))
        σr β₀ H₀ ρ₀ κ₀ Hr₀)
    (hH₀ : H₀ 0 ≠ 0) (hρ₀ : ρ₀ 0 ≠ 0)
    (Jl : N06RootFirstJets (K.chart z ml) (K.height z ml) (K.physicalRight ml)
      (n06Endpoint (K.left ml) (K.right ml) (if reverseL then !true else true))
        σl β H ρ κ Hr)
    (Jr : N06RootFirstJets (K.chart z mr) (K.height z mr) (K.physicalRight ml)
      (n06Endpoint (K.left mr) (K.right mr) (if reverseR then !false else false))
        σr β H ρ κ Hr)
    (Ql : N06CurrentHeightTestTraces S K z ml φ)
    (Qr : N06CurrentHeightTestTraces S K z mr φ)
    (hφ : ContDiff ℝ ∞ φ)
    (hvl : ∀ n ∈ s, ContDiff ℝ 1 (vl n))
    (hvr : ∀ n ∈ s, ContDiff ℝ 1 (vr n))
    (hmodeL : ∀ n ∈ s, n06HalfCosineCoefficient (u.val.1.1 ml) n
      =ᵐ[volume.restrict (Ioo (K.left ml) (K.right ml))] vl n)
    (hmodeR : ∀ n ∈ s, n06HalfCosineCoefficient (u.val.1.1 mr) n
      =ᵐ[volume.restrict (Ioo (K.left mr) (K.right mr))] vr n)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    n06OrientedCanonicalBoundary Ql (r11bFiniteSynthesis s vl referenceAngularBasis)
        (fun y => if K.positive ml = true then a ml y else 1) reverseL true θ =
      n06OrientedCanonicalBoundary Qr (r11bFiniteSynthesis s vr referenceAngularBasis)
        (fun y => if K.positive mr = true then a mr y else 1) reverseR false θ := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h03 : N03Properties D T S C R L base ε := h.1.1.2
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2
  have hrl : K.physicalRight ml ∈ Icc (K.physicalLeft ml) (K.physicalRight ml) :=
    ⟨(h04.2.2.2.1 ml).1.le, le_rfl⟩
  have hrr : K.physicalRight ml ∈ Icc (K.physicalLeft mr) (K.physicalRight mr) := by
    rw [hjoin]
    exact ⟨le_rfl, (h04.2.2.2.1 mr).1.le⟩
  have hp : K.physicalRight ml ∈ radialCore D :=
    n06_adjacentInterface_mem_core h04 hjoin
  have hpos : 0 ≤ deriv D.w (K.physicalRight ml) := by
    rcases hpositive with hl | hr
    · exact n06_positivePiece_closed_slope_nonneg h01 h04 ml hl hrl
    · exact n06_positivePiece_closed_slope_nonneg h01 h04 mr hr hrr
  obtain ⟨η, hη, hβη⟩ :=
    (n06_current_boundary_angular_surjOn Jl h04 hz hs hrl).2.2 hθ
  have he := n06N05_finite_current_root_boundaryDensity hS h hcoordinates hz hs
    u ml mr s vl vr hjoin hp Jl₀ Jr₀ hH₀ hρ₀ Jl Jr Ql Qr hφ
    hvl hvr hmodeL hmodeR (L.coefficients z) hη
  have hrowL := n06_nonnegative_boundaryDensity hT hS h01 h03 h04 hz hs a ha hea heb hreg
    (if reverseL then !true else true) Jl hrl hp hpos η
      Ql.value Ql.radial Ql.angular (r11bFiniteSynthesis s vl referenceAngularBasis)
  have hrowR := n06_nonnegative_boundaryDensity hT hS h01 h03 h04 hz hs a ha hea heb hreg
    (if reverseR then !false else false) Jr hrr hp hpos η
      Qr.value Qr.radial Qr.angular (r11bFiniteSynthesis s vr referenceAngularBasis)
  have hsignL := n06_current_boundary_radialSign_eq_reverse reverseL true Jl h04 hz hs η
  have Jr' : N06RootFirstJets (K.chart z mr) (K.height z mr) (K.physicalLeft mr)
      (n06Endpoint (K.left mr) (K.right mr) (if reverseR then !false else false))
        σr β H ρ κ Hr := by
    rw [← hjoin]
    exact Jr
  have hsignR := n06_current_boundary_radialSign_eq_reverse reverseR false Jr' h04 hz hs η
  rw [hrowL, hrowR, hsignL, hsignR, hβη] at he
  simpa only [n06OrientedCanonicalBoundary, mul_assoc] using he

/-- The true affine cut jets imply the same pointwise oriented matching
on all of the angular half-period. The fixed affine parameter occurs in
both actual reference and current forward jets, and cancels algebraically. -/
theorem n06N05_finite_current_cut_orientedMatching
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : B.Space) (ml mr : ℕ) (s : Finset ℕ) (vl vr : ℕ → ℝ → ℝ)
    (hjoin : K.physicalRight ml = K.physicalLeft mr)
    {y σ τ : ℝ} (hyl : y = K.right ml) (hyr : y = K.right mr)
    {β₀ H₀ ρ₀ κ₀ Hr₀ β H ρ κ Hr : ℝ → ℝ}
    (Jl₀ : N06RootFirstJets (K.chart (C.referenceState, 0) ml)
      (K.height (C.referenceState, 0) ml) (K.physicalRight ml) y σ β₀ H₀ ρ₀ κ₀ Hr₀)
    (Jr₀ : N06RootFirstJets (K.chart (C.referenceState, 0) mr)
      (K.height (C.referenceState, 0) mr) (K.physicalRight ml) y (-σ) β₀ H₀ ρ₀ κ₀
        (fun θ => Hr₀ θ - H₀ θ * (σ * ρ₀ θ) * τ))
    (Jl : N06RootFirstJets (K.chart z ml) (K.height z ml)
      (K.physicalRight ml) y σ β H ρ κ Hr)
    (Jr : N06RootFirstJets (K.chart z mr) (K.height z mr)
      (K.physicalRight ml) y (-σ) β H ρ κ
        (fun θ => Hr θ - H θ * (σ * ρ θ) * τ))
    (Ql : N06CurrentHeightTestTraces S K z ml φ)
    (Qr : N06CurrentHeightTestTraces S K z mr φ)
    (hφ : ContDiff ℝ ∞ φ)
    (hvl : ∀ n ∈ s, ContDiff ℝ 1 (vl n))
    (hvr : ∀ n ∈ s, ContDiff ℝ 1 (vr n))
    (hmodeL : ∀ n ∈ s, n06HalfCosineCoefficient (u.val.1.1 ml) n
      =ᵐ[volume.restrict (Ioo (K.left ml) (K.right ml))] vl n)
    (hmodeR : ∀ n ∈ s, n06HalfCosineCoefficient (u.val.1.1 mr) n
      =ᵐ[volume.restrict (Ioo (K.left mr) (K.right mr))] vr n)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    n06OrientedCanonicalBoundary Ql (r11bFiniteSynthesis s vl referenceAngularBasis)
        (fun _ => 1) false true θ =
      n06OrientedCanonicalBoundary Qr (r11bFiniteSynthesis s vr referenceAngularBasis)
        (fun _ => 1) true false θ := by
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2
  have hroot : K.physicalRight ml ∈ radialCore D :=
    n06_adjacentInterface_mem_core h04 hjoin
  have hrl : K.physicalRight ml ∈ Icc (K.physicalLeft ml) (K.physicalRight ml) :=
    ⟨(h04.2.2.2.1 ml).1.le, le_rfl⟩
  obtain ⟨η, hη, hβη⟩ :=
    (n06_current_boundary_angular_surjOn Jl h04 hz hs hrl).2.2 hθ
  have he := n06N05_finite_current_cut_wronskians_cancel hS h hcoordinates hz hs
    u ml mr s vl vr hjoin hroot Jl₀ Jr₀ Jl Jr Ql Qr hφ hvl hvr hmodeL hmodeR hη
  rw [hβη] at he
  simp only [n06OrientedCanonicalBoundary, n06Endpoint, Bool.false_eq_true, if_false, if_true,
    Bool.not_false, Bool.not_true, one_mul, neg_one_mul, neg_mul, ← hyl, ← hyr]
  linarith only [he]

end ContinuousFlexibility.Analysis
