import ContinuousFlexibility.Analysis.N06FiniteBoundaryMatching
import ContinuousFlexibility.Analysis.N05N06ClosedChartBridge

/-!
# Genuine atlas jets give every finite modal matching condition

The geometric input records only values and first derivatives of the
actual forward charts and heights. It contains no reconstructed-field
matching condition. At ordinary interfaces the reference and current
charts share their boundary jets. The artificial moving cuts require no
first-jet record: their affine laws follow directly from N04 and the same
original graph through the genuine closed inverse.

The original N05 graph then forces matching for its actual finite modes.
The original N01/N04 geometry classifies every adjacent pair, and the
endpoint values themselves determine the two negative-cut orientations.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The precise forward first jets needed of a chosen reference/current
atlas at true root circles. These are geometric realization requirements; no modal value,
conormal, weak equation, or Green matching is a field of this structure. -/
structure N06AtlasTransmissionJets
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (reverse : ℕ → Bool) : Prop where
  endpoints : ∀ m, ∀ side : Bool, ¬n06ArtificialCutSide K m side →
    ∃ σ : ℝ, ∃ β H ρ κ Hr : ℝ → ℝ,
    Nonempty (N06RootFirstJets (K.chart z m) (K.height z m)
      (n06Endpoint (K.physicalLeft m) (K.physicalRight m) side)
      (n06Endpoint (K.left m) (K.right m) (if reverse m then !side else side))
        σ β H ρ κ Hr)
  roots : ∀ ml mr, K.physicalRight ml = K.physicalLeft mr →
    (K.positive ml = true ∨ K.positive mr = true) →
    ∃ σl σr : ℝ, ∃ β₀ H₀ ρ₀ κ₀ Hr₀ β H ρ κ Hr : ℝ → ℝ,
      N06RootFirstJets (K.chart (C.referenceState, 0) ml)
        (K.height (C.referenceState, 0) ml) (K.physicalRight ml)
        (n06Endpoint (K.left ml) (K.right ml) (if reverse ml then !true else true))
          σl β₀ H₀ ρ₀ κ₀ Hr₀ ∧
      N06RootFirstJets (K.chart (C.referenceState, 0) mr)
        (K.height (C.referenceState, 0) mr) (K.physicalRight ml)
        (n06Endpoint (K.left mr) (K.right mr) (if reverse mr then !false else false))
          σr β₀ H₀ ρ₀ κ₀ Hr₀ ∧
      N06RootFirstJets (K.chart z ml) (K.height z ml) (K.physicalRight ml)
        (n06Endpoint (K.left ml) (K.right ml) (if reverse ml then !true else true))
          σl β H ρ κ Hr ∧
      N06RootFirstJets (K.chart z mr) (K.height z mr) (K.physicalRight ml)
        (n06Endpoint (K.left mr) (K.right mr) (if reverse mr then !false else false))
          σr β H ρ κ Hr
variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {Vol : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K Vol b} {z : AnnularState S × ℝ}

/-- Every true endpoint circle has its actual physical radius under
the genuine closed inverse. The original geometry supplies membership;
the actual forward angular map supplies the whole half-period. -/
theorem N06AtlasTransmissionJets.endpointInverseRadius
    {reverse : ℕ → Bool} (J : N06AtlasTransmissionJets S C K z reverse)
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (side : Bool) (htrue : ¬n06ArtificialCutSide K m side)
    (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    (K.inverseChart z m
      ((if (if reverse m then !side else side) then K.right m else K.left m), θ)).1 =
        if side then K.physicalRight m else K.physicalLeft m := by
  obtain ⟨σ, β, H, ρ, κ, Hr, ⟨Je⟩⟩ := J.endpoints m side htrue
  have hx := (n06_trueEndpoint_current_geometry hC h04 hz hs m side htrue).1
  obtain ⟨η, hη, hβη⟩ :=
    (n06_current_boundary_angular_surjOn Je h04 hz hs hx).2.2 hθ
  have he := (h04.1.boundary z hz hs m).2.2.1 _ (hx η)
  rw [Je.chart_value η, hβη] at he
  exact congrArg Prod.fst he

/-- The true root endpoint, rather than a fictitious fixed middle cut,
determines the reversal flags of both negative halves. -/
theorem N06AtlasTransmissionJets.negative_reverse
    {reverse : ℕ → Bool} (J : N06AtlasTransmissionJets S C K z reverse)
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (n : ℕ) :
    reverse (K.cutPair n).1 = false ∧ reverse (K.cutPair n).2 = true := by
  have hne : (K.cutPair n).1 ≠ (K.cutPair n).2 := by
    intro he
    have hj := (h04.2.1.1.1 n).2.2.2.2.1
    rw [← he] at hj
    exact (h04.1.referenceBounds (K.cutPair n).1).1.ne' hj
  have htrueL : ¬n06ArtificialCutSide K (K.cutPair n).1 false := by
    rintro ⟨k, hk⟩
    have he : n = k := n06_cutHalf_component_eq hC h04 (Or.inl rfl) (Or.inr hk)
    rw [← he] at hk
    exact hne hk
  have htrueR : ¬n06ArtificialCutSide K (K.cutPair n).2 true := by
    rintro ⟨k, hk⟩
    have he : n = k := n06_cutHalf_component_eq hC h04 (Or.inr rfl) (Or.inl hk)
    rw [← he] at hk
    exact hne hk.symm
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
  have hleft := J.endpointInverseRadius hC h04 hz hs (K.cutPair n).1 false htrueL 0 hzero
  have hright := J.endpointInverseRadius hC h04 hz hs (K.cutPair n).2 true htrueR 0 hzero
  have hcut := h04.2.1.1.2 z hz hs n
  have hx := hcut.2.1 ⟨(0 : ℝ), rfl⟩
  obtain ⟨_, _, hl, hr, _, _, _, _, hRl, hRr⟩ := h04.2.1.1.1 n
  constructor
  · cases he : reverse (K.cutPair n).1
    · rfl
    · simp only [he, Bool.not_false, if_true, Bool.false_eq_true, if_false, hRl, hl] at hleft
      exact False.elim (hx.1.1.ne' hleft)
  · cases he : reverse (K.cutPair n).2
    · simp only [he, Bool.false_eq_true, if_false, if_true, hRr, hr] at hright
      rw [hcut.1 0] at hright
      exact False.elim (hx.1.2.ne hright)
    · rfl

/-- The original graph and genuine atlas first jets imply every actual
oriented matching relation. The classification and negative-cut reversal
flags are conclusions, rather than further atlas hypotheses. -/
theorem n06N05_finite_atlas_orientedMatching
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
    (reverse : ℕ → Bool) (J : N06AtlasTransmissionJets S C K z reverse)
    (u : B.Space) (s : Finset ℕ) (v : ℕ → ℕ → ℝ → ℝ)
    (hv : ∀ m, ∀ n ∈ s, ContDiff ℝ 1 (v m n))
    (hmode : ∀ m, ∀ n ∈ s, n06HalfCosineCoefficient (u.val.1.1 m) n
      =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v m n)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (Q : ∀ m, N06CurrentHeightTestTraces S K z m φ)
    (ml mr : ℕ) (hjoin : K.physicalRight ml = K.physicalLeft mr)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    n06OrientedCanonicalBoundary (Q ml) (r11bFiniteSynthesis s (v ml) referenceAngularBasis)
        (fun y => if K.positive ml = true then a ml y else 1) (reverse ml) true θ =
      n06OrientedCanonicalBoundary (Q mr) (r11bFiniteSynthesis s (v mr) referenceAngularBasis)
        (fun y => if K.positive mr = true then a mr y else 1) (reverse mr) false θ := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  rcases n06_adjacentPiece_positive_or_cutPair h01 h04 hjoin with hpositive | hcut
  · obtain ⟨σl, σr, β₀, H₀, ρ₀, κ₀, Hr₀, β, H, ρ, κ, Hr, Jl₀, Jr₀, Jl, Jr⟩ :=
      J.roots ml mr hjoin hpositive
    have href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
      n05_referenceState_mem h01.2.1
    have hsref : stateSector S C.referenceState := n05_referenceState_sector h01.2.2.1
    have hr : K.physicalRight ml ∈ Icc (K.physicalLeft ml) (K.physicalRight ml) :=
      ⟨(h04.1.referenceBounds ml).1.le, le_rfl⟩
    have hb := n05_reference_boundary_regular h04.1 href hsref ml
      (p := (K.physicalRight ml, 0)) hr
    have hH₀ : H₀ 0 ≠ 0 := by
      rw [← Jl₀.height_value 0]
      exact hb.2.2.2.ne'
    have hρ₀ : ρ₀ 0 ≠ 0 := by
      have hJ := hb.2.2.1
      rw [Jl₀.jacobian 0] at hJ
      exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hJ).1).2
    exact n06N05_finite_current_root_orientedMatching hT hS h hcoordinates hz hs
      a ha hea heb hreg u ml mr s (v ml) (v mr) (reverse ml) (reverse mr) hjoin
      hpositive Jl₀ Jr₀ hH₀ hρ₀ Jl Jr (Q ml) (Q mr) hφ
      (hv ml) (hv mr) (hmode ml) (hmode mr) hθ
  · obtain ⟨n, rfl, rfl⟩ := hcut
    have hcuts := h04.2.1.1.1 n
    have hreverse := J.negative_reverse h01.2.2.2.1 h04 hz hs n
    have he := n06N05_finite_current_cut_orientedMatching hS h hcoordinates hz hs
      u n s (v (K.cutPair n).1) (v (K.cutPair n).2)
      (Q (K.cutPair n).1) (Q (K.cutPair n).2) hφ
      (hv _) (hv _) (hmode _) (hmode _) hθ
    simpa only [hcuts.1, hcuts.2.1, Bool.false_eq_true, if_false,
      hreverse.1, hreverse.2] using he

end ContinuousFlexibility.Statements
