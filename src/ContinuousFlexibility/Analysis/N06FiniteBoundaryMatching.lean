import ContinuousFlexibility.Analysis.N06OrientedRootDensity
import ContinuousFlexibility.Analysis.N06AdjacentPieceClassification
import ContinuousFlexibility.Analysis.N06CutBoundaryCancellation

/-!
# Actual finite modal matching in the finite-atlas orientation

The original N05 graph determines the physical value and conormal traces
of its actual modes. True common forward first jets transport those traces
to the current charts. Their radial signs are fixed by the original chart
map, and their common angular map covers the whole half-period.

Consequently the oriented rows in the finite Green assembly match at
every angular point. At a turning interface the actual principal density
is used; at a negative cut the two genuine affine trace laws cancel.
Only true root interfaces retain shared forward first-jet records. The
artificial cut relation now follows from the genuine closed inverse and
the original N04 transmission clause; it needs no cut geometry record.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- Both true root circles are genuine closed physical boundary points,
and their actual forward canonical radial coordinate is zero. -/
theorem n06_current_cutRoot_geometry
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (n : ℕ) :
    (∀ θ, (C.left n, θ) ∈ physicalPieceClosed S K z (K.cutPair n).1 ∧
      (K.chart z (K.cutPair n).1 (C.left n, θ)).1 = 0) ∧
    (∀ θ, (C.right n, θ) ∈ physicalPieceClosed S K z (K.cutPair n).2 ∧
      (K.chart z (K.cutPair n).2 (C.right n, θ)).1 = 0) := by
  obtain ⟨_, _, _, _, _, hR, hl, hr, hRl, hRr⟩ := h04.2.1.1.1 n
  have hcut := h04.2.1.1.2 z hz hs n
  have hroot (m : ℕ) (r : ℝ) (hleft : K.left m = 0) (hright : K.right m = K.cutRadius n)
      (himage : K.inverseChart z m '' ({0} ×ˢ (univ : Set ℝ)) =
        {r} ×ˢ (univ : Set ℝ)) (θ : ℝ) :
      (r, θ) ∈ physicalPieceClosed S K z m ∧ (K.chart z m (r, θ)).1 = 0 := by
    have hx : (r, θ) ∈ K.inverseChart z m '' ({0} ×ˢ (univ : Set ℝ)) := by
      rw [himage]
      exact ⟨rfl, mem_univ _⟩
    obtain ⟨p, hp, hpx⟩ := hx
    have hp0 : p.1 = 0 := hp.1
    have hpC : p ∈ canonicalClosed S K m := by
      refine ⟨?_, mem_univ _⟩
      rw [hleft, hright, hp0]
      exact ⟨le_rfl, hR.le⟩
    have hb := h04.1.boundary z hz hs m
    refine ⟨?_, ?_⟩
    · rw [← hpx]
      exact hb.2.1 hpC
    · rw [← hpx, hb.2.2.2.1 p hpC]
      exact hp0
  exact ⟨hroot _ _ hl hRl hcut.2.2.2.2.1,
    hroot _ _ hr hRr hcut.2.2.2.2.2⟩

/-- A non-artificial reference side is a true root or outer endpoint.
Its entire circle belongs to the actual closed domain, and the actual
open domain lies on the correct side. This follows from the original
positive-domain and current negative-component clauses. -/
theorem n06_trueEndpoint_current_geometry
    (hC : controlGeometryConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (side : Bool) (htrue : ¬n06ArtificialCutSide K m side) :
    (∀ θ, (n06Endpoint (K.physicalLeft m) (K.physicalRight m) side, θ) ∈
      physicalPieceClosed S K z m) ∧
    (∀ p ∈ physicalPieceOpen S K z m,
      if side then p.1 < K.physicalRight m else K.physicalLeft m < p.1) := by
  by_cases hm : K.positive m = true
  · have hd := (h04.1.domains z hz hs m).2.2.2.2.2.1 hm
    have hclosed : physicalPieceClosed S K z m =
        Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ (univ : Set ℝ) := by
      rw [physicalPieceClosed, hd, referencePhysicalPieceOpen,
        closure_prod_eq, closure_Ioo (h04.1.referenceBounds m).1.ne, closure_univ]
    constructor
    · intro θ
      rw [hclosed]
      refine ⟨?_, mem_univ _⟩
      cases side
      · exact ⟨le_rfl, (h04.1.referenceBounds m).1.le⟩
      · exact ⟨(h04.1.referenceBounds m).1.le, le_rfl⟩
    · intro p hp
      have hp' : p ∈ referencePhysicalPieceOpen S K m := by
        rw [← hd]
        exact hp
      cases side
      · exact hp'.1.1
      · exact hp'.1.2
  · obtain ⟨n, rfl | rfl⟩ := n06_negativePiece_is_cutHalf h04 hC
      (Bool.eq_false_of_not_eq_true hm)
    · cases side
      · have hleft := (h04.2.1.1.1 n).2.2.1
        constructor
        · intro θ
          change (K.physicalLeft (K.cutPair n).1, θ) ∈ _
          rw [hleft]
          exact (n06_current_cutRoot_geometry h04 hz hs n).1 θ |>.1
        · intro p hp
          change K.physicalLeft (K.cutPair n).1 < p.1
          rw [hleft]
          exact ((n06_currentCutHalf_subset_component h04 hz hs n).1 hp).1.1
      · exact (htrue ⟨n, rfl⟩).elim
    · cases side
      · exact (htrue ⟨n, rfl⟩).elim
      · have hright := (h04.2.1.1.1 n).2.2.2.1
        constructor
        · intro θ
          change (K.physicalRight (K.cutPair n).2, θ) ∈ _
          rw [hright]
          exact (n06_current_cutRoot_geometry h04 hz hs n).2 θ |>.1
        · intro p hp
          change p.1 < K.physicalRight (K.cutPair n).2
          rw [hright]
          exact ((n06_currentCutHalf_subset_component h04 hz hs n).2 hp).1.2

/-- An adjacent pair with a positive member meets at two true sides.
The reference partition excludes identifying such a side with an
artificial negative middle cut. -/
theorem n06_positive_adjacent_trueSides
    (h04 : N04Properties D T S C L K base loss ε)
    {ml mr : ℕ} (hjoin : K.physicalRight ml = K.physicalLeft mr)
    (hpositive : K.positive ml = true ∨ K.positive mr = true) :
    ¬n06ArtificialCutSide K ml true ∧ ¬n06ArtificialCutSide K mr false := by
  have hlr := fun m => (h04.1.referenceBounds m).1
  have hd := n06_physicalPiece_pairwiseDisjoint h04
  have hinjL := n06_disjoint_intervals_left_injective hlr hd
  have hinjR := n06_disjoint_intervals_right_injective hlr hd
  constructor
  · rintro ⟨n, rfl⟩
    have hcut := h04.2.1.1.1 n
    have he : mr = (K.cutPair n).2 := hinjL (hjoin.symm.trans hcut.2.2.2.2.1)
    rcases hpositive with hp | hp
    · exact Bool.noConfusion (hp.symm.trans hcut.1)
    · rw [he] at hp
      exact Bool.noConfusion (hp.symm.trans hcut.2.1)
  · rintro ⟨n, rfl⟩
    have hcut := h04.2.1.1.1 n
    have he : ml = (K.cutPair n).1 := hinjR (hjoin.trans hcut.2.2.2.2.1.symm)
    rcases hpositive with hp | hp
    · rw [he] at hp
      exact Bool.noConfusion (hp.symm.trans hcut.1)
    · exact Bool.noConfusion (hp.symm.trans hcut.2.1)

end ContinuousFlexibility.Statements

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
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hrl : K.physicalRight ml ∈ Icc (K.physicalLeft ml) (K.physicalRight ml) :=
    ⟨(h04.1.referenceBounds ml).1.le, le_rfl⟩
  have hrr : K.physicalRight ml ∈ Icc (K.physicalLeft mr) (K.physicalRight mr) := by
    rw [hjoin]
    exact ⟨le_rfl, (h04.1.referenceBounds mr).1.le⟩
  have hp : K.physicalRight ml ∈ radialCore D :=
    n06_adjacentInterface_mem_core h04 hjoin
  have hpos : 0 ≤ deriv D.w (K.physicalRight ml) := by
    rcases hpositive with hl | hr
    · exact n06_positivePiece_closed_slope_nonneg h01 h04 ml hl hrl
    · exact n06_positivePiece_closed_slope_nonneg h01 h04 mr hr hrr
  have htrue := n06_positive_adjacent_trueSides h04 hjoin hpositive
  have hxL := n06_trueEndpoint_current_geometry h01.2.2.2.1 h04 hz hs ml true htrue.1
  have hxR' := n06_trueEndpoint_current_geometry h01.2.2.2.1 h04 hz hs mr false htrue.2
  have hxR : ∀ η, (K.physicalRight ml, η) ∈ physicalPieceClosed S K z mr := by
    rw [hjoin]
    exact hxR'.1
  obtain ⟨η, hη, hβη⟩ :=
    (n06_current_boundary_angular_surjOn Jl h04 hz hs hxL.1).2.2 hθ
  have he := n06N05_finite_current_root_boundaryDensity hS h hcoordinates hz hs
    u ml mr s vl vr hjoin hp Jl₀ Jr₀ hH₀ hρ₀ Jl Jr hxL.1 hxR Ql Qr hφ
    hvl hvr hmodeL hmodeR (L.coefficients z) hη
  have hrowL := n06_nonnegative_boundaryDensity hT hS h01 h03 h04 hz hs a ha hea heb hreg
    (if reverseL then !true else true) Jl hxL.1 hp hpos η
      Ql.value Ql.radial Ql.angular (r11bFiniteSynthesis s vl referenceAngularBasis)
  have hrowR := n06_nonnegative_boundaryDensity hT hS h01 h03 h04 hz hs a ha hea heb hreg
    (if reverseR then !false else false) Jr hxR hp hpos η
      Qr.value Qr.radial Qr.angular (r11bFiniteSynthesis s vr referenceAngularBasis)
  have hsignL := n06_current_boundary_radialSign_eq_reverse reverseL true Jl h04 hz hs hxL.1 hxL.2 η
  have Jr' : N06RootFirstJets (K.chart z mr) (K.height z mr) (K.physicalLeft mr)
      (n06Endpoint (K.left mr) (K.right mr) (if reverseR then !false else false))
        σr β H ρ κ Hr := by
    rw [← hjoin]
    exact Jr
  have hsignR := n06_current_boundary_radialSign_eq_reverse reverseR false Jr' h04 hz hs hxR'.1 hxR'.2 η
  rw [hrowL, hrowR, hsignL, hsignR, hβη] at he
  simpa only [n06OrientedCanonicalBoundary, n06Endpoint, mul_assoc] using he

/-- The original N04 cut law for current closed tests and the original
N05 cut law for actual modes give oriented matching directly at the same
canonical angle. No fixed current physical cut or cut first jets occur. -/
theorem n06N05_finite_current_cut_orientedMatching
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : B.Space) (n : ℕ) (s : Finset ℕ) (vl vr : ℕ → ℝ → ℝ)
    (Ql : N06CurrentHeightTestTraces S K z (K.cutPair n).1 φ)
    (Qr : N06CurrentHeightTestTraces S K z (K.cutPair n).2 φ)
    (hφ : ContDiff ℝ ∞ φ)
    (hvl : ∀ k ∈ s, ContDiff ℝ 1 (vl k))
    (hvr : ∀ k ∈ s, ContDiff ℝ 1 (vr k))
    (hmodeL : ∀ k ∈ s, n06HalfCosineCoefficient (u.val.1.1 (K.cutPair n).1) k
      =ᵐ[volume.restrict (Ioo (K.left (K.cutPair n).1) (K.right (K.cutPair n).1))] vl k)
    (hmodeR : ∀ k ∈ s, n06HalfCosineCoefficient (u.val.1.1 (K.cutPair n).2) k
      =ᵐ[volume.restrict (Ioo (K.left (K.cutPair n).2) (K.right (K.cutPair n).2))] vr k)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    n06OrientedCanonicalBoundary Ql (r11bFiniteSynthesis s vl referenceAngularBasis)
        (fun _ => 1) false true θ =
      n06OrientedCanonicalBoundary Qr (r11bFiniteSynthesis s vr referenceAngularBasis)
        (fun _ => 1) true false θ := by
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  obtain ⟨_, _, _, _, _, _, _, _, hyl, hyr⟩ := h04.2.1.1.1 n
  have he := n06N05_finite_current_cut_wronskians_cancel hS h hcoordinates hz hs
    u n s vl vr Ql Qr hφ hvl hvr hmodeL hmodeR hθ
  simp only [n06OrientedCanonicalBoundary, Bool.false_eq_true, if_false, if_true,
    Bool.not_false, Bool.not_true, one_mul, neg_one_mul, neg_mul, hyl, hyr]
  linarith only [he]

end ContinuousFlexibility.Analysis
