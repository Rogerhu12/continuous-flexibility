module

public import ContinuousFlexibility.Analysis.N06PrimitiveModalTraces
public import ContinuousFlexibility.Analysis.N06PrimitiveAtlasTransmissionJets
public import ContinuousFlexibility.Analysis.N05N06ClosedChartBridge

/-!
# Finite true boundary matching from the original primitive atlas

The original graph's actual modes obey the reference root and moving-cut
trace laws. Genuine common forward first jets carry the root traces to
the current charts. The original affine cut law cancels its two true
Wronskians directly. This uses the same K and no controlled-coordinate
window, replacement atlas, or matching premise on the finite fields.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial CanonicalGeometry
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {Vol : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K Vol b} {z : AnnularState S × ℝ}
  {φ : PolarPoint → ℝ}

theorem n06N05_primitive_finite_current_root_orientedMatching
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (hradial : ReferenceRadial S C K)
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
  have htrace (n : ℕ) (hn : n ∈ s) :=
    n06N05_primitive_canonicalMode_root_traces hS h hradial u ml mr n (vl n) (vr n)
      hjoin hp Jl₀ Jr₀ hH₀ hρ₀ (hvl n hn) (hvr n hn) (hmodeL n hn) (hmodeR n hn)
  have hbasis : ∀ n ∈ s, ContDiff ℝ 1 (referenceAngularBasis n) :=
    fun n _ => (contDiff_referenceAngularBasis n).of_le (by simp)
  have hWl : ContDiff ℝ 1 (r11bFiniteSynthesis s vl referenceAngularBasis) :=
    ContDiff.sum (fun n hn => ((hvl n hn).comp contDiff_fst).mul
      ((hbasis n hn).comp contDiff_snd))
  have hWr : ContDiff ℝ 1 (r11bFiniteSynthesis s vr referenceAngularBasis) :=
    ContDiff.sum (fun n hn => ((hvr n hn).comp contDiff_fst).mul
      ((hbasis n hn).comp contDiff_snd))
  let yl := n06Endpoint (K.left ml) (K.right ml) (if reverseL then !true else true)
  let yr := n06Endpoint (K.left mr) (K.right mr) (if reverseR then !false else false)
  have hvalue (t : ℝ) : r11bFiniteSynthesis s vl referenceAngularBasis (yl, t) =
      r11bFiniteSynthesis s vr referenceAngularBasis (yr, t) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [(htrace n hn).1]
  have hnormal (t : ℝ) :
      σl * radialPartial (r11bFiniteSynthesis s vl referenceAngularBasis) (yl, t) =
        σr * radialPartial (r11bFiniteSynthesis s vr referenceAngularBasis) (yr, t) := by
    rw [n06_radialPartial_finiteSynthesis_one s vl referenceAngularBasis hvl hbasis,
      n06_radialPartial_finiteSynthesis_one s vr referenceAngularBasis hvr hbasis]
    simp only [r11bFiniteSynthesis, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← mul_assoc, (htrace n hn).2, mul_assoc]
  have hmatch := n06_root_reconstruction_firstJets_match Jl Jr
    (fun t => hWl.differentiable (by norm_num) (_, t))
    (fun t => hWr.differentiable (by norm_num) (_, t)) hvalue hnormal η
  have hflux : symmetricNormalFlux (L.coefficients z).a (L.coefficients z).b
      (fun p => K.height z ml p * r11bFiniteSynthesis s vl referenceAngularBasis
        (K.chart z ml p)) (K.physicalRight ml, η) =
      symmetricNormalFlux (L.coefficients z).a (L.coefficients z).b
        (fun p => K.height z mr p * r11bFiniteSynthesis s vr referenceAngularBasis
          (K.chart z mr p)) (K.physicalRight ml, η) := by
    simp only [symmetricNormalFlux, hmatch.2.1, hmatch.2.2]
  have he := n06_current_root_boundaryDensity_eq_of_value_conormal Jl Jr Ql Qr
    h04 hz hs hφ hxL.1 hxR hη (L.coefficients z)
    (hWl.differentiable (by norm_num) _) (hWr.differentiable (by norm_num) _)
    hmatch.1 hflux
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

theorem n06N05_primitive_finite_current_cut_orientedMatching
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (hradial : ReferenceRadial S C K)
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
  have htest := n06_current_cut_test_traces h04 hz hs n Ql Qr hφ hθ
  have hbasis : ∀ k ∈ s, ContDiff ℝ 1 (referenceAngularBasis k) :=
    fun k _ => (contDiff_referenceAngularBasis k).of_le (by simp)
  have htrace (k : ℕ) (hk : k ∈ s) :=
    n06N05_primitive_canonicalMode_cut_traces hS h hradial u n k (vl k) (vr k)
      (hvl k hk) (hvr k hk) (hmodeL k hk) (hmodeR k hk)
  have hsum := n06_finiteSynthesis_cut_traces s vl vr referenceAngularBasis
    hvl hvr hbasis htrace θ
  have he := n06_affine_cut_wronskians_cancel htest.1 hsum.1 htest.2.1 hsum.2
  simp only [n06OrientedCanonicalBoundary, Bool.false_eq_true, if_false, if_true,
    Bool.not_false, Bool.not_true, one_mul, neg_one_mul, neg_mul, hyl, hyr]
  linarith only [he]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial CanonicalGeometry
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {Vol : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K Vol b} {z : AnnularState S × ℝ}

theorem n06N05_primitive_finite_atlas_orientedMatching
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (hradial : ReferenceRadial S C K)
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
    exact n06N05_primitive_finite_current_root_orientedMatching hT hS h hradial hz hs
      a ha hea heb hreg u ml mr s (v ml) (v mr) (reverse ml) (reverse mr) hjoin
      hpositive Jl₀ Jr₀ hH₀ hρ₀ Jl Jr (Q ml) (Q mr) hφ
      (hv ml) (hv mr) (hmode ml) (hmode mr) hθ
  · obtain ⟨n, rfl, rfl⟩ := hcut
    have hcuts := h04.2.1.1.1 n
    have hreverse := J.negative_reverse h01.2.2.2.1 h04 hz hs n
    have he := n06N05_primitive_finite_current_cut_orientedMatching hS h hradial hz hs
      u n s (v (K.cutPair n).1) (v (K.cutPair n).2)
      (Q (K.cutPair n).1) (Q (K.cutPair n).2) hφ
      (hv _) (hv _) (hmode _) (hmode _) hθ
    simpa only [hcuts.1, hcuts.2.1, Bool.false_eq_true, if_false,
      hreverse.1, hreverse.2] using he

end ContinuousFlexibility.Statements
