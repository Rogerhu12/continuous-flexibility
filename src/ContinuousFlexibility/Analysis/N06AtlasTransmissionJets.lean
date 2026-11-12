import ContinuousFlexibility.Analysis.N06FiniteBoundaryMatching

/-!
# Genuine atlas jets give every finite modal matching condition

The geometric input records only values and first derivatives of the
actual forward charts and heights. It contains no reconstructed-field
matching condition. At ordinary interfaces the reference and current
charts share their boundary jets; at the prescribed negative cuts they
satisfy the original affine height-jet law.

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
atlas. These are geometric realization requirements; no modal value,
conormal, weak equation, or Green matching is a field of this structure. -/
structure N06AtlasTransmissionJets
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (reverse : ℕ → Bool) : Prop where
  endpoints : ∀ m, ∀ side : Bool, ∃ σ : ℝ, ∃ β H ρ κ Hr : ℝ → ℝ,
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
  cuts : ∀ n, ∃ σ : ℝ, ∃ β₀ H₀ ρ₀ κ₀ Hr₀ β H ρ κ Hr : ℝ → ℝ,
      N06RootFirstJets (K.chart (C.referenceState, 0) (K.cutPair n).1)
        (K.height (C.referenceState, 0) (K.cutPair n).1)
        (K.physicalRight (K.cutPair n).1) (K.cutRadius n) σ β₀ H₀ ρ₀ κ₀ Hr₀ ∧
      N06RootFirstJets (K.chart (C.referenceState, 0) (K.cutPair n).2)
        (K.height (C.referenceState, 0) (K.cutPair n).2)
        (K.physicalRight (K.cutPair n).1) (K.cutRadius n) (-σ) β₀ H₀ ρ₀ κ₀
          (fun θ => Hr₀ θ - H₀ θ * (σ * ρ₀ θ) * (2 * K.cutRadius n)⁻¹) ∧
      N06RootFirstJets (K.chart z (K.cutPair n).1) (K.height z (K.cutPair n).1)
        (K.physicalRight (K.cutPair n).1) (K.cutRadius n) σ β H ρ κ Hr ∧
      N06RootFirstJets (K.chart z (K.cutPair n).2) (K.height z (K.cutPair n).2)
        (K.physicalRight (K.cutPair n).1) (K.cutRadius n) (-σ) β H ρ κ
          (fun θ => Hr θ - H θ * (σ * ρ θ) * (2 * K.cutRadius n)⁻¹)

private theorem n06_reverse_eq_of_upper_endpoint
    {l r : ℝ} (hlr : l < r) (reverse side : Bool)
    (he : n06Endpoint l r (if reverse then !side else side) = r) :
    reverse = !side := by
  cases reverse <;> cases side <;> simp_all [n06Endpoint, ne_of_lt hlr]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {Vol : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K Vol b} {z : AnnularState S × ℝ}

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
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2
  rcases n06_adjacentPiece_positive_or_cutPair h01 h04 hjoin with hpositive | hcut
  · obtain ⟨σl, σr, β₀, H₀, ρ₀, κ₀, Hr₀, β, H, ρ, κ, Hr, Jl₀, Jr₀, Jl, Jr⟩ :=
      J.roots ml mr hjoin hpositive
    have href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
      n05_referenceState_mem h01.2.1
    have hsref : stateSector S C.referenceState := n05_referenceState_sector h01.2.2.1
    have hr : K.physicalRight ml ∈ Icc (K.physicalLeft ml) (K.physicalRight ml) :=
      ⟨(h04.2.2.2.1 ml).1.le, le_rfl⟩
    have hb := h04.2.2.2.2.2.2.2.2.1 (C.referenceState, 0) href hsref ml
      (K.physicalRight ml, 0) hr
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
    have hfull := h04
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcuts, _⟩ := hfull
    obtain ⟨hlneg, hrneg, _, _, hcutjoin, _, _, _, hyl, hyr⟩ := hcuts n
    obtain ⟨σ, β₀, H₀, ρ₀, κ₀, Hr₀, β, H, ρ, κ, Hr, Jl₀, Jr₀, Jl, Jr⟩ := J.cuts n
    have hreverseL : reverse (K.cutPair n).1 = false := by
      obtain ⟨σe, βe, He, ρe, κe, Hre, ⟨Je⟩⟩ := J.endpoints (K.cutPair n).1 true
      have he : n06Endpoint (K.left (K.cutPair n).1) (K.right (K.cutPair n).1)
          (if reverse (K.cutPair n).1 then !true else true) = K.right (K.cutPair n).1 := by
        have h₁ := congrArg Prod.fst (Je.chart_value 0)
        have h₂ := congrArg Prod.fst (Jl.chart_value 0)
        exact h₁.symm.trans (h₂.trans hyl.symm)
      exact n06_reverse_eq_of_upper_endpoint (h04.2.2.2.1 (K.cutPair n).1).2.1 _ true he
    have hreverseR : reverse (K.cutPair n).2 = true := by
      obtain ⟨σe, βe, He, ρe, κe, Hre, ⟨Je⟩⟩ := J.endpoints (K.cutPair n).2 false
      have he : n06Endpoint (K.left (K.cutPair n).2) (K.right (K.cutPair n).2)
          (if reverse (K.cutPair n).2 then !false else false) = K.right (K.cutPair n).2 := by
        have h₁ := congrArg Prod.fst (Je.chart_value 0)
        have h₂ := congrArg Prod.fst (Jr.chart_value 0)
        change (K.chart z (K.cutPair n).2 (K.physicalLeft (K.cutPair n).2, 0)).1 = _ at h₁
        rw [← hcutjoin] at h₁
        exact h₁.symm.trans (h₂.trans hyr.symm)
      exact n06_reverse_eq_of_upper_endpoint (h04.2.2.2.1 (K.cutPair n).2).2.1 _ false he
    have he := n06N05_finite_current_cut_orientedMatching hS h hcoordinates hz hs
      u (K.cutPair n).1 (K.cutPair n).2 s (v (K.cutPair n).1) (v (K.cutPair n).2)
      hcutjoin hyl.symm hyr.symm Jl₀ Jr₀ Jl Jr (Q (K.cutPair n).1) (Q (K.cutPair n).2)
      hφ (hv (K.cutPair n).1) (hv (K.cutPair n).2)
      (hmode (K.cutPair n).1) (hmode (K.cutPair n).2) hθ
    simpa only [hlneg, hrneg, Bool.false_eq_true, if_false, hreverseL, hreverseR] using he

end ContinuousFlexibility.Statements
