module

public import ContinuousFlexibility.Analysis.CylinderEndpointLocalization
public import ContinuousFlexibility.Analysis.PositiveEndpointRadialNormalization
public import ContinuousFlexibility.Analysis.AngularFiberFiniteJetBounds
public import ContinuousFlexibility.Analysis.PositiveReferenceCollarFactory
public import ContinuousFlexibility.Analysis.PositiveFiberCoordinates
public import ContinuousFlexibility.Analysis.BoundaryRadialFrechetJets

/-!
# A positive endpoint collar from actual root fields

The root field is smooth on a genuine open collar, which may depend on
the family member. A radial localization preserves every actual boundary
jet, and the true angular inverse transfers those finite jets to fixed
canonical angle. Their uniform finite bound selects one Taylor collar
and one positive radial lower bound before the family member.

The right endpoint is reflected and translated explicitly. The output
has the actual global smooth inverse, matches the original normalized
radial jets, and equals the fixed reference chart as a joint exit germ.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The hypotheses concern actual raw root jets and the separately
constructed angular lift. No Jacobian or inverse-jet bound of the output
is assumed. Taking the normalized endpoint value to be 0 on the left
and 1 on the right gives the usual ξ and 1 - ξ conventions. -/
theorem exists_positiveActualEndpointCollar_family
    {ι : Type*} {n : ℕ} {φ ψ ξ : ι → PolarPoint → ℝ}
    {Ref : PolarPoint → ℝ} {d : ι → ℝ}
    {l r ρ κφ κξ M Lref Mref v m T : ℝ} (root : Bool)
    (hlr : l < r) (hρ : 0 < ρ) (hκφ : 0 < κφ) (hκξ : 0 < κξ)
    (hM : 0 ≤ M) (hLref : 0 < Lref) (hMref : 0 ≤ Mref)
    (hm : 0 < m) (hT : T ≠ 0)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hφLower : ∀ i x θ, κφ ≤ deriv (fun η => φ i (x, η)) θ)
    (hperiod : ∀ i x θ, φ i (x, θ + T) = φ i (x, θ) + T)
    (hd : ∀ i, 0 < d i)
    (hξ : ∀ i (p : PolarPoint), p.1 ∈ Metric.ball (if root then r else l) (d i) →
      ContDiffAt ℝ ∞ (ξ i) p)
    (hξzero : ∀ i θ, ξ i (if root then r else l, θ) = 0)
    (hξLow : ∀ i θ, κξ ≤
      if root then -radialPartial (ξ i) (if root then r else l, θ)
      else radialPartial (ξ i) (if root then r else l, θ))
    (hψ : ∀ i (p : PolarPoint), p.1 ∈ Metric.ball (if root then r else l) (d i) →
      ContDiffAt ℝ ∞ (ψ i) p)
    (hφJet : ∀ i k, k ≤ n + 1 → ∀ θ,
      radialBoundaryJet (φ i) (if root then r else l) k θ =
        radialBoundaryJet (ψ i) (if root then r else l) k θ)
    (hψRaw : ∀ i k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
      ‖iteratedFDeriv ℝ k (ψ i) (if root then r else l, θ)‖ ≤ M)
    (hξRaw : ∀ i k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
      ‖iteratedFDeriv ℝ k (ξ i) (if root then r else l, θ)‖ ≤ M)
    (hRef : ContDiff ℝ ∞ Ref)
    (hRefValue : ∀ side, side ≠ root → ∀ θ,
      Ref (if side then r else l, θ) = if side then v + m else v)
    (hRefLow : ∀ side, side ≠ root → ∀ x,
      x ∈ Metric.ball (if side then r else l) ρ → ∀ θ,
        Lref ≤ radialPartial Ref (x, θ))
    (hRefBound : ∀ side, side ≠ root → ∀ x,
      x ∈ Metric.ball (if side then r else l) ρ → ∀ θ,
        |radialPartial Ref (x, θ)| ≤ Mref)
    (hφExit : ∀ i side, side ≠ root → ∀ θ,
      φ i =ᶠ[𝓝 (if side then r else l, θ)] (fun p : PolarPoint => p.2)) :
    ∃ δ B : ℝ, 0 < δ ∧ δ < ρ ∧ 2 * δ < r - l ∧ 0 < B ∧
      ∀ i : ι, ∃ Y : PolarPoint → ℝ,
        ContDiff ℝ ∞ Y ∧
        (∀ x θ, B ≤ deriv (fun t => Y (t, θ)) x) ∧
        (∀ (side : Bool) θ, Y (if side then r else l, θ) = if side then v + m else v) ∧
        (∀ k ≤ n + 1, ∀ θ,
          radialBoundaryJet (fun p => Y (p.1, φ i p)) (if root then r else l) k θ =
            radialBoundaryJet
              (positiveEndpointRadialNormalization root (if root then v + m else v) (ξ i))
              (if root then r else l) k θ) ∧
        (∀ side, side ≠ root → ∀ θ,
          Y =ᶠ[𝓝 (if side then r else l, θ)] Ref) ∧
        (∀ side, side ≠ root → ∀ θ,
          positiveFiberChart (φ i) Y =ᶠ[𝓝 (if side then r else l, θ)]
            (fun p : PolarPoint => (Ref p, p.2))) ∧
        (ContDiff ℝ ∞ (positiveFiberChart (φ i) Y) ∧
          ContDiff ℝ ∞ (positiveFiberChartInverse (φ i) Y) ∧
          Function.LeftInverse (positiveFiberChartInverse (φ i) Y)
            (positiveFiberChart (φ i) Y) ∧
          Function.RightInverse (positiveFiberChartInverse (φ i) Y)
            (positiveFiberChart (φ i) Y) ∧
          ∀ p, B * κφ ≤ planeJacobian (positiveFiberChart (φ i) Y) p) ∧
        BijOn (positiveFiberChart (φ i) Y) (Ioo l r ×ˢ (univ : Set ℝ))
          (Ioo v (v + m) ×ˢ (univ : Set ℝ)) := by
  let c : ℝ := if root then r else l
  let e : ℝ := if root then v + m else v
  let N : ι → PolarPoint → ℝ := fun i =>
    positiveEndpointRadialNormalization root e (ξ i)
  let X : ι → PolarPoint → ℝ := fun i =>
    cylinderEndpointLocalization c (d i) (N i)
  have hφRaw (i : ι) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) (θ : ℝ) :
      ‖iteratedFDeriv ℝ k (φ i) (c, θ)‖ ≤ M := by
    let U : Set PolarPoint := Metric.ball c (d i) ×ˢ (univ : Set ℝ)
    have hU : IsOpen U := Metric.isOpen_ball.prod isOpen_univ
    have hψU : ContDiffOn ℝ ∞ (ψ i) U :=
      fun p hp => (hψ i p hp.1).contDiffWithinAt
    exact norm_iteratedFDeriv_le_of_radialBoundaryJets_eq
      hU (hφ i).contDiffOn hψU c
      (fun η => ⟨Metric.mem_ball_self (hd i), mem_univ η⟩)
      (hφJet i) hkn (hψRaw i k hk hkn θ)
  have hξAt (i : ι) (θ : ℝ) : ContDiffAt ℝ ∞ (ξ i) (c, θ) :=
    hξ i (c, θ) (Metric.mem_ball_self (hd i))
  have hN (i : ι) (p : PolarPoint) (hp : p.1 ∈ Metric.ball c (d i)) :
      ContDiffAt ℝ ∞ (N i) p :=
    contDiffAt_positiveEndpointRadialNormalization root e (hξ i p hp)
  have hX (i : ι) : ContDiff ℝ ∞ (X i) :=
    contDiff_cylinderEndpointLocalization (hd i) (hN i)
  have hXgerm (i : ι) (θ : ℝ) : X i =ᶠ[𝓝 (c, θ)] N i :=
    cylinderEndpointLocalization_eventuallyEq c (d i) (N i) θ
  have hXvalue (i : ι) (θ : ℝ) : X i (c, θ) = e :=
    (hXgerm i θ).eq_of_nhds.trans
      (positiveEndpointRadialNormalization_boundary root e (hξzero i) θ)
  have hXlow (i : ι) (θ : ℝ) : κξ ≤ radialPartial (X i) (c, θ) := by
    change κξ ≤ fderiv ℝ (X i) (c, θ) (1, 0)
    rw [(hXgerm i θ).fderiv_eq (𝕜 := ℝ)]
    change κξ ≤ radialPartial (N i) (c, θ)
    rw [radialPartial_positiveEndpointRadialNormalization root e
      ((hξAt i θ).differentiableAt (by simp))]
    exact hξLow i θ
  have hXraw (i : ι) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) (θ : ℝ) :
      ‖iteratedFDeriv ℝ k (X i) (c, θ)‖ ≤ M := by
    rw [iteratedFDeriv_cylinderEndpointLocalization_boundary,
      norm_iteratedFDeriv_positiveEndpointRadialNormalization root e (hξAt i θ) hk]
    exact hξRaw i k hk hkn θ
  have hpositive (i : ι) (p : PolarPoint) :
      0 < deriv (fun θ => φ i (p.1, θ)) p.2 :=
    hκφ.trans_le (hφLower i p.1 p.2)
  have hangle (i : ι) (θ : ℝ) : κφ ≤ angularPartial (φ i) (c, θ) := by
    rw [← deriv_cylinder_angular_slice ((hφ i).differentiable (by simp)) c θ]
    exact hφLower i c θ
  have hφradial (i : ι) (θ : ℝ) : |radialPartial (φ i) (c, θ)| ≤ M := by
    have hfirst : ‖fderiv ℝ (φ i) (c, θ)‖ ≤ M := by
      simpa only [norm_iteratedFDeriv_one] using
        hφRaw i 1 le_rfl (by omega) θ
    have hunit : |radialPartial (φ i) (c, θ)| ≤ ‖fderiv ℝ (φ i) (c, θ)‖ := by
      simpa [radialPartial, Prod.norm_def] using
        (fderiv ℝ (φ i) (c, θ)).le_opNorm (1, 0)
    exact hunit.trans hfirst
  let σ : ι → PolarPoint → ℝ := fun i => angularFiberPullback (φ i) (X i)
  let A : ι → ℕ → ℝ → ℝ := fun i => radialBoundaryJet (σ i) c
  have hσ (i : ι) : ContDiff ℝ ∞ (σ i) :=
    contDiff_angularFiberPullback hT (hφ i) (hX i) (hpositive i) (hperiod i)
  obtain ⟨Mσ, hMσ, hσBound⟩ :=
    exists_angularFiberBoundaryJets_bound (n + 1) hκφ hM
  have hAbound (i : ι) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) (θ : ℝ) :
      |A i k θ| ≤ Mσ :=
    hσBound (φ i) (X i) T hT (hφ i) (hX i) (hpositive i) (hperiod i)
      c (hangle i) (hφradial i) (hφRaw i) (hXraw i) k hk hkn θ
  have hAvalue (i : ι) (θ : ℝ) : A i 0 θ = e := by
    change iteratedDeriv 0 (fun x => σ i (x, θ)) c = e
    simpa only [iteratedDeriv_zero] using
      angularFiberPullback_boundary (φ := φ i) (hXvalue i) θ
  have hAlow (i : ι) (θ : ℝ) : κξ ≤ A i 1 θ := by
    change κξ ≤ iteratedDeriv 1 (fun x => σ i (x, θ)) c
    rw [iteratedDeriv_one,
      deriv_cylinder_radial_slice ((hσ i).differentiable (by simp)) c θ,
      radialPartial_angularFiberPullback_boundary hT (hφ i) (hX i)
        (hpositive i) (hperiod i) (hXvalue i)]
    exact hXlow i _
  obtain ⟨δ, B, hδ, hδρ, hgap, hB, hFactory⟩ :=
    exists_positiveReferenceCollar_family root hlr hρ hκξ
      (zero_le_one.trans hMσ) hLref hMref hm
      (fun i j _ => contDiff_radialBoundaryJet (hσ i) c j)
      hAvalue hAlow hAbound hRef hRefValue hRefLow hRefBound
  refine ⟨δ, B, hδ, hδρ, hgap, hB, ?_⟩
  intro i
  let Y := positiveReferenceCollarCoordinate n l r δ v m root (A i) Ref
  obtain ⟨hY, hYlow, hYvalue, hYjet, hYgerm⟩ := hFactory i
  have hphysical := radialBoundaryJets_angularFiber_composition
    hT (hφ i) (hX i) hY (hpositive i) (hperiod i) hYjet
  refine ⟨Y, hY, hYlow, hYvalue, ?_, hYgerm, ?_,
    positiveFiberChart_geometry (hφ i) hY hκφ hB hT (hφLower i) hYlow (hperiod i),
    positiveFiberChart_bijOn_openStrip (hφ i) hY hκφ hB hT
      (hφLower i) hYlow (hperiod i) (hYvalue false) (hYvalue true)⟩
  · intro k hk θ
    have hs := (hXgerm i θ).comp_tendsto
      ((continuous_id.prodMk (continuous_const (y := θ))).tendsto c)
    have hj : radialBoundaryJet (X i) c k θ = radialBoundaryJet (N i) c k θ := by
      simpa only [radialBoundaryJet, Function.comp_def, id_eq] using
        (hs.iteratedDeriv k).eq_of_nhds
    exact (hphysical k hk θ).trans hj
  · intro side hs θ
    filter_upwards [hYgerm side hs θ, hφExit i side hs θ] with p hpY hpφ
    apply Prod.ext
    · change Y (p.1, φ i p) = Ref p
      rw [hpφ]
      exact hpY
    · exact hpφ

end ContinuousFlexibility.Analysis
