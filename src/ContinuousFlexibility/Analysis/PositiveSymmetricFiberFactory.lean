module

public import ContinuousFlexibility.Analysis.AngularFiberFiniteJetBounds
public import ContinuousFlexibility.Analysis.PositiveFiberInterpolationSymmetry
public import ContinuousFlexibility.Analysis.PositiveAngularTaylorInterpolation

/-!
# Positive fiber collars from actual symmetric endpoint fields

The radial field may depend on the angle. Its true inverse-angle jets
are bounded by the already proved finite inverse estimate, then the
explicit mass-corrected primitive realizes them. Periodicity and
reflection follow from that explicit primitive. The collar width and
positive radial lower bound are selected before the family member.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The angular interpolation is the identity as a joint germ away from
the two radial collars, not merely pointwise on the middle interval. -/
theorem positiveAngularTaylorInterpolation_angle_germ
    (n : ℕ) {l r δ x : ℝ} (hδ : 0 < δ) (A : Bool → ℕ → ℝ → ℝ)
    (hxL : x ∉ Metric.ball l δ) (hxR : x ∉ Metric.ball r δ) (θ : ℝ) :
    positiveAngularTaylorInterpolation n l r δ A =ᶠ[𝓝 (x, θ)]
      (fun p : PolarPoint => p.2) := by
  have hL := (positiveEndpointCutoff_zero_germ_of_not_mem_ball hδ hxL).comp_tendsto
    (continuous_fst.continuousAt (x := (x, θ)))
  have hR := (positiveEndpointCutoff_zero_germ_of_not_mem_ball hδ hxR).comp_tendsto
    (continuous_fst.continuousAt (x := (x, θ)))
  filter_upwards [hL, hR] with p hpL hpR
  have hpL' : positiveEndpointCutoff l δ p.1 = 0 := hpL
  have hpR' : positiveEndpointCutoff r δ p.1 = 0 := hpR
  simp only [positiveAngularTaylorInterpolation, positiveAngularTaylorPatch,
    hpL', hpR', zero_mul]
  ring

/-- These hypotheses concern actual raw coordinate jets. They do not
assume a Jacobian estimate or an inverse estimate for the output. -/
theorem exists_positiveSymmetricFiberCollar_family
    {ι : Type*} {n : ℕ} {φ X : ι → PolarPoint → ℝ} {Ref : PolarPoint → ℝ}
    {l r ρ κφ κX M Lref Mref v m T : ℝ} (root : Bool)
    (hlr : l < r) (hρ : 0 < ρ) (hκφ : 0 < κφ) (hκX : 0 < κX)
    (hM : 0 ≤ M) (hLref : 0 < Lref) (hMref : 0 ≤ Mref) (hm : 0 < m) (hT : T ≠ 0)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hX : ∀ i, ContDiff ℝ ∞ (X i))
    (hφLower : ∀ i x θ, κφ ≤ deriv (fun η => φ i (x, η)) θ)
    (hφperiod : ∀ i x θ, φ i (x, θ + T) = φ i (x, θ) + T)
    (hφodd : ∀ i x θ, φ i (x, -θ) = -φ i (x, θ))
    (hXperiod : ∀ i x θ, X i (x, θ + T) = X i (x, θ))
    (hXeven : ∀ i x θ, X i (x, -θ) = X i (x, θ))
    (hXvalue : ∀ i θ, X i (if root then r else l, θ) = if root then v + m else v)
    (hXlow : ∀ i θ, κX ≤ radialPartial (X i) (if root then r else l, θ))
    (hφraw : ∀ i k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
      ‖iteratedFDeriv ℝ k (φ i) (if root then r else l, θ)‖ ≤ M)
    (hXraw : ∀ i k, 1 ≤ k → k ≤ n + 1 → ∀ θ,
      ‖iteratedFDeriv ℝ k (X i) (if root then r else l, θ)‖ ≤ M)
    (hRef : ContDiff ℝ ∞ Ref)
    (hRefperiod : ∀ x θ, Ref (x, θ + T) = Ref (x, θ))
    (hRefeven : ∀ x θ, Ref (x, -θ) = Ref (x, θ))
    (hRefValue : ∀ side, side ≠ root → ∀ θ,
      Ref (if side then r else l, θ) = if side then v + m else v)
    (hRefLow : ∀ side, side ≠ root → ∀ x,
      x ∈ Metric.ball (if side then r else l) ρ → ∀ θ,
        Lref ≤ radialPartial Ref (x, θ))
    (hRefBound : ∀ side, side ≠ root → ∀ x,
      x ∈ Metric.ball (if side then r else l) ρ → ∀ θ,
        |radialPartial Ref (x, θ)| ≤ Mref) :
    ∃ δ B : ℝ, 0 < δ ∧ δ < ρ ∧ 2 * δ < r - l ∧ 0 < B ∧
      ∀ i : ι, ∃ Y : PolarPoint → ℝ,
        ContDiff ℝ ∞ Y ∧
        (∀ x θ, B ≤ deriv (fun t => Y (t, θ)) x) ∧
        (∀ (side : Bool) θ, Y (if side then r else l, θ) = if side then v + m else v) ∧
        (∀ k ≤ n + 1, ∀ θ,
          radialBoundaryJet (fun p => Y (p.1, φ i p)) (if root then r else l) k θ =
            radialBoundaryJet (X i) (if root then r else l) k θ) ∧
        (∀ side, side ≠ root → ∀ θ,
          Y =ᶠ[𝓝 (if side then r else l, θ)] Ref) ∧
        (∀ x θ, Y (x, θ + T) = Y (x, θ)) ∧
        (∀ x θ, Y (x, -θ) = Y (x, θ)) := by
  let c : ℝ := if root then r else l
  have hpositive (i : ι) (p : PolarPoint) :
      0 < deriv (fun θ => φ i (p.1, θ)) p.2 :=
    hκφ.trans_le (hφLower i p.1 p.2)
  have hangle (i : ι) (θ : ℝ) : κφ ≤ angularPartial (φ i) (c, θ) := by
    rw [← deriv_cylinder_angular_slice ((hφ i).differentiable (by simp)) c θ]
    exact hφLower i c θ
  have hφradial (i : ι) (θ : ℝ) : |radialPartial (φ i) (c, θ)| ≤ M := by
    have hfirst : ‖fderiv ℝ (φ i) (c, θ)‖ ≤ M := by
      simpa only [norm_iteratedFDeriv_one] using hφraw i 1 le_rfl (by omega) θ
    have hu : |radialPartial (φ i) (c, θ)| ≤ ‖fderiv ℝ (φ i) (c, θ)‖ := by
      simpa [radialPartial, Prod.norm_def] using (fderiv ℝ (φ i) (c, θ)).le_opNorm (1, 0)
    exact hu.trans hfirst
  let σ : ι → PolarPoint → ℝ := fun i => angularFiberPullback (φ i) (X i)
  let A : ι → ℕ → ℝ → ℝ := fun i => radialBoundaryJet (σ i) c
  have hσ (i : ι) : ContDiff ℝ ∞ (σ i) :=
    contDiff_angularFiberPullback hT (hφ i) (hX i) (hpositive i) (hφperiod i)
  obtain ⟨Mσ, hMσ, hσBound⟩ := exists_angularFiberBoundaryJets_bound (n + 1) hκφ hM
  have hAbound (i : ι) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) (θ : ℝ) :
      |A i k θ| ≤ Mσ :=
    hσBound (φ i) (X i) T hT (hφ i) (hX i) (hpositive i) (hφperiod i)
      c (hangle i) (hφradial i) (hφraw i) (hXraw i) k hk hkn θ
  have hAvalue (i : ι) (θ : ℝ) : A i 0 θ = if root then v + m else v := by
    change iteratedDeriv 0 (fun x => σ i (x, θ)) c = _
    simpa only [iteratedDeriv_zero] using
      angularFiberPullback_boundary (φ := φ i) (hXvalue i) θ
  have hAlow (i : ι) (θ : ℝ) : κX ≤ A i 1 θ := by
    change κX ≤ iteratedDeriv 1 (fun x => σ i (x, θ)) c
    rw [iteratedDeriv_one, deriv_cylinder_radial_slice ((hσ i).differentiable (by simp)) c θ,
      radialPartial_angularFiberPullback_boundary hT (hφ i) (hX i)
        (hpositive i) (hφperiod i) (hXvalue i)]
    exact hXlow i _
  obtain ⟨δ, B, hδ, hδρ, hgap, hB, hFactory⟩ :=
    exists_positiveReferenceCollar_family root hlr hρ hκX (zero_le_one.trans hMσ)
      hLref hMref hm (fun i j _ => contDiff_radialBoundaryJet (hσ i) c j)
      hAvalue hAlow hAbound hRef hRefValue hRefLow hRefBound
  refine ⟨δ, B, hδ, hδρ, hgap, hB, ?_⟩
  intro i
  let Y := positiveReferenceCollarCoordinate n l r δ v m root (A i) Ref
  obtain ⟨hY, hYlow, hYvalue, hYjet, hYgerm⟩ := hFactory i
  refine ⟨Y, hY, hYlow, hYvalue,
    radialBoundaryJets_angularFiber_composition hT (hφ i) (hX i) hY
      (hpositive i) (hφperiod i) hYjet, hYgerm, ?_, ?_⟩
  · intro x θ
    apply positiveReferenceCollarCoordinate_angleInvariant
      (fun j _ => contDiff_radialBoundaryJet (hσ i) c j) hRef (fun η => η + T)
    · intro j _ η
      exact radialBoundaryJet_angleInvariant (fun η => η + T)
        (angularFiberPullback_periodic hT (hφ i) (hpositive i) (hφperiod i) (hXperiod i)) c j η
    · exact hRefperiod
  · intro x θ
    apply positiveReferenceCollarCoordinate_angleInvariant
      (fun j _ => contDiff_radialBoundaryJet (hσ i) c j) hRef (fun η => -η)
    · intro j _ η
      exact radialBoundaryJet_angleInvariant (fun η => -η)
        (angularFiberPullback_reflect hT (hφ i) (hpositive i) (hφperiod i)
          (hφodd i) (hXeven i)) c j η
    · exact hRefeven

end ContinuousFlexibility.Analysis
