import ContinuousFlexibility.Analysis.OneSidedTaylorHighJets

/-!
# All root jets of the already chosen angular patch

At either root the two physical cutoffs are identically one and zero
on a genuine joint neighborhood. Thus the existing angular patch has
the full jet of its fixed Taylor polynomial, even above its radial
degree. The original same-order endpoint jet controls every order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem positiveAngularTaylorInterpolation_joint_root_germ
    (n : ℕ) {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ ≤ r - l)
    (A : Bool → ℕ → ℝ → ℝ) (side : Bool) (θ : ℝ) :
    positiveAngularTaylorInterpolation n l r δ A =ᶠ[𝓝 (if side then r else l, θ)]
      boundaryTaylorPolynomial n (if side then r else l) (A side) := by
  let c : ℝ := if side then r else l
  let d : ℝ := if side then l else r
  have hsep : 0 ≤ r - l := by linarith only [hδ, hgap]
  have hcd : δ ≤ |c - d| := by
    cases side with
    | false =>
        change δ ≤ |l - r|
        rw [abs_sub_comm, abs_of_nonneg hsep]
        linarith only [hδ, hgap]
    | true =>
        change δ ≤ |r - l|
        rw [abs_of_nonneg hsep]
        linarith only [hδ, hgap]
  have hone := (positiveEndpointCutoff_one_germ c δ).comp_tendsto
    (continuous_fst.continuousAt (x := (c, θ)))
  have hzero := (positiveEndpointCutoff_zero_germ_of_separation hδ hcd).comp_tendsto
    (continuous_fst.continuousAt (x := (c, θ)))
  change positiveAngularTaylorInterpolation n l r δ A =ᶠ[𝓝 (c, θ)]
    boundaryTaylorPolynomial n c (A side)
  filter_upwards [hone, hzero] with p hpone hpzero
  have hself : positiveEndpointCutoff c δ p.1 = 1 := hpone
  have hother : positiveEndpointCutoff d δ p.1 = 0 := hpzero
  cases side <;>
    simp only [c, d, Bool.false_eq_true, ite_false, ite_true] at hself hother ⊢ <;>
    simp only [positiveAngularTaylorInterpolation, positiveAngularTaylorPatch,
      hself, hother, one_mul, zero_mul] <;> ring

theorem norm_iteratedFDeriv_rawEndpointAngularInterpolation_root_le
    (n : ℕ) {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ ≤ r - l)
    (ψ : Bool → PolarPoint → ℝ) (a b : Bool → ℝ)
    (hab : ∀ side, a side < b side)
    (hend : ∀ side, (if side then r else l) ∈ Icc (a side) (b side))
    (hψ : ∀ side, ContDiffOn ℝ ∞ (ψ side)
      (Ioo (a side) (b side) ×ˢ (univ : Set ℝ)))
    (hroot : ∀ side θ, ContDiffAt ℝ ∞ (ψ side) (if side then r else l, θ))
    (side : Bool) (k : ℕ) (θ : ℝ) :
    ‖iteratedFDeriv ℝ k (positiveAngularTaylorInterpolation n l r δ
      (rawEndpointAngularData l r ψ)) (if side then r else l, θ)‖ ≤
        (2 : ℝ) ^ k * ‖iteratedFDeriv ℝ k (ψ side) (if side then r else l, θ)‖ := by
  have he := positiveAngularTaylorInterpolation_joint_root_germ n hδ hgap
    (rawEndpointAngularData l r ψ) side θ
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact norm_iteratedFDeriv_oneSidedBoundaryTaylorRepresentative_le
    (hab side) (hψ side) (hend side) (hroot side) n k θ

theorem norm_iteratedFDeriv_wholeComponentEndpointAngle_oneSided_root_le
    (n : ℕ) {l r c d κ M : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r) (hκ : 0 < κ) (hM : 0 ≤ M)
    (ψ : Bool → PolarPoint → ℝ) (a b : Bool → ℝ)
    (hab : ∀ side, a side < b side)
    (hend : ∀ side, (if side then r else l) ∈ Icc (a side) (b side))
    (hψ : ∀ side, ContDiffOn ℝ ∞ (ψ side)
      (Ioo (a side) (b side) ×ˢ (univ : Set ℝ)))
    (hroot : ∀ side θ, ContDiffAt ℝ ∞ (ψ side) (if side then r else l, θ))
    (side : Bool) (k : ℕ) (θ : ℝ) :
    ‖iteratedFDeriv ℝ k
      (wholeComponentEndpointAngle n (oneSidedEndpointRepresentative (n + 2) l r ψ)
        l r c d κ M) (if side then r else l, θ)‖ ≤
      (2 : ℝ) ^ k * ‖iteratedFDeriv ℝ k (ψ side) (if side then r else l, θ)‖ := by
  rw [wholeComponentEndpointAngle_oneSidedRepresentative]
  have hm := endpointAngularWidth_margins (n + 1) hlc hcd hdr hκ hM
  exact norm_iteratedFDeriv_rawEndpointAngularInterpolation_root_le (n + 1)
    hm.1 hm.2.2.1.le ψ a b hab hend hψ hroot side k θ

end ContinuousFlexibility.Analysis
