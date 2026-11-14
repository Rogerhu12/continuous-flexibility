module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsKernelPrimitive
public import ContinuousFlexibility.Analysis.PositiveReferenceAffineDifference

/-!
# Uniform jets through the two actual radial collars

The reference exit neighborhood is uniform in the free coefficients.
Consequently each full coefficient/radial jet of the glued kernel is a
jet of one of its two collars or of the identity radial coordinate.
The same three uniform polynomial envelopes therefore bound the glue,
including both interface radii.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff BigOperators

private def radialSplice {P : Type*} (c d : ℝ) (L R : P × ℝ → ℝ)
    (p : P × ℝ) : ℝ :=
  if p.2 < c then L p else if p.2 < d then p.2 else R p

private theorem radialSplice_eventuallyEq {P : Type*} [TopologicalSpace P]
    {c d : ℝ} (hcd : c < d) (L R : P × ℝ → ℝ)
    (hL : ∃ ε : ℝ, 0 < ε ∧ ∀ a t, t ∈ Metric.ball c ε → L (a, t) = t)
    (hR : ∃ ε : ℝ, 0 < ε ∧ ∀ a t, t ∈ Metric.ball d ε → R (a, t) = t)
    (p : P × ℝ) :
    radialSplice c d L R =ᶠ[𝓝 p] L ∨
      radialSplice c d L R =ᶠ[𝓝 p] Prod.snd ∨
      radialSplice c d L R =ᶠ[𝓝 p] R := by
  rcases lt_trichotomy p.2 c with hpc | hpc | hcp
  · left
    filter_upwards [continuousAt_snd.eventually (eventually_lt_nhds hpc)] with q hq
    simp only [radialSplice, if_pos hq]
  · right; left
    obtain ⟨ε, hε, hmatch⟩ := hL
    have hball : p.2 ∈ Metric.ball c ε := by simpa only [hpc] using Metric.mem_ball_self hε
    have hpd : p.2 < d := hpc.trans_lt hcd
    filter_upwards [continuousAt_snd.eventually (Metric.isOpen_ball.mem_nhds hball),
      continuousAt_snd.eventually (eventually_lt_nhds hpd)] with q hq hqd
    by_cases hqc : q.2 < c
    · simpa only [radialSplice, if_pos hqc] using hmatch q.1 q.2 hq
    · simp only [radialSplice, if_neg hqc, if_pos hqd]
  · rcases lt_trichotomy p.2 d with hpd | hpd | hdp
    · right; left
      filter_upwards [continuousAt_snd.eventually (eventually_gt_nhds hcp),
        continuousAt_snd.eventually (eventually_lt_nhds hpd)] with q hqc hqd
      simp only [radialSplice, if_neg (not_lt.mpr hqc.le), if_pos hqd]
    · right; left
      obtain ⟨ε, hε, hmatch⟩ := hR
      have hball : p.2 ∈ Metric.ball d ε := by simpa only [hpd] using Metric.mem_ball_self hε
      filter_upwards [continuousAt_snd.eventually (eventually_gt_nhds hcp),
        continuousAt_snd.eventually (Metric.isOpen_ball.mem_nhds hball)] with q hqc hq
      by_cases hqd : q.2 < d
      · simp only [radialSplice, if_neg (not_lt.mpr hqc.le), if_pos hqd]
      · simpa only [radialSplice, if_neg (not_lt.mpr hqc.le), if_neg hqd] using
          hmatch q.1 q.2 hq
    · right; right
      filter_upwards [continuousAt_snd.eventually (eventually_gt_nhds hdp)] with q hqd
      simp only [radialSplice, if_neg (not_lt.mpr (hcd.le.trans hqd.le)),
        if_neg (not_lt.mpr hqd.le)]

/-- One of the two actual collars, pulled back along its fixed endpoint
coefficient projection. -/
def n04PositiveGeometry_radialCollarKernel (n : ℕ) (l r c d : ℝ)
    (η : Bool → ℝ) (side : Bool) (p : N04PositiveRadialCoefficients n × ℝ) : ℝ :=
  n04PositiveGeometry_scalarCollarKernel n (if side then d else l)
    (if side then r else c) (η side) side (p.1 side, p.2)

private theorem radialKernel_eq_splice (n : ℕ) (l r c d : ℝ) (η : Bool → ℝ) :
    n04PositiveGeometry_radialKernel n l r c d η =
      radialSplice c d (n04PositiveGeometry_radialCollarKernel n l r c d η false)
        (n04PositiveGeometry_radialCollarKernel n l r c d η true) := by
  funext p
  have hc (side : Bool) : endpointFiberCollar n l r c d η
      (n04PositiveGeometry_radialCoefficientField n l r p.1) side (p.2, 0) =
      n04PositiveGeometry_radialCollarKernel n l r c d η side p := by
    have he : n04PositiveGeometry_radialCoefficientField n l r p.1 side =
        n04PositiveGeometry_radialCoefficientField n (if side then d else l)
          (if side then r else c) (fun _ => p.1 side) side := by
      funext j θ
      cases j <;> cases side <;> rfl
    change positiveReferenceCollarCoordinate n (if side then d else l)
      (if side then r else c) (η side) (if side then d else l)
      ((if side then r else c) - (if side then d else l)) side
      (n04PositiveGeometry_radialCoefficientField n l r p.1 side) Prod.fst (p.2, 0) = _
    rw [he]
    rfl
  simp only [n04PositiveGeometry_radialKernel, endpointFiberInterpolation,
    twoEndpointFiberCoordinate, radialGermGlue, radialSplice]
  split_ifs <;> first | exact hc false | exact hc true | rfl

private theorem radialCollarKernel_exit
    (n : ℕ) (l r c d : ℝ) (η : Bool → ℝ)
    (hη : ∀ side, 0 < η side)
    (hgap : ∀ side, 2 * η side <
      (if side then r else c) - (if side then d else l)) (side : Bool) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a t, t ∈ Metric.ball (if side then d else c) ε →
      n04PositiveGeometry_radialCollarKernel n l r c d η side (a, t) = t := by
  have h := n04Realization_positiveCollar_uniform_exit n (hη side) (hgap side) side
  refine ⟨h.choose, h.choose_spec.1, ?_⟩
  intro a t ht
  have hcenter : (if side then (if side then d else l) else (if side then r else c)) =
      (if side then d else c) := by cases side <;> rfl
  apply h.choose_spec.2
    (n04PositiveGeometry_radialCoefficientField n (if side then d else l)
      (if side then r else c) (fun _ => a side) side)
  · intro j _
    cases j <;> exact contDiff_const
  · simpa only [hcenter] using ht

/-- Full finite coefficient/radial jets of the actual two-collar kernel,
with a common envelope selected before the component and evaluation point. -/
theorem n04PositiveGeometry_radialKernel_bounds
    {I : Type} {W : I → ℝ} (hW : ∀ i, 1 ≤ W i) (n : ℕ)
    (p : I → N04PositiveRadialCoefficients n × ℝ) (l r c d : I → ℝ)
    (η : I → Bool → ℝ)
    (hcd : ∀ i, c i < d i) (hη : ∀ i side, 0 < η i side)
    (hgap : ∀ i side, 2 * η i side <
      (if side then r i else c i) - (if side then d i else l i))
    (hp : HasPositiveEnvelope W (fun i => ‖p i‖))
    (hl : HasPositiveEnvelope W (fun i => |l i|))
    (hr : HasPositiveEnvelope W (fun i => |r i|))
    (hc : HasPositiveEnvelope W (fun i => |c i|))
    (hd : HasPositiveEnvelope W (fun i => |d i|))
    (hηinv : ∀ side, HasPositiveEnvelope W (fun i => |(η i side)⁻¹|))
    (hspan : ∀ side : Bool, HasPositiveEnvelope W
      (fun i => |((if side then r i else c i) - (if side then d i else l i))⁻¹|))
    (hmiddle : ∀ side, HasPositiveEnvelope W
      (fun i => |(positiveReferenceMiddleMass (if side then d i else l i)
        (if side then r i else c i) (η i side))⁻¹|)) :
    N04PositiveKernelJetBounds W p
      (fun i => n04PositiveGeometry_radialKernel n (l i) (r i) (c i) (d i) (η i)) := by
  let P := N04PositiveRadialCoefficients n
  have hcollar (side : Bool) : N04PositiveKernelJetBounds W p
      (fun i => n04PositiveGeometry_radialCollarKernel n (l i) (r i) (c i) (d i) (η i) side) := by
    let L : (P × ℝ) →L[ℝ] ((Fin (n + 1) → ℝ) × ℝ) :=
      ((ContinuousLinearMap.proj side).comp (ContinuousLinearMap.fst ℝ P ℝ)).prod
        (ContinuousLinearMap.snd ℝ P ℝ)
    have hp' : HasPositiveEnvelope W (fun i => ‖L (p i)‖) :=
      ((hasPositiveEnvelope_const W hW ‖L‖).mul hW hp (fun _ => norm_nonneg _)).mono
        (fun i => L.le_opNorm (p i))
    have h := n04PositiveGeometry_scalarCollarKernel_bounds hW n side (fun i => L (p i))
      (fun i => if side then d i else l i) (fun i => if side then r i else c i)
      (fun i => η i side) hp' (by cases side <;> assumption)
      (by cases side <;> assumption) (hηinv side) (hspan side) (hmiddle side)
    exact h.precompLinear hW L p (fun _ => rfl)
  have hid : N04PositiveKernelJetBounds W p (fun _ => Prod.snd) :=
    N04PositiveKernelJetBounds.linear hW (ContinuousLinearMap.snd ℝ P ℝ) hp
  refine ⟨fun i => n04PositiveGeometry_radialKernel_contDiff n (l i) (r i) (c i) (d i)
    (hcd i) (η i) (hη i) (hgap i), ?_⟩
  intro k
  have hsum := (((hcollar false).jets k).add hW (hid.jets k)).add hW
    ((hcollar true).jets k)
  apply hsum.mono
  intro i
  have hg := radialSplice_eventuallyEq (hcd i)
    (n04PositiveGeometry_radialCollarKernel n (l i) (r i) (c i) (d i) (η i) false)
    (n04PositiveGeometry_radialCollarKernel n (l i) (r i) (c i) (d i) (η i) true)
    (radialCollarKernel_exit n (l i) (r i) (c i) (d i) (η i) (hη i) (hgap i) false)
    (radialCollarKernel_exit n (l i) (r i) (c i) (d i) (η i) (hη i) (hgap i) true) (p i)
  rw [← radialKernel_eq_splice] at hg
  rcases hg with hg | hg | hg
  · rw [(hg.iteratedFDeriv ℝ k).eq_of_nhds]
    exact le_add_of_nonneg_right (norm_nonneg _) |>.trans
      (le_add_of_nonneg_right (norm_nonneg _))
  · rw [(hg.iteratedFDeriv ℝ k).eq_of_nhds]
    exact le_add_of_nonneg_left (norm_nonneg _) |>.trans
      (le_add_of_nonneg_right (norm_nonneg _))
  · rw [(hg.iteratedFDeriv ℝ k).eq_of_nhds]
    exact le_add_of_nonneg_left (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The kernel preserves the two physical boundary radii for every finite
coefficient vector. Only the fixed cutoff margins are used here. -/
theorem n04PositiveGeometry_radialKernel_endpoints
    (n : ℕ) {l r c d : ℝ} (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (η : Bool → ℝ) (hη : ∀ side, 0 < η side)
    (hgap : ∀ side, 2 * η side <
      (if side then r else c) - (if side then d else l))
    (a : N04PositiveRadialCoefficients n) :
    n04PositiveGeometry_radialKernel n l r c d η (a, l) = l ∧
      n04PositiveGeometry_radialKernel n l r c d η (a, r) = r := by
  rw [radialKernel_eq_splice]
  constructor
  · simp only [radialSplice, if_pos hlc, n04PositiveGeometry_radialCollarKernel,
      Bool.false_eq_true, ite_false]
    rw [n04PositiveGeometry_scalarCollarKernel_formula,
      positiveReferenceCoordinate_left, mul_zero, add_zero]
  · have hrc : ¬ r < c := not_lt.mpr (hcd.le.trans hdr.le)
    have hrd : ¬ r < d := not_lt.mpr hdr.le
    simp only [radialSplice, if_neg hrc, if_neg hrd,
      n04PositiveGeometry_radialCollarKernel, ite_true]
    rw [n04PositiveGeometry_scalarCollarKernel_formula]
    have hs (side : Bool) : ContDiff ℝ ∞
        (fun t => n04PositiveGeometry_collarSlopeKernel n d r true (a true) side t / (r - d)) := by
      apply ContDiff.div_const
      cases side with
      | false => exact contDiff_const
      | true =>
        change ContDiff ℝ ∞ (fun t => ∑ j : Fin (n + 1),
          a true j / (j.val.factorial : ℝ) * (t - r) ^ j.val)
        apply ContDiff.sum
        intro j _
        exact contDiff_const.mul ((contDiff_id.sub contDiff_const).pow j.val)
    change d + (r - d) * positiveReferenceCoordinate d r (η true)
      (fun t => n04PositiveGeometry_collarSlopeKernel n d r true (a true) false t / (r - d))
      (fun t => n04PositiveGeometry_collarSlopeKernel n d r true (a true) true t / (r - d)) r = r
    rw [positiveReferenceCoordinate_right (l := d) (r := r) (hη true)
      (show 2 * η true < r - d from hgap true)
      (fun t _ => (hs false).contDiffAt) (fun t _ => (hs true).contDiffAt), mul_one]
    ring

/-- Every inverse evaluation in the physical component has its actual
preimage in that same closed component. This is the bounded radial set
used for uniform coefficient jets. -/
theorem n04PositiveGeometry_radialKernel_inverse_mem
    (n : ℕ) {l r c d κ M : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r) (hκ : 0 < κ) (hM : 0 ≤ M)
    {a : N04PositiveRadialCoefficients n}
    (ha : a ∈ n04PositiveGeometry_radialCoefficientDomain n κ M)
    {x : ℝ} (hx : x ∈ Icc l r) :
    Function.invFun (fun t => n04PositiveGeometry_radialKernel n l r c d
      (endpointFiberWidths n l r c d κ M) (a, t)) x ∈ Icc l r := by
  let F : ℝ → ℝ := fun t => n04PositiveGeometry_radialKernel n l r c d
    (endpointFiberWidths n l r c d κ M) (a, t)
  have hgeom := n04PositiveGeometry_radialKernel_geometry n hlc hcd hdr hκ hM
  have hm : StrictMono F := strictMono_of_deriv_pos
    (fun t => hgeom.2.2.1.trans_le (hgeom.2.2.2 a ha t))
  have hsurj : Function.Surjective F :=
    (bijective_of_deriv_lower_bound hgeom.2.2.1 (hgeom.2.2.2 a ha)).2
  have he := n04PositiveGeometry_radialKernel_endpoints n hlc hcd hdr
    (endpointFiberWidths n l r c d κ M) hgeom.1 hgeom.2.1 a
  have hleft : F l = l := he.1
  have hend : F r = r := he.2
  have hright : F (Function.invFun F x) = x := Function.rightInverse_invFun hsurj x
  change Function.invFun F x ∈ Icc l r
  constructor
  · by_contra hn
    have hlt : F (Function.invFun F x) < F l := hm (lt_of_not_ge hn)
    rw [hright, hleft] at hlt
    exact (not_lt.mpr hx.1) hlt
  · by_contra hn
    have hlt : F r < F (Function.invFun F x) := hm (lt_of_not_ge hn)
    rw [hright, hend] at hlt
    exact (not_lt.mpr hx.2) hlt

end ContinuousFlexibility.Analysis
