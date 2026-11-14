module

public import ContinuousFlexibility.Analysis.WeightedCutFirstJets
public import ContinuousFlexibility.Analysis.CanonicalClosedInverseJets
public import ContinuousFlexibility.Blueprint.CanonicalParts

/-!
# First-jet matching on the actual canonical cut

The closed inverse contract makes the derivatives in the transmission law
ordinary derivatives of the true inverse. The constant and centered affine
physical tests then fix the height and radial inverse column. The common
cut curve fixes the angular column. The actual inverse derivative equations
convert these identities to the full forward derivative matching rule.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The value and radial transmission laws force the complete first-jet
matching across the true current cut, including the physical heights. -/
theorem canonicalCut_height_and_firstJets
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (θ : ℝ) :
    let q : PolarPoint := (K.cutRadius m, θ)
    let x := canonicalCutPoint S K z m θ
    K.height z (K.cutPair m).2 x = K.height z (K.cutPair m).1 x ∧
      fderiv ℝ (K.inverseChart z (K.cutPair m).2) q (1, 0) =
        -fderiv ℝ (K.inverseChart z (K.cutPair m).1) q (1, 0) ∧
      fderiv ℝ (K.inverseChart z (K.cutPair m).2) q (0, 1) =
        fderiv ℝ (K.inverseChart z (K.cutPair m).1) q (0, 1) ∧
      ∀ v : PolarPoint, fderiv ℝ (K.chart z (K.cutPair m).2) x v =
        (-(fderiv ℝ (K.chart z (K.cutPair m).1) x v).1,
          (fderiv ℝ (K.chart z (K.cutPair m).1) x v).2) := by
  let q : PolarPoint := (K.cutRadius m, θ)
  let k (i : ℕ) : PolarPoint → ℝ :=
    fun y => 1 / K.height z i (K.inverseChart z i y)
  obtain ⟨_, _, _, _, _, hρ, hleft₀, hleft₁, hright₀, hright₁⟩ := hB.1.1 m
  have hq (i : ℕ) (hl : K.left i = 0) (hr : K.right i = K.cutRadius m) :
      q ∈ canonicalClosed S K i := by
    change (K.left i ≤ K.cutRadius m ∧ K.cutRadius m ≤ K.right i) ∧ True
    exact ⟨⟨by simpa only [hl] using hρ.le, by rw [hr]⟩, trivial⟩
  have hregular (i : ℕ) (hi : q ∈ canonicalClosed S K i) :
      DifferentiableAt ℝ (K.inverseChart z i) q ∧
        DifferentiableAt ℝ (k i) q ∧ k i q ≠ 0 := by
    have hx := (hA.boundary z hz hs i).2.1 hi
    have hG := n04b_inverseChart_contDiffAt_closed hA hz hs i hi
    have hh := (hA.boundary z hz hs i).2.2.2.2.1 _ hx
    have hcomp : ContDiffAt ℝ ∞
        (fun y => K.height z i (K.inverseChart z i y)) q := hh.2.1.comp q hG
    have hk : ContDiffAt ℝ ∞ (k i) q :=
      contDiffAt_const.div hcomp hh.2.2.2.ne'
    exact ⟨hG.differentiableAt (by simp), hk.differentiableAt (by simp),
      div_ne_zero one_ne_zero hh.2.2.2.ne'⟩
  have hq₀ := hq (K.cutPair m).1 hleft₀ hright₀
  have hq₁ := hq (K.cutPair m).2 hleft₁ hright₁
  have hreg₀ := hregular (K.cutPair m).1 hq₀
  have hreg₁ := hregular (K.cutPair m).2 hq₁
  have hboundary (η : ℝ) :
      K.inverseChart z (K.cutPair m).2 (K.cutRadius m, η) =
        K.inverseChart z (K.cutPair m).1 (K.cutRadius m, η) :=
    (hB.1.2 z hz hs m).1 η
  have hpoint : K.inverseChart z (K.cutPair m).2 q =
      K.inverseChart z (K.cutPair m).1 q := hboundary θ
  have hheight (i : ℕ) (u : PolarPoint → ℝ) :
      canonicalHeight S K z i u = fun y => k i y * u (K.inverseChart z i y) := by
    funext y
    simp only [canonicalHeight, k, div_eq_mul_inv, one_mul, mul_comm]
  have hcut (u : PolarPoint → ℝ) (hu : ContDiff ℝ ∞ u) :
      k (K.cutPair m).2 q * u (K.inverseChart z (K.cutPair m).2 q) =
          k (K.cutPair m).1 q * u (K.inverseChart z (K.cutPair m).1 q) ∧
        radialPartial (fun y => k (K.cutPair m).2 y *
            u (K.inverseChart z (K.cutPair m).2 y)) q =
          -radialPartial (fun y => k (K.cutPair m).1 y *
            u (K.inverseChart z (K.cutPair m).1 y)) q -
              (k (K.cutPair m).1 q * u (K.inverseChart z (K.cutPair m).1 q)) /
                (2 * K.cutRadius m) := by
    have he := hB.2.1 z hz hs u hu m θ
    rw [hheight (K.cutPair m).1 u, hheight (K.cutPair m).2 u] at he
    exact he
  have hjets := inverse_radialJet_of_weighted_cutLaw
    hreg₀.1 hreg₁.1 hreg₀.2.1 hreg₁.2.1 hpoint hreg₀.2.2 hcut
  have hangular := inverse_angularJet_of_boundary_eq hreg₀.1 hreg₁.1 hboundary
  refine ⟨?_, hjets.2, hangular, ?_⟩
  · simpa only [k, one_div, inv_inj, hpoint, canonicalCutPoint] using hjets.1
  · intro v
    have hleft := (canonicalClosed_inverse_fderiv hA hz hs (K.cutPair m).1 hq₀).1
    have hright := (canonicalClosed_inverse_fderiv hA hz hs (K.cutPair m).2 hq₁).2
    rw [hpoint] at hright
    exact planeInverse_reflected_columns hleft hright hjets.2 hangular v

end ContinuousFlexibility.Analysis
