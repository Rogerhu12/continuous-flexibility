import ContinuousFlexibility.Analysis.N07aCanonicalRoughPairing
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# True boundary inverse germs of the actual open coordinate chart

An inverse candidate is only constrained inside its open canonical strip.
Its bounded first derivatives give a Lipschitz extension for this proof.
The inverse-function theorem then identifies the true smooth inverse germ
at a boundary point. No meaning is assigned to the candidate's arbitrary
value at that boundary.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology NNReal

theorem n07a_boundary_inverse_germ
    {f g : PolarPoint → PolarPoint} {s t : Set PolarPoint} {a : PolarPoint}
    (ha : a ∈ closure s) (hmap : MapsTo f s t)
    (hgf : ∀ p ∈ s, g (f p) = p) (hfg : ∀ q ∈ t, f (g q) = q)
    (hf : ContDiffAt ℝ ∞ f a) (hdet : (fderiv ℝ f a).det ≠ 0)
    {M : ℝ≥0} (hg : LipschitzOnWith M g t) :
    ∃ G : PolarPoint → PolarPoint,
      ContDiffAt ℝ ∞ G (f a) ∧ G (f a) = a ∧
      HasFDerivAt G
        (((fderiv ℝ f a).toContinuousLinearEquivOfDetNeZero hdet).symm :
          PolarPoint →L[ℝ] PolarPoint) (f a) ∧
      ∀ᶠ q in 𝓝 (f a), q ∈ t → g q = G q := by
  obtain ⟨g₀, hg₀, hgg₀⟩ := hg.extend_finite_dimension
  have : NeBot (𝓝[s] a) := mem_closure_iff_nhdsWithin_neBot.mp ha
  have hvalue : g₀ (f a) = a := by
    have hleft : Tendsto (fun p => g₀ (f p)) (𝓝[s] a) (𝓝 (g₀ (f a))) :=
      ((hg₀.continuous.continuousAt).comp hf.continuousAt).tendsto.mono_left
        nhdsWithin_le_nhds
    have he : (fun p => g₀ (f p)) =ᶠ[𝓝[s] a] id := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (hgg₀ (hmap hp)).symm.trans (hgf p hp)
    have hright : Tendsto (fun p => g₀ (f p)) (𝓝[s] a) (𝓝 a) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).congr' he.symm
    exact tendsto_nhds_unique hleft hright
  let e : PolarPoint ≃L[ℝ] PolarPoint :=
    (fderiv ℝ f a).toContinuousLinearEquivOfDetNeZero hdet
  have hf' : HasFDerivAt f (e : PolarPoint →L[ℝ] PolarPoint) a := by
    simpa only [e, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using
      (hf.differentiableAt (by simp)).hasFDerivAt
  have hs := hf.hasStrictFDerivAt' hf' (by simp)
  let G : PolarPoint → PolarPoint := hs.localInverse f e a
  have hG : ContDiffAt ℝ ∞ G (f a) := hf.to_localInverse hf' (by simp)
  have hg₀t : Tendsto g₀ (𝓝 (f a)) (𝓝 a) := by
    have hgt : Tendsto g₀ (𝓝 (f a)) (𝓝 (g₀ (f a))) :=
      hg₀.continuous.continuousAt.tendsto
    simpa only [hvalue] using hgt
  have hnear : ∀ᶠ q in 𝓝 (f a), G (f (g₀ q)) = g₀ q :=
    hg₀t.eventually hs.eventually_left_inverse
  refine ⟨G, hG, hs.localInverse_apply_image, hs.to_localInverse.hasFDerivAt, ?_⟩
  filter_upwards [hnear] with q hq hqt
  have hqg : g q = g₀ q := hgg₀ hqt
  have hqf : f (g₀ q) = q := hqg ▸ hfg q hqt
  exact hqg.trans (by simpa only [hqf] using hq.symm)

end ContinuousFlexibility.Analysis
