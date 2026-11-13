import ContinuousFlexibility.Analysis.N01cMixedPowerBounds
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine
import ContinuousFlexibility.Analysis.MixedDerivativeLocality

/-!
# Affine transport of actual mixed power bounds

An inclusion preserving the grading transports every supplied tower by
uniqueness. The physical domain may be restricted at the same time; its
material weights and distributed spatial exponent remain unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04NegativeGeometry_mixedPower_affine_domain
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {base loss : ℕ} {U : Set E} {V : Set F}
    {Ω Ω₀ : Set PolarPoint} {H W : PolarPoint → ℝ}
    {f : F → PolarPoint → ℝ} {g : E → PolarPoint → ℝ}
    (I : E →L[ℝ] F) (center : F)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hΩ₀ : Ω ⊆ Ω₀)
    (hmap : MapsTo (fun x => center + I x) U V)
    (hgrade : ∀ n x, q n (I x) = p n x)
    (RF : MixedJetRegularity V Ω₀ f)
    (hf : MixedPowerBounds q center base loss V Ω₀ H W f)
    (heq : ∀ x ∈ U, EqOn (g x) (f (center + I x)) Ω) :
    ∃ RG : MixedJetRegularity U Ω g,
      MixedPowerBounds p 0 base loss U Ω H W g := by
  have hspatial (x : E) (hx : x ∈ U) : ContDiffOn ℝ ∞ (g x) Ω :=
    ((RF.spatial (center + I x) (hmap hx)).mono hΩ₀).congr (heq x hx)
  have hjet (a b : ℕ) (y : PolarPoint) (hy : y ∈ Ω) (x : E) (hx : x ∈ U) :
      mixedDerivative a b (g x) y =
        mixedDerivative a b (f (center + I x)) y :=
    mixedDerivative_congr_on_open hΩ (heq x hx) a b hy
  let RG : MixedJetRegularity U Ω g := {
    spatial := hspatial
    parameter := fun a b y hy =>
      ((RF.parameter a b y (hΩ₀ hy)).compAffine I center hU hmap).congr
        (fun x hx => (hjet a b y hy x hx).symm) }
  refine ⟨RG, ?_⟩
  intro K s
  obtain ⟨C, A, hC, hA, hb⟩ := hf K s
  refine ⟨C, A, hC, hA, ?_⟩
  intro k hk a b hab y hy J x hx hlow v hv R hR hhigh hvhigh
  let JF : SmoothDirections V (fun z => mixedDerivative a b (f z) y) :=
    RF.parameter a b y (hΩ₀ hy)
  have he : J.D k x v = JF.D k (center + I x) (fun j => I (v j)) := by
    apply (congrArg (fun A : E [×k]→L[ℝ] ℝ => A v)
      (J.unique (RG.parameter a b y hy) k x hx)).trans
    change (JF.compAffine I center hU hmap).D k x v = _
    exact JF.compAffine_apply I center hU hmap k x v
  have hstate (n : ℕ) : q n ((center + I x) - center) = p n (x - 0) := by
    rw [add_sub_cancel_left, hgrade, sub_zero]
  have hb' := hb k hk a b hab y (hΩ₀ hy) JF (center + I x) (hmap hx)
    ((hstate base).trans_le hlow) (fun j => I (v j))
    (fun j => (hgrade base (v j)).trans_le (hv j)) R hR
    ((hstate (s + loss)).trans_le hhigh)
    (fun j => (hgrade (s + loss) (v j)).trans_le (hvhigh j))
  exact (congrArg norm he).trans_le hb'

end ContinuousFlexibility.Analysis
