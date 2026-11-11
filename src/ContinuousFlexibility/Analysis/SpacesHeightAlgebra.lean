import ContinuousFlexibility.Analysis.SpacesHeightBounds
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Products of actual weighted heights

The normalization at exponent `γ + δ` turns multiplication into ordinary
multiplication on the material cylinder. The mixed Leibniz formula places
the weight on an integrable factor and uses the cylinder Sobolev bound on
the other factor. This proves membership in the exact target space for
every pair of exponents.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

theorem spaces_mixedDerivative_mul {f g : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f q * g q) p =
      ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        (b.choose j : ℝ) * (a.choose i : ℝ) *
          mixedDerivative i j f p * mixedDerivative (a - i) (b - j) g p := by
  have hfr (j : ℕ) : ContDiff ℝ ∞
      (fun r => iteratedDeriv j (fun θ => f (r, θ)) p.2) := by
    convert (contDiff_mixedDerivative hf 0 j).comp
      (contDiff_id.prodMk (contDiff_const (c := p.2))) using 1
    funext r
    simp only [Function.comp_apply, id_eq, mixedDerivative, iteratedDeriv_zero]
  have hgr (j : ℕ) : ContDiff ℝ ∞
      (fun r => iteratedDeriv j (fun θ => g (r, θ)) p.2) := by
    convert (contDiff_mixedDerivative hg 0 j).comp
      (contDiff_id.prodMk (contDiff_const (c := p.2))) using 1
    funext r
    simp only [Function.comp_apply, id_eq, mixedDerivative, iteratedDeriv_zero]
  have he : (fun r => iteratedDeriv b (fun θ => f (r, θ) * g (r, θ)) p.2) =
      fun r => ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) *
        (iteratedDeriv j (fun θ => f (r, θ)) p.2 *
          iteratedDeriv (b - j) (fun θ => g (r, θ)) p.2) := by
    funext r
    have hft : ContDiff ℝ ∞ (fun θ => f (r, θ)) :=
      hf.comp (contDiff_const.prodMk contDiff_id)
    have hgt : ContDiff ℝ ∞ (fun θ => g (r, θ)) :=
      hg.comp (contDiff_const.prodMk contDiff_id)
    simpa only [mul_assoc] using iteratedDeriv_fun_mul
      ((hft.of_le (by simp)).contDiffAt) ((hgt.of_le (by simp)).contDiffAt)
  unfold mixedDerivative
  rw [he, iteratedDeriv_fun_sum (fun j _ =>
    ((contDiff_const.mul ((hfr j).mul (hgr (b - j)))).of_le (by simp)).contDiffAt)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul ((hfr j).of_le (by simp)).contDiffAt
      ((hgr (b - j)).of_le (by simp)).contDiffAt, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem spaces_materialPullback_mul {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (γ δ : ℝ) (f g : PolarPoint → ℝ) :
    materialPullback T (γ + δ) (fun p => f p * g p) =
      fun p => materialPullback T γ f p * materialPullback T δ g p := by
  have hrange := hT.2.2.2.2.2.2.2.1
  funext p
  have hH : 0 < T.H (T.radius p.1) := (hT.2.1 _ (hrange p.1).1).2.1
  simp only [materialPullback, neg_add_rev, Real.rpow_add hH]
  ring

theorem spaces_memLp_mul_bounded {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} {p : ℝ≥0∞} (hf : MemLp f p μ)
    (hg : AEStronglyMeasurable g μ) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    MemLp (fun x => f x * g x) p μ := by
  apply hf.of_le_mul (c := B) (hf.aestronglyMeasurable.mul hg)
  filter_upwards [] with x
  simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)).trans_eq (mul_comm _ _)

/-- Multiplication preserves every mixed weighted integrability condition. -/
theorem spaces_heightMember_mul {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {γ δ : ℝ} {f g : PolarPoint → ℝ}
    (hf : HeightMember D T γ f) (hg : HeightMember D T δ g) :
    HeightMember D T (γ + δ) (fun p => f p * g p) := by
  refine ⟨hf.1.mul hg.1, ?_, ?_, ?_, ?_⟩
  · intro r θ
    dsimp only
    rw [hf.2.1, hg.2.1]
  · intro p
    dsimp only
    rw [hf.2.2.1 p, hg.2.2.1 p]
  · intro p hp
    dsimp only
    rw [hf.2.2.2.1 p hp, zero_mul]
  · intro a b c
    have hfs := contDiff_materialPullback (γ := γ) hT hf.1
    have hgs := contDiff_materialPullback (γ := δ) hT hg.1
    have he : weightedPhysicalJet T (γ + δ) a b c (fun p => f p * g p) =
        fun p => ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
          ((b.choose j : ℝ) * (a.choose i : ℝ)) *
            (weightedPhysicalJet T γ i j c f p *
              mixedDerivative (a - i) (b - j) (materialPullback T δ g) p) := by
      funext p
      rw [weightedPhysicalJet, spaces_materialPullback_mul hT,
        spaces_mixedDerivative_mul hfs hgs, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [weightedPhysicalJet]
      ring
    rw [he]
    apply memLp_finsetSum
    intro j hj
    apply memLp_finsetSum
    intro i hi
    obtain ⟨B, hB, hbound⟩ :=
      heightMember_materialPullback_mixedDerivative_uniform_bound hT hg (a - i) (b - j)
    exact (spaces_memLp_mul_bounded (hf.2.2.2.2 i j c)
      (contDiff_mixedDerivative hgs (a - i) (b - j)).continuous.aestronglyMeasurable
      hbound).const_mul ((b.choose j : ℝ) * (a.choose i : ℝ))

/-- The exact model surjectivity now supplies a height representing the
pointwise product, without altering the concrete function space. -/
theorem spaces_exists_height_product {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {γ δ : ℝ} {H K L : SobolevModelData}
    (hH : IsSobolevModel D T γ H) (hK : IsSobolevModel D T δ K)
    (hL : IsSobolevModel D T (γ + δ) L) (u : H.Space) (v : K.Space) :
    ∃ w : L.Space, ∀ p, L.decode w p = H.decode u p * K.decode v p := by
  obtain ⟨w, hw⟩ := hL.2.2.2.2.1 _
    (spaces_heightMember_mul hT (hH.2.2.2.1 u) (hK.2.2.2.1 v))
  exact ⟨w, fun p => congrFun hw p⟩

end ContinuousFlexibility.Statements
