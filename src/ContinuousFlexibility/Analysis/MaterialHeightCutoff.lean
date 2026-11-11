import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Localization of actual weighted heights

Multiplication by a smooth radial cutoff is performed in the material
coordinate.  The actual mixed derivatives satisfy the ordinary finite
Leibniz formula, so every weighted L² jet remains integrable.  A compact
cutoff can be chosen to equal one on any closed interior component.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

/-- A radial multiplier in the actual material coordinate. -/
def materialCutoffHeight (T : MaterialData) (χ : ℝ → ℝ)
    (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  χ (T.rho p.1) * f p

theorem materialPullback_cutoff {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (γ : ℝ) (χ : ℝ → ℝ) (f : PolarPoint → ℝ) :
    materialPullback T γ (materialCutoffHeight T χ f) =
      fun p => χ p.1 * materialPullback T γ f p := by
  obtain ⟨_, _, _, _, _, _, _, hInv, _⟩ := hT
  funext p
  simp only [materialPullback, materialCutoffHeight, (hInv p.1).2]
  ring

/-- The full mixed jet of a radial multiplier uses exactly the radial
Leibniz sum; angular differentiation does not touch the multiplier. -/
theorem mixedDerivative_radial_mul {χ : ℝ → ℝ} {f : PolarPoint → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => χ q.1 * f q) p =
      ∑ i ∈ Finset.range (a + 1),
        (a.choose i : ℝ) * iteratedDeriv i χ p.1 * mixedDerivative (a - i) b f p := by
  have hg : ContDiff ℝ ∞ (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2) := by
    have h := (contDiff_mixedDerivative hf 0 b).comp
      (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => p.2)))
    simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero, id_eq] using h
  have hangle (r : ℝ) :
      iteratedDeriv b (fun θ => χ r * f (r, θ)) p.2 =
        χ r * iteratedDeriv b (fun θ => f (r, θ)) p.2 :=
    iteratedDeriv_const_mul_field (χ r) (fun θ => f (r, θ))
  unfold mixedDerivative
  simp only [hangle]
  simpa only [Pi.mul_apply] using
    iteratedDeriv_mul (hχ.contDiffAt.of_le (by simp : (a : ℕ∞ω) ≤ (∞ : ℕ∞ω)))
      (hg.contDiffAt.of_le (by simp : (a : ℕ∞ω) ≤ (∞ : ℕ∞ω)))

theorem weightedPhysicalJet_cutoff {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {χ : ℝ → ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (a b c : ℕ) (p : PolarPoint) :
    weightedPhysicalJet T γ a b c (materialCutoffHeight T χ f) p =
      ∑ i ∈ Finset.range (a + 1),
        (a.choose i : ℝ) * iteratedDeriv i χ p.1 *
          weightedPhysicalJet T γ (a - i) b c f p := by
  unfold weightedPhysicalJet
  rw [materialPullback_cutoff hT, mixedDerivative_radial_mul hχ
    (contDiff_materialPullback hT hf), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem materialCutoffHeight_member_of_bounded_jets
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {χ : ℝ → ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : HeightMember D T γ f)
    (hχ : ContDiff ℝ ∞ χ)
    (hbound : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |iteratedDeriv n χ x| ≤ K) :
    HeightMember D T γ (materialCutoffHeight T χ f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hρ : ContDiffOn ℝ ∞ (fun p : PolarPoint => T.rho p.1) (annularOpen D) :=
      (hT.1 T.rho (by simp)).comp contDiffOn_fst (fun p hp => hp.1)
    exact (hχ.comp_contDiffOn hρ).mul hf.1
  · intro r θ
    simp only [materialCutoffHeight, hf.2.1 r θ]
  · intro p
    simpa only [materialCutoffHeight, Prod.fst_add, add_zero] using
      congrArg (fun t => χ (T.rho p.1) * t) (hf.2.2.1 p)
  · intro p hp
    simp only [materialCutoffHeight, hf.2.2.2.1 p hp, mul_zero]
  · intro a b c
    have hterm (i : ℕ) :
        MemLp (fun p : PolarPoint => (a.choose i : ℝ) * iteratedDeriv i χ p.1 *
          weightedPhysicalJet T γ (a - i) b c f p) 2 materialCylinderMeasure := by
      obtain ⟨K, hK, hKi⟩ := hbound i
      have hχi : ContDiff ℝ ∞ (iteratedDeriv i χ) := by
        rw [iteratedDeriv_eq_iterate]
        exact ContDiff.iterate_deriv i hχ
      have hj := hf.2.2.2.2 (a - i) b c
      have hprod : MemLp (fun p : PolarPoint =>
          iteratedDeriv i χ p.1 * weightedPhysicalJet T γ (a - i) b c f p)
          2 materialCylinderMeasure := by
        apply (hj.const_mul K).of_le
          ((hχi.continuous.comp continuous_fst).aestronglyMeasurable.mul hj.aestronglyMeasurable)
        exact Filter.Eventually.of_forall fun p => by
          simp only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hK]
          exact mul_le_mul_of_nonneg_right (hKi p.1) (abs_nonneg _)
      simpa only [mul_assoc] using hprod.const_mul (a.choose i : ℝ)
    have hsum := memLp_finsetSum (Finset.range (a + 1)) (fun i _ => hterm i)
    apply hsum.ae_eq
    exact Filter.Eventually.of_forall fun p =>
      (weightedPhysicalJet_cutoff hT hχ hf.1 a b c p).symm

theorem compactCutoff_iteratedDeriv_bounded {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hsupp : HasCompactSupport χ) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |iteratedDeriv n χ x| ≤ K := by
  have hs : HasCompactSupport (iteratedDeriv n χ) := by
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hsupp
    | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hc : ContDiff ℝ ∞ (iteratedDeriv n χ) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv n hχ
  obtain ⟨K, hK⟩ := hs.exists_bound_of_continuous hc.continuous
  refine ⟨max K 0, le_max_right _ _, fun x => ?_⟩
  have hx : |iteratedDeriv n χ x| ≤ K := by
    simpa only [Real.norm_eq_abs] using hK x
  exact hx.trans (le_max_left _ _)

theorem materialCutoffHeight_member
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {χ : ℝ → ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : HeightMember D T γ f)
    (hχ : ContDiff ℝ ∞ χ) (hsupp : HasCompactSupport χ) :
    HeightMember D T γ (materialCutoffHeight T χ f) :=
  materialCutoffHeight_member_of_bounded_jets hT hf hχ
    (compactCutoff_iteratedDeriv_bounded hχ hsupp)

theorem materialCutoffHeight_compactRadialSupport
    {D : ReferenceData} {T : MaterialData} {χ : ℝ → ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hsupp : HasCompactSupport χ)
    (hf : ∀ p, p ∉ annularOpen D → f p = 0) :
    HasCompactRadialSupport D (materialCutoffHeight T χ f) := by
  obtain ⟨_, _, _, _, _, _, hradius, hInv, hback, _⟩ := hT
  refine ⟨T.radius '' tsupport χ, hsupp.image hradius.continuous, ?_, ?_⟩
  · rintro r ⟨x, hx, rfl⟩
    exact (hInv x).1
  · intro r hr θ
    by_cases hcore : r ∈ Ioo D.a D.b
    · have hz : χ (T.rho r) = 0 := by
        by_contra hn
        exact hr ⟨T.rho r, subset_closure hn, hback r hcore⟩
      simp only [materialCutoffHeight, hz, zero_mul]
    · have hp : (r, θ) ∉ annularOpen D := fun hp => hcore hp.1
      simp only [materialCutoffHeight, hf (r, θ) hp, mul_zero]

/-- A concrete material-coordinate bump equals one on any prescribed
closed interval in the annular interior. -/
theorem exists_materialCutoff_one_on_Icc
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {l r : ℝ} (hl : D.a < l) (hlr : l ≤ r) (hr : r < D.b) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      ∀ t ∈ Icc l r, χ (T.rho t) = 1 := by
  let R : ℝ := |T.rho l| + |T.rho r| + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  let χ : ContDiffBump (0 : ℝ) :=
    ⟨R, R + 1, hR, by linarith⟩
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, ?_⟩
  intro t ht
  have hlt : l ∈ Ioo D.a D.b := ⟨hl, hlr.trans_lt hr⟩
  have hrt : r ∈ Ioo D.a D.b := ⟨hl.trans_le hlr, hr⟩
  have htt : t ∈ Ioo D.a D.b := ⟨hl.trans_le ht.1, ht.2.trans_lt hr⟩
  have hlow : T.rho l ≤ T.rho t := hT.2.2.2.1.monotoneOn hlt htt ht.1
  have hupp : T.rho t ≤ T.rho r := hT.2.2.2.1.monotoneOn htt hrt ht.2
  apply χ.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  change |T.rho t| ≤ R
  rw [abs_le]
  constructor <;> dsimp only [R] <;>
    linarith [neg_abs_le (T.rho l), le_abs_self (T.rho r),
      abs_nonneg (T.rho l), abs_nonneg (T.rho r)]

/-- The given Sobolev decoder realizes localization inside the same
physical space, with genuine compact radial support. -/
theorem exists_physical_height_localization
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : SobolevModelData}
    (hT : IsMaterialData D T) (hH : IsSobolevModel D T γ H)
    {l r : ℝ} (hl : D.a < l) (hlr : l ≤ r) (hr : r < D.b) (u : H.Space) :
    ∃ v : H.Space, HasCompactRadialSupport D (H.decode v) ∧
      ∀ t ∈ Icc l r, ∀ θ, H.decode v (t, θ) = H.decode u (t, θ) := by
  obtain ⟨χ, hχ, hsupp, hone⟩ := exists_materialCutoff_one_on_Icc hT hl hlr hr
  have hu := hH.2.2.2.1 u
  obtain ⟨v, hv⟩ := hH.2.2.2.2.1 (materialCutoffHeight T χ (H.decode u))
    (materialCutoffHeight_member hT hu hχ hsupp)
  refine ⟨v, ?_, ?_⟩
  · rw [hv]
    exact materialCutoffHeight_compactRadialSupport hT hsupp hu.2.2.2.1
  · intro t ht θ
    rw [hv]
    simp only [materialCutoffHeight, hone t ht, one_mul]

end ContinuousFlexibility.Statements
