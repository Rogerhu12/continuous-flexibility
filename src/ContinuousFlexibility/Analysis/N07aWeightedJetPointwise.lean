import ContinuousFlexibility.Analysis.N07aMaterialPowerJets
import ContinuousFlexibility.Analysis.N07aCanonicalWeakJets
import ContinuousFlexibility.Scalar.WeightedRadialMultiplier

/-!
# Point evaluation of the actual material-weighted jets

The material weight is differentiated before applying the cylinder Sobolev
inequality. Its derivatives retain the same power of M, so the pointwise
estimate costs exactly two additional orders, independently of the jet.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements
open scoped BigOperators ContDiff ENNReal

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ}

theorem n07a_weightedPhysicalJet_mixed_norm
    (hT : IsMaterialData D T) (a b c i j s : ℕ)
    (horder : a + b + c + i + j ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      MemLp (mixedDerivative i j (weightedPhysicalJet T γ a b c f))
        2 materialCylinderMeasure ∧
      (eLpNorm (mixedDerivative i j (weightedPhysicalJet T γ a b c f))
        2 materialCylinderMeasure).toReal ≤ C * physicalNorm T γ s f := by
  classical
  let g : ℝ → ℝ := fun x => T.M (T.radius x) ^ c
  have hg : ContDiff ℝ ∞ g := by
    simpa only [Real.rpow_natCast] using n07a_materialM_rpow_contDiff hT (c : ℝ)
  choose B hB hBx using fun k : Fin (i + 1) =>
    n07a_iteratedDeriv_materialM_pow_bound hT c k.val
  let A : Fin (i + 1) → ℝ := fun k => (i.choose k.val : ℝ) * B k
  have hA (k : Fin (i + 1)) : 0 ≤ A k :=
    mul_nonneg (Nat.cast_nonneg _) (hB k)
  let coefficient : Fin (i + 1) → PolarPoint → ℝ := fun k p =>
    (i.choose k.val : ℝ) * iteratedDeriv k.val g p.1
  have hc (k : Fin (i + 1)) :
      AEStronglyMeasurable (coefficient k) materialCylinderMeasure := by
    have hd : Continuous (fun p : PolarPoint => iteratedDeriv k.val g p.1) := by
      simpa only [Function.comp_def] using
        (ContDiff.continuous_iteratedDeriv k.val hg (by simp)).comp continuous_fst
    exact (hd.const_mul _).aestronglyMeasurable
  have hcb (k : Fin (i + 1)) (p : PolarPoint) :
      |coefficient k p| ≤ A k * T.M (T.radius p.1) ^ c := by
    dsimp only [coefficient, A]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (i.choose k.val))]
    exact (mul_le_mul_of_nonneg_left (hBx k p.1) (Nat.cast_nonneg _)).trans_eq
      (by ring)
  refine ⟨∑ k, A k, Finset.sum_nonneg (fun k _ => hA k), ?_⟩
  intro f hf
  let F : PolarPoint → ℝ := materialPullback T γ f
  have hF : ContDiff ℝ ∞ F := contDiff_materialPullback hT hf.1
  let term : Fin (i + 1) → PolarPoint → ℝ := fun k p =>
    coefficient k p * weightedPhysicalJet T γ (i - k.val + a) (j + b) 0 f p
  have ht (k : Fin (i + 1)) := weightedPhysicalJet_mul_coefficient_bound hT hf
    (i - k.val + a) (j + b) 0 c s (by omega) (hA k) (hc k) (hcb k)
  have heq : mixedDerivative i j (weightedPhysicalJet T γ a b c f) =
      ∑ k : Fin (i + 1), term k := by
    funext p
    change mixedDerivative i j (fun q => g q.1 * mixedDerivative a b F q) p = _
    rw [mixedDerivative_radial_mul hg (contDiff_mixedDerivative hF a b),
      Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [n07a_mixedDerivative_mixedDerivative hF]
    simp only [term, coefficient, weightedPhysicalJet, pow_zero, one_mul, F]
  rw [heq]
  refine ⟨memLp_finsetSum' Finset.univ (fun k _ => (ht k).1), ?_⟩
  have hfinite : (∑ k, eLpNorm (term k) 2 materialCylinderMeasure) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun k _ => (ht k).1.eLpNorm_ne_top)
  have htri := ENNReal.toReal_mono hfinite
    (eLpNorm_sum_le (f := term) (s := Finset.univ) (p := 2) (μ := materialCylinderMeasure)
      (by norm_num))
  rw [ENNReal.toReal_sum (fun k _ => (ht k).1.eLpNorm_ne_top)] at htri
  apply htri.trans
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun k _ => (ht k).2)

theorem n07a_weightedPhysicalJet_pointwise
    (hT : IsMaterialData D T) (a b c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      ∀ p, |weightedPhysicalJet T γ a b c f p| ≤
        C * physicalNorm T γ (a + b + c + 2) f := by
  obtain ⟨A₀, hA₀, hb₀⟩ := n07a_weightedPhysicalJet_mixed_norm (γ := γ)
    hT a b c 0 0 (a + b + c + 2) (by omega)
  obtain ⟨A₁, hA₁, hb₁⟩ := n07a_weightedPhysicalJet_mixed_norm (γ := γ)
    hT a b c 1 0 (a + b + c + 2) (by omega)
  obtain ⟨A₂, hA₂, hb₂⟩ := n07a_weightedPhysicalJet_mixed_norm (γ := γ)
    hT a b c 0 1 (a + b + c + 2) (by omega)
  obtain ⟨A₃, hA₃, hb₃⟩ := n07a_weightedPhysicalJet_mixed_norm (γ := γ)
    hT a b c 1 1 (a + b + c + 2) (by omega)
  refine ⟨Real.sqrt Real.pi * (A₀ + A₁ + A₂ + A₃),
    mul_nonneg (Real.sqrt_nonneg _) (by positivity), fun f hf p => ?_⟩
  let g : PolarPoint → ℝ := weightedPhysicalJet T γ a b c f
  have hF := contDiff_materialPullback (γ := γ) hT hf.1
  have hM : ContDiff ℝ ∞ (fun x => T.M (T.radius x) ^ c) := by
    simpa only [Real.rpow_natCast] using n07a_materialM_rpow_contDiff hT (c : ℝ)
  have hg : ContDiff ℝ ∞ g :=
    (hM.comp contDiff_fst).mul (contDiff_mixedDerivative hF a b)
  have hp : ∀ r : ℝ, Function.Periodic (fun θ => g (r, θ)) Real.pi := by
    intro r θ
    change T.M (T.radius r) ^ c *
      mixedDerivative a b (materialPullback T γ f) (r, θ + Real.pi) = _
    exact congrArg (fun v : ℝ => T.M (T.radius r) ^ c * v)
      (mixedDerivative_angular_periodic
        (materialPullback_angular_periodic (T := T) (γ := γ) hf.2.2.1) a b r θ)
  have he₀ : mixedDerivative 0 0 g = g := spaces_mixedDerivative_zero g
  have he₁ : mixedDerivative 1 0 g = radialPartial g := by
    simpa only [Nat.zero_add, spaces_mixedDerivative_zero] using
      (radialPartial_mixedDerivative hg 0 0).symm
  have he₂ : mixedDerivative 0 1 g = angularPartial g := by
    simpa only [Nat.zero_add, spaces_mixedDerivative_zero] using
      (angularPartial_mixedDerivative hg 0 0).symm
  have he₃ : mixedDerivative 1 1 g = radialPartial (angularPartial g) := by
    rw [← he₂]
    simpa only [Nat.zero_add] using (radialPartial_mixedDerivative hg 0 1).symm
  have h₀ := hb₀ f hf
  have h₁ := hb₁ f hf
  have h₂ := hb₂ f hf
  have h₃ := hb₃ f hf
  change MemLp (mixedDerivative 0 0 g) 2 _ ∧ _ at h₀
  change MemLp (mixedDerivative 1 0 g) 2 _ ∧ _ at h₁
  change MemLp (mixedDerivative 0 1 g) 2 _ ∧ _ at h₂
  change MemLp (mixedDerivative 1 1 g) 2 _ ∧ _ at h₃
  rw [he₀] at h₀
  rw [he₁] at h₁
  rw [he₂] at h₂
  rw [he₃] at h₃
  apply (abs_le_materialCylinder_L2 hg hp h₀.1 h₁.1 h₂.1 h₃.1 p.1 p.2).trans
  calc
    _ ≤ Real.sqrt Real.pi *
        (A₀ * physicalNorm T γ (a + b + c + 2) f +
          A₁ * physicalNorm T γ (a + b + c + 2) f +
          A₂ * physicalNorm T γ (a + b + c + 2) f +
          A₃ * physicalNorm T γ (a + b + c + 2) f) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (add_le_add h₀.2 h₁.2) h₂.2) h₃.2)
        (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem n07a_materialPullback_decode_weighted_pointwise
    {A : SobolevModelData} (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (a b c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : A.Space) (p : PolarPoint),
      |mixedDerivative a b (materialPullback T γ (A.decode u)) p| ≤
        C * (T.M (T.radius p.1) ^ c)⁻¹ * A.grading (a + b + c + 2) u := by
  obtain ⟨C, hC, hCb⟩ := n07a_weightedPhysicalJet_pointwise (γ := γ) hT a b c
  refine ⟨C, hC, fun u p => ?_⟩
  have hM : 0 < T.M (T.radius p.1) :=
    zero_lt_one.trans_le (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 p.1).1).2.2.2
  have hpow : 0 < T.M (T.radius p.1) ^ c := pow_pos hM c
  have hbound := (hCb (A.decode u) (hA.2.2.2.1 u) p).trans
    (mul_le_mul_of_nonneg_left
      (physicalNorm_decode_le_grading hA u (a + b + c + 2)) hC)
  simp only [weightedPhysicalJet, abs_mul, abs_of_pos hpow] at hbound
  have h := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hpow.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hpow.ne', one_mul,
    mul_comm (T.M (T.radius p.1) ^ c)⁻¹ C] using h

end ContinuousFlexibility.Analysis
