module

public import ContinuousFlexibility.Analysis.SpacesPhysicalDecode
public import ContinuousFlexibility.Analysis.SpacesHeightAlgebra
public import ContinuousFlexibility.Analysis.SpacesInterpolationProducts
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Quantitative products in the physical grading

The actual mixed Leibniz formula uses one `L²` factor and the uniform
cylinder estimate on the other. Interpolation then gives a fixed-loss
one-high-factor bound in the original compatible-jet grading.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

theorem spaces_lpNorm_mul_bounded {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : AEStronglyMeasurable g μ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |g x| ≤ B) :
    lpNorm (fun x => f x * g x) 2 μ ≤ B * lpNorm f 2 μ := by
  have he : eLpNorm (fun x => f x * g x) 2 μ ≤ eLpNorm (B • f) 2 μ := by
    apply eLpNorm_mono_ae (hf.aestronglyMeasurable.mul hg)
    filter_upwards [] with x
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hB]
    exact (mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)).trans_eq (mul_comm _ _)
  have ht := ENNReal.toReal_mono (hf.const_smul B).eLpNorm_ne_top he
  simpa only [toReal_eLpNorm, lpNorm_const_smul, coe_nnnorm,
    Real.norm_eq_abs, abs_of_nonneg hB] using ht

theorem spaces_lpNorm_fun_sum_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (S : Finset ι) (f : ι → α → ℝ) (hf : ∀ i ∈ S, MemLp (f i) 2 μ) :
    lpNorm (fun x => ∑ i ∈ S, f i x) 2 μ ≤ ∑ i ∈ S, lpNorm (f i) 2 μ := by
  convert lpNorm_sum_le hf (by norm_num : 1 ≤ (2 : ℝ≥0∞)) using 1
  congr 1
  funext x
  simp only [Finset.sum_apply]

theorem spaces_lpNorm_const_mul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    lpNorm (fun x => c * f x) 2 μ = c * lpNorm f 2 μ := by
  have he : (fun x => c * f x) = c • f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [he, lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hc]

theorem spaces_physicalNorm_le_jet_sum {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T γ f) (s : ℕ) :
    physicalNorm T γ s f ≤ ∑ j : JetIndex s,
      lpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
        2 materialCylinderMeasure := by
  rw [physicalNorm, ENNReal.toReal_sum (fun j _ =>
    ENNReal.pow_ne_top (hf.2.2.2.2 _ _ _).eLpNorm_ne_top)]
  simp only [ENNReal.toReal_pow, toReal_eLpNorm]
  exact Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg (fun _ _ => lpNorm_nonneg),
    Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => lpNorm_nonneg)⟩

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

/-- All exponents have the same normalized compatible-jet grading. -/
abbrev spacesPhysicalGrading : ℕ → Seminorm ℝ (PhysicalJetProjectiveLimit hT) :=
  Analysis.gradedSeminorm (fun s => physicalJetClosedSubmodule hT s) (physicalJetBond hT)

theorem spacesPhysicalGrading_eq_levelNorm (u : PhysicalJetProjectiveLimit hT) (s : ℕ) :
    spacesPhysicalGrading hT s u = ‖u.val s‖ := by
  apply le_antisymm
  · apply (Analysis.gradedSeminorm_le_iff _ _ s u (norm_nonneg _)).mpr
    intro i hi
    exact physicalJetProjective_level_norm_mono u hi
  · exact Analysis.norm_coordinate_le_graded _ _ le_rfl u

theorem spacesPhysicalGrading_eq_physicalNorm (γ : ℝ) (u : PhysicalJetProjectiveLimit hT) (s : ℕ) :
    spacesPhysicalGrading hT s u = physicalNorm T γ s (spacesPhysicalDecoded hT γ u) := by
  rw [spacesPhysicalGrading_eq_levelNorm, spacesPhysicalDecoded_physicalNorm]

theorem spaces_decoded_jet_lpNorm_le (γ : ℝ) (u : PhysicalJetProjectiveLimit hT)
    (a b c s : ℕ) (hs : a + b + c ≤ s) :
    lpNorm (weightedPhysicalJet T γ a b c (spacesPhysicalDecoded hT γ u))
      2 materialCylinderMeasure ≤ spacesPhysicalGrading hT s u := by
  rw [spacesPhysicalGrading_eq_physicalNorm hT γ]
  exact spaces_full_jet_norm_le (spacesPhysicalDecoded_heightMember hT γ u) a b c s hs

theorem spaces_decoded_mixed_pointwise (γ : ℝ) (u : PhysicalJetProjectiveLimit hT)
    (a b s : ℕ) (hs : a + b + 2 ≤ s) (p : PolarPoint) :
    |mixedDerivative a b (materialPullback T γ (spacesPhysicalDecoded hT γ u)) p| ≤
      (4 * Real.sqrt Real.pi) * spacesPhysicalGrading hT s u := by
  obtain ⟨K, _, hbound⟩ := spaces_weighted_mixed_pointwise hT
  rw [spacesPhysicalGrading_eq_physicalNorm hT γ]
  simpa only [pow_zero, one_mul, Nat.cast_zero, zero_mul, Real.exp_zero, mul_one] using
    hbound γ _ (spacesPhysicalDecoded_heightMember hT γ u) a b 0 s (by omega) p

private theorem spaces_product_jet_one_high (γ δ : ℝ) (base loss s : ℕ) {C : ℝ}
    (hC : 0 ≤ C)
    (hpair : ∀ i j : ℕ, i + j ≤ s → ∀ u v : PhysicalJetProjectiveLimit hT,
      spacesPhysicalGrading hT (i + 2) u * spacesPhysicalGrading hT (j + 2) v ≤ C *
        (spacesPhysicalGrading hT (s + loss) u * spacesPhysicalGrading hT base v +
          spacesPhysicalGrading hT base u * spacesPhysicalGrading hT (s + loss) v))
    (a b c : ℕ) (hs : a + b + c ≤ s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u v : PhysicalJetProjectiveLimit hT,
      lpNorm (weightedPhysicalJet T (γ + δ) a b c
        (fun p => spacesPhysicalDecoded hT γ u p * spacesPhysicalDecoded hT δ v p))
        2 materialCylinderMeasure ≤ A *
          (spacesPhysicalGrading hT (s + loss) u * spacesPhysicalGrading hT base v +
            spacesPhysicalGrading hT base u * spacesPhysicalGrading hT (s + loss) v) := by
  let M : ℝ := 4 * Real.sqrt Real.pi
  have hM : 0 ≤ M := by positivity
  let coeff (j i : ℕ) : ℝ := (b.choose j : ℝ) * (a.choose i : ℝ)
  have hc (j i : ℕ) : 0 ≤ coeff j i := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  let term (j i : ℕ) (u v : PhysicalJetProjectiveLimit hT) (p : PolarPoint) : ℝ :=
    coeff j i * (weightedPhysicalJet T γ i j c (spacesPhysicalDecoded hT γ u) p *
      mixedDerivative (a - i) (b - j) (materialPullback T δ (spacesPhysicalDecoded hT δ v)) p)
  have hm (j i : ℕ) (u v : PhysicalJetProjectiveLimit hT) :
      MemLp (term j i u v) 2 materialCylinderMeasure := by
    exact (spaces_memLp_mul_bounded
      ((spacesPhysicalDecoded_heightMember hT γ u).2.2.2.2 i j c)
      (contDiff_mixedDerivative (contDiff_materialPullback hT
        (spacesPhysicalDecoded_heightMember hT δ v).1) (a - i) (b - j)).continuous.aestronglyMeasurable
      (spaces_decoded_mixed_pointwise hT δ v (a - i) (b - j) _ le_rfl)).const_mul (coeff j i)
  have hterm (j i : ℕ) (hj : j ≤ b) (hi : i ≤ a) (u v : PhysicalJetProjectiveLimit hT) :
      lpNorm (term j i u v) 2 materialCylinderMeasure ≤ (coeff j i * M * C) *
        (spacesPhysicalGrading hT (s + loss) u * spacesPhysicalGrading hT base v +
          spacesPhysicalGrading hT base u * spacesPhysicalGrading hT (s + loss) v) := by
    let g := mixedDerivative (a - i) (b - j)
      (materialPullback T δ (spacesPhysicalDecoded hT δ v))
    have hg : AEStronglyMeasurable g materialCylinderMeasure :=
      (contDiff_mixedDerivative (contDiff_materialPullback hT
        (spacesPhysicalDecoded_heightMember hT δ v).1) _ _).continuous.aestronglyMeasurable
    have hgB : ∀ p, |g p| ≤ M * spacesPhysicalGrading hT (a - i + (b - j) + 2) v :=
      spaces_decoded_mixed_pointwise hT δ v (a - i) (b - j) _ le_rfl
    have hfg := spaces_lpNorm_mul_bounded
      ((spacesPhysicalDecoded_heightMember hT γ u).2.2.2.2 i j c) hg
      (mul_nonneg hM (apply_nonneg _ _)) hgB
    have hfirst := spaces_decoded_jet_lpNorm_le hT γ u i j c (i + j + c + 2) (by omega)
    have hinterp := hpair (i + j + c) (a - i + (b - j)) (by omega) u v
    dsimp only [term]
    rw [spaces_lpNorm_const_mul _ _ (hc j i)]
    calc
      _ ≤ coeff j i * ((M * spacesPhysicalGrading hT (a - i + (b - j) + 2) v) *
          spacesPhysicalGrading hT (i + j + c + 2) u) :=
        mul_le_mul_of_nonneg_left
          (hfg.trans (mul_le_mul_of_nonneg_left hfirst
            (mul_nonneg hM (apply_nonneg _ _)))) (hc j i)
      _ = (coeff j i * M) * (spacesPhysicalGrading hT (i + j + c + 2) u *
          spacesPhysicalGrading hT (a - i + (b - j) + 2) v) := by ring
      _ ≤ (coeff j i * M) * (C *
          (spacesPhysicalGrading hT (s + loss) u * spacesPhysicalGrading hT base v +
            spacesPhysicalGrading hT base u * spacesPhysicalGrading hT (s + loss) v)) :=
        mul_le_mul_of_nonneg_left hinterp (mul_nonneg (hc j i) hM)
      _ = _ := by ring
  let A : ℝ := ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1), coeff j i * M * C
  refine ⟨A, Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (hc j i) hM) hC)), fun u v => ?_⟩
  rw [spaces_weightedPhysicalJet_mul hT
    (spacesPhysicalDecoded_heightMember hT γ u) (spacesPhysicalDecoded_heightMember hT δ v)]
  change lpNorm (fun p => ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1), term j i u v p)
    2 materialCylinderMeasure ≤ _
  apply (spaces_lpNorm_fun_sum_le _ _ (fun j _ => memLp_finsetSum _ (fun i _ => hm j i u v))).trans
  simp only [A, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  apply (spaces_lpNorm_fun_sum_le _ _ (fun i _ => hm j i u v)).trans
  apply Finset.sum_le_sum
  intro i hi
  exact hterm j i (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) u v

theorem spaces_physical_product_one_high (hI : HasInterpolation (spacesPhysicalGrading hT))
    (γ δ : ℝ) : ∃ base loss : ℕ, ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : PhysicalJetProjectiveLimit hT,
        physicalNorm T (γ + δ) s
          (fun p => spacesPhysicalDecoded hT γ u p * spacesPhysicalDecoded hT δ v p) ≤ C *
            (spacesPhysicalGrading hT (s + loss) u * spacesPhysicalGrading hT base v +
              spacesPhysicalGrading hT base u * spacesPhysicalGrading hT (s + loss) v) := by
  obtain ⟨base, loss, hpair⟩ := Analysis.spaces_interpolation_pair_uniform_bound
    (spacesPhysicalGrading hT) (fun u _ _ h => Analysis.gradedSeminorm_monotone _ _ h u) hI
  refine ⟨base, loss, fun s => ?_⟩
  obtain ⟨C, hC, hb⟩ := hpair s
  have hjet (j : JetIndex s) := spaces_product_jet_one_high hT γ δ base loss s hC hb
    (j.val 0).val (j.val 1).val (j.val 2).val j.property
  choose A hA hAb using hjet
  refine ⟨∑ j, A j, Finset.sum_nonneg (fun j _ => hA j), fun u v => ?_⟩
  apply (spaces_physicalNorm_le_jet_sum
    (spaces_heightMember_mul hT (spacesPhysicalDecoded_heightMember hT γ u)
      (spacesPhysicalDecoded_heightMember hT δ v)) s).trans
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun j _ => hAb j u v)

end ContinuousFlexibility.Statements
