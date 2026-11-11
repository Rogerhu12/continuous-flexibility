import ContinuousFlexibility.Scalar.WeightedPhysicalMultiplier

/-!
# Uniform constants for families of actual radial multipliers

The finite Leibniz constants are selected before the family index. The
same is true when the jet estimates are assembled into a physical norm,
and when that norm is read in an actual Sobolev realization.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped BigOperators ContDiff ENNReal

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ}

theorem n08_weightedRadialMultiplier_family_jet_bound
    (hT : IsMaterialData D T) (g : I → ℝ → ℝ)
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (loss : ℕ)
    (hgb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x,
      |iteratedDeriv j (g i) x| ≤ C * T.M (T.radius x) ^ loss)
    (a b c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      MemLp
        (fun p => T.M (T.radius p.1) ^ c *
          mixedDerivative a b (fun q => g i q.1 * materialPullback T γ f q) p)
        2 materialCylinderMeasure ∧
      (eLpNorm
        (fun p => T.M (T.radius p.1) ^ c *
          mixedDerivative a b (fun q => g i q.1 * materialPullback T γ f q) p)
        2 materialCylinderMeasure).toReal ≤ C * physicalNorm T γ (a + b + c + loss) f := by
  classical
  choose B hB hBx using fun j : Fin (a + 1) => hgb j.val
  let C : Fin (a + 1) → ℝ := fun j => (a.choose j.val : ℝ) * B j
  have hC (j : Fin (a + 1)) : 0 ≤ C j := mul_nonneg (Nat.cast_nonneg _) (hB j)
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), fun i f hf => ?_⟩
  let coefficient : Fin (a + 1) → PolarPoint → ℝ := fun j p =>
    (a.choose j.val : ℝ) * iteratedDeriv j.val (g i) p.1
  have hc (j : Fin (a + 1)) : AEStronglyMeasurable (coefficient j) materialCylinderMeasure := by
    have hd : Continuous (fun p : PolarPoint => iteratedDeriv j.val (g i) p.1) := by
      simpa only [Function.comp_def] using
        (ContDiff.continuous_iteratedDeriv j.val (hg i) (by simp)).comp continuous_fst
    exact (hd.const_mul _).aestronglyMeasurable
  have hcb (j : Fin (a + 1)) (p : PolarPoint) :
      |coefficient j p| ≤ C j * T.M (T.radius p.1) ^ loss := by
    dsimp only [coefficient, C]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (a.choose j.val))]
    exact (mul_le_mul_of_nonneg_left (hBx j i p.1) (Nat.cast_nonneg _)).trans_eq (by ring)
  let term : Fin (a + 1) → PolarPoint → ℝ := fun j p =>
    coefficient j p * weightedPhysicalJet T γ (a - j.val) b c f p
  have ht (j : Fin (a + 1)) := weightedPhysicalJet_mul_coefficient_bound hT hf
    (a - j.val) b c loss (a + b + c + loss) (by omega) (hC j) (hc j) (hcb j)
  have heq :
      (fun p => T.M (T.radius p.1) ^ c *
        mixedDerivative a b (fun q => g i q.1 * materialPullback T γ f q) p) =
        ∑ j : Fin (a + 1), term j := by
    funext p
    rw [mixedDerivative_radial_mul (hg i) (contDiff_materialPullback hT hf.1),
      Finset.mul_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [term, coefficient, weightedPhysicalJet]
    ring
  rw [heq]
  refine ⟨memLp_finsetSum' Finset.univ (fun j _ => (ht j).1), ?_⟩
  have hfinite : (∑ j, eLpNorm (term j) 2 materialCylinderMeasure) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun j _ => (ht j).1.eLpNorm_ne_top)
  have htri := ENNReal.toReal_mono hfinite
    (eLpNorm_sum_le (f := term) (s := Finset.univ) (p := 2) (μ := materialCylinderMeasure)
      (by norm_num))
  rw [ENNReal.toReal_sum (fun j _ => (ht j).1.eLpNorm_ne_top)] at htri
  apply htri.trans
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun j _ => (ht j).2)

theorem n08_physicalNorm_family_bound_of_operator_jets
    {δ : ℝ} {loss : ℕ} {op : I → (PolarPoint → ℝ) → PolarPoint → ℝ}
    (hjets : ∀ a b c : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
        MemLp (weightedPhysicalJet T δ a b c (op i f)) 2 materialCylinderMeasure ∧
        (eLpNorm (weightedPhysicalJet T δ a b c (op i f)) 2 materialCylinderMeasure).toReal ≤
          C * physicalNorm T γ (a + b + c + loss) f)
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      physicalNorm T δ s (op i f) ≤ C * physicalNorm T γ (s + loss) f := by
  classical
  choose B hB hBx using fun j : JetIndex s =>
    hjets (j.val 0).val (j.val 1).val (j.val 2).val
  let K : ℝ := ∑ j, B j
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => hB j)
  have hBK (j : JetIndex s) : B j ≤ K :=
    Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ j)
  refine ⟨Real.sqrt (Fintype.card (JetIndex s) : ℝ) * K,
    mul_nonneg (Real.sqrt_nonneg _) hK, fun i f hf => ?_⟩
  have hN : 0 ≤ physicalNorm T γ (s + loss) f := Real.sqrt_nonneg _
  have hmem (a b c : ℕ) (_ : a + b + c ≤ s) :
      MemLp (weightedPhysicalJet T δ a b c (op i f)) 2 materialCylinderMeasure := by
    obtain ⟨_, _, hb⟩ := hjets a b c
    exact (hb i f hf).1
  have hbound (a b c : ℕ) (horder : a + b + c ≤ s) :
      (eLpNorm (weightedPhysicalJet T δ a b c (op i f)) 2 materialCylinderMeasure).toReal ≤
        K * physicalNorm T γ (s + loss) f := by
    let j : JetIndex s :=
      ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by simpa using horder⟩
    have hj : (eLpNorm (weightedPhysicalJet T δ a b c (op i f))
        2 materialCylinderMeasure).toReal ≤ B j * physicalNorm T γ (a + b + c + loss) f := by
      simpa [j] using (hBx j i f hf).2
    exact hj.trans ((mul_le_mul_of_nonneg_left
      (physicalNorm_monotone_of_heightMember hf (by omega)) (hB j)).trans
        (mul_le_mul_of_nonneg_right (hBK j) hN))
  exact (physicalNorm_le_of_weightedJet_bounds (mul_nonneg hK hN) hmem hbound).trans_eq (by ring)

theorem n08_physicalNorm_radialMultiplier_family_bound
    (hT : IsMaterialData D T) (k : I → ℝ → ℝ)
    (hk : ∀ i, ContDiff ℝ ∞ (fun x => k i (T.radius x))) (loss : ℕ)
    (hkb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x,
      |iteratedDeriv j (fun t => k i (T.radius t)) x| ≤ C * T.M (T.radius x) ^ loss)
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      physicalNorm T γ s (fun p => k i p.1 * f p) ≤
        C * physicalNorm T γ (s + loss) f := by
  apply n08_physicalNorm_family_bound_of_operator_jets (loss := loss) ?_ s
  intro a b c
  obtain ⟨C, hC, hCb⟩ := n08_weightedRadialMultiplier_family_jet_bound (γ := γ)
    hT (fun i x => k i (T.radius x)) hk loss hkb a b c
  refine ⟨C, hC, fun i f hf => ?_⟩
  simpa only [weightedPhysicalJet, materialPullback_radialMultiplier T γ (k i) f] using
    hCb i f hf

/-- The norm estimate applies to any actual realization of the multiplier;
its constants are independent of the realization and family index. -/
theorem n08_radialMultiplier_family_grading_bound
    {A : SobolevModelData} (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (k : I → ℝ → ℝ) (F : I → A.Space →L[ℝ] A.Space)
    (hdecode : ∀ i u p, A.decode (F i u) p = k i p.1 * A.decode u p)
    (hk : ∀ i, ContDiff ℝ ∞ (fun x => k i (T.radius x))) (loss : ℕ)
    (hkb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x,
      |iteratedDeriv j (fun t => k i (T.radius t)) x| ≤ C * T.M (T.radius x) ^ loss)
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i u, A.grading s (F i u) ≤ C * A.grading (s + loss) u := by
  obtain ⟨C, hC, hCb⟩ := n08_physicalNorm_radialMultiplier_family_bound (γ := γ)
    hT k hk loss hkb s
  refine ⟨C, hC, fun i u => ?_⟩
  have heq : A.decode (F i u) = fun p => k i p.1 * A.decode u p := funext (hdecode i u)
  rw [sobolevGrading_eq_physicalNorm hA, sobolevGrading_eq_physicalNorm hA, heq]
  exact hCb i (A.decode u) (hA.2.2.2.1 u)

end ContinuousFlexibility.Statements
