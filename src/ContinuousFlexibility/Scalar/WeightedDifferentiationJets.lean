module

public import ContinuousFlexibility.Scalar.WeightedDifferentiationSupport
public import ContinuousFlexibility.Scalar.WeightedRadialMultiplier
public import ContinuousFlexibility.Scalar.WeightedFieldRegularity
public import ContinuousFlexibility.Scalar.WeightedDecodeLift

/-!
# Fixed-loss jet bounds for the actual radial derivative

The inverse material scale costs one envelope power. Differentiating the
input material pullback costs one derivative. The logarithmic-weight term
collects its complete coefficient before using the same envelope bound.
Thus the actual ordinary radial derivative has one fixed loss of two.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

theorem MaterialSubpower.const_mul {T : MaterialData} {g : ℝ → ℝ}
    (hg : MaterialSubpower T g) (c : ℝ) :
    MaterialSubpower T (fun x => c * g x) := by
  refine ⟨contDiff_const.mul hg.1, fun n ε hε => ?_⟩
  obtain ⟨K, hK, hKb⟩ := hg.2 n ε hε
  refine ⟨|c| * K, mul_nonneg (abs_nonneg c) hK, fun x => ?_⟩
  rw [iteratedDeriv_const_mul_field, abs_mul]
  exact (mul_le_mul_of_nonneg_left (hKb x) (abs_nonneg c)).trans_eq (by ring)

/-- The radial multiplier estimate with one actual material radial
derivative on the input. Its additional cost is exactly one jet order. -/
theorem weightedRadialMultiplier_radialPartial_jet_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {g : ℝ → ℝ}
    (hT : IsMaterialData D T) (hg : ContDiff ℝ ∞ g) (r : ℕ)
    (hgb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv j g x| ≤ C * T.M (T.radius x) ^ r)
    (a b c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      MemLp (fun p => T.M (T.radius p.1) ^ c *
        mixedDerivative a b (fun q => g q.1 * radialPartial (materialPullback T γ f) q) p)
        2 materialCylinderMeasure ∧
      (eLpNorm (fun p => T.M (T.radius p.1) ^ c *
        mixedDerivative a b (fun q => g q.1 * radialPartial (materialPullback T γ f) q) p)
        2 materialCylinderMeasure).toReal ≤ C * physicalNorm T γ (a + b + c + r + 1) f := by
  classical
  choose B hB hBx using fun i : Fin (a + 1) => hgb i.val
  let C : Fin (a + 1) → ℝ := fun i => (a.choose i.val : ℝ) * B i
  have hC (i : Fin (a + 1)) : 0 ≤ C i := mul_nonneg (Nat.cast_nonneg _) (hB i)
  let coefficient : Fin (a + 1) → PolarPoint → ℝ := fun i p =>
    (a.choose i.val : ℝ) * iteratedDeriv i.val g p.1
  have hc (i : Fin (a + 1)) : AEStronglyMeasurable (coefficient i) materialCylinderMeasure := by
    have hd : ContDiff ℝ ∞ (iteratedDeriv i.val g) := by
      rw [iteratedDeriv_eq_iterate]
      exact hg.iterate_deriv i.val
    exact ((hd.continuous.comp continuous_fst).const_mul _).aestronglyMeasurable
  have hcb (i : Fin (a + 1)) (p : PolarPoint) :
      |coefficient i p| ≤ C i * T.M (T.radius p.1) ^ r := by
    dsimp only [coefficient, C]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (a.choose i.val))]
    exact (mul_le_mul_of_nonneg_left (hBx i p.1) (Nat.cast_nonneg _)).trans_eq (by ring)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun f hf => ?_⟩
  have hG := contDiff_materialPullback (γ := γ) hT hf.1
  have hGr : ContDiff ℝ ∞ (radialPartial (materialPullback T γ f)) :=
    contDiffOn_univ.mp (scalar_contDiffOn_radialPartial isOpen_univ hG.contDiffOn)
  let term : Fin (a + 1) → PolarPoint → ℝ := fun i p =>
    coefficient i p * weightedPhysicalJet T γ (a - i.val + 1) b c f p
  have ht (i : Fin (a + 1)) := weightedPhysicalJet_mul_coefficient_bound hT hf
    (a - i.val + 1) b c r (a + b + c + r + 1) (by omega) (hC i) (hc i) (hcb i)
  have heq : (fun p => T.M (T.radius p.1) ^ c *
      mixedDerivative a b (fun q => g q.1 * radialPartial (materialPullback T γ f) q) p) =
      ∑ i : Fin (a + 1), term i := by
    funext p
    rw [mixedDerivative_radial_mul hg hGr, Finset.mul_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [mixedDerivative_radialPartial isOpen_univ hG.contDiffOn
      (a - i.val) b (mem_univ p)]
    dsimp only [term, coefficient, weightedPhysicalJet]
    ring
  rw [heq]
  refine ⟨memLp_finsetSum' Finset.univ (fun i _ => (ht i).1), ?_⟩
  have hfinite : (∑ i, eLpNorm (term i) 2 materialCylinderMeasure) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => (ht i).1.eLpNorm_ne_top)
  have htri := ENNReal.toReal_mono hfinite
    (eLpNorm_sum_le (f := term) (s := Finset.univ) (p := 2) (μ := materialCylinderMeasure)
      (by norm_num))
  rw [ENNReal.toReal_sum (fun i _ => (ht i).1.eLpNorm_ne_top)] at htri
  apply htri.trans
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => (ht i).2)

/-- A single fixed loss controls every weighted jet of the actual
ordinary radial partial, uniformly before the input field is chosen. -/
theorem weightedPhysicalJet_radialPartial_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    (hT : IsMaterialData D T) (a b c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      MemLp (weightedPhysicalJet T γ a b c (radialPartial f)) 2 materialCylinderMeasure ∧
      (eLpNorm (weightedPhysicalJet T γ a b c (radialPartial f))
        2 materialCylinderMeasure).toReal ≤ C * physicalNorm T γ (a + b + c + 2) f := by
  let g : ℝ → ℝ := fun x => (T.ell (T.radius x))⁻¹
  let k : ℝ → ℝ := fun x => γ *
    ((T.ell (T.radius x))⁻¹ * deriv (fun t => Real.log (T.H (T.radius t))) x)
  have hg : MaterialSubpower T g := materialEll_inv_subpower hT
  have hk : MaterialSubpower T k :=
    (MaterialSubpower.mul hT hg (materialLogH_deriv_subpower hT)).const_mul γ
  have hgb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv j g x| ≤ C * T.M (T.radius x) ^ (1 : ℕ) := by
    intro j
    simpa only [pow_one] using hg.le_materialM j
  have hkb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv j k x| ≤ C * T.M (T.radius x) ^ (1 : ℕ) := by
    intro j
    simpa only [pow_one] using hk.le_materialM j
  obtain ⟨C, hC, hCf⟩ :=
    weightedRadialMultiplier_radialPartial_jet_bound (γ := γ) hT hg.1 1 hgb a b c
  obtain ⟨K, hK, hKf⟩ := weightedRadialMultiplier_jet_bound (γ := γ) hT hk.1 1 hkb a b c
  refine ⟨C + K, add_nonneg hC hK, fun f hf => ?_⟩
  have hG := contDiff_materialPullback (γ := γ) hT hf.1
  have hGr : ContDiff ℝ ∞ (radialPartial (materialPullback T γ f)) :=
    contDiffOn_univ.mp (scalar_contDiffOn_radialPartial isOpen_univ hG.contDiffOn)
  have hfirst : ContDiff ℝ ∞ (fun q : PolarPoint =>
      g q.1 * radialPartial (materialPullback T γ f) q) :=
    (hg.1.comp contDiff_fst).mul hGr
  have hsecond : ContDiff ℝ ∞ (fun q : PolarPoint => k q.1 * materialPullback T γ f q) :=
    (hk.1.comp contDiff_fst).mul hG
  have hformula : materialPullback T γ (radialPartial f) =
      fun p => g p.1 * radialPartial (materialPullback T γ f) p +
        k p.1 * materialPullback T γ f p := by
    funext p
    rw [materialPullback_radialPartial hT hf.1]
    dsimp only [g, k]
    ring
  let A : PolarPoint → ℝ := fun p => T.M (T.radius p.1) ^ c *
    mixedDerivative a b (fun q => g q.1 * radialPartial (materialPullback T γ f) q) p
  let B : PolarPoint → ℝ := fun p => T.M (T.radius p.1) ^ c *
    mixedDerivative a b (fun q => k q.1 * materialPullback T γ f q) p
  have heq : weightedPhysicalJet T γ a b c (radialPartial f) = A + B := by
    funext p
    simp only [weightedPhysicalJet, hformula,
      mixedDerivative_add_of_contDiff hfirst hsecond, Pi.add_apply, A, B, mul_add]
  have hAmem : MemLp A 2 materialCylinderMeasure := (hCf f hf).1
  have hBmem : MemLp B 2 materialCylinderMeasure := (hKf f hf).1
  have hAbound : (eLpNorm A 2 materialCylinderMeasure).toReal ≤
      C * physicalNorm T γ (a + b + c + 2) f := by
    simpa only [Nat.add_assoc] using (hCf f hf).2
  have hBbound : (eLpNorm B 2 materialCylinderMeasure).toReal ≤
      K * physicalNorm T γ (a + b + c + 2) f :=
    (hKf f hf).2.trans (mul_le_mul_of_nonneg_left
      (physicalNorm_monotone_of_heightMember hf (by omega)) hK)
  rw [heq]
  refine ⟨hAmem.add hBmem, ?_⟩
  have hfinite : eLpNorm A 2 materialCylinderMeasure + eLpNorm B 2 materialCylinderMeasure ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hAmem.eLpNorm_ne_top, hBmem.eLpNorm_ne_top⟩
  have htri := ENNReal.toReal_mono hfinite
    (eLpNorm_add_le (f := A) (g := B) (p := 2) (μ := materialCylinderMeasure) (by norm_num))
  rw [ENNReal.toReal_add hAmem.eLpNorm_ne_top hBmem.eLpNorm_ne_top] at htri
  exact htri.trans ((add_le_add hAbound hBbound).trans_eq (by ring))

theorem heightMember_radialPartial
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : HeightMember D T γ f) :
    HeightMember D T γ (radialPartial f) := by
  apply heightMember_radialPartial_of_weightedJets hf
  intro a b c
  obtain ⟨_, _, hbound⟩ := weightedPhysicalJet_radialPartial_bound (γ := γ) hT a b c
  exact (hbound f hf).1

end ContinuousFlexibility.Statements
