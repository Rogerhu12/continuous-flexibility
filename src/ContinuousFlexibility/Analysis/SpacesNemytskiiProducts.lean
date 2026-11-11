import ContinuousFlexibility.Analysis.SpacesHeightProductBounds

/-!
# Finite products of normalized physical jets

One factor carries the physical weight and its L² norm. The remaining
factors use point evaluation. The interpolation product inequality gives
one high factor with a loss independent of the number of factors.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

def spacesNormalizedJet (a b c : ℕ) (u : PhysicalJetProjectiveLimit hT) (p : PolarPoint) : ℝ :=
  T.M (T.radius p.1) ^ c * mixedDerivative a b (spacesPhysicalRepresentative hT u) p

theorem spacesNormalizedJet_eq_weighted (a b c : ℕ) (u : PhysicalJetProjectiveLimit hT) :
    spacesNormalizedJet hT a b c u = weightedPhysicalJet T 0 a b c (spacesPhysicalDecoded hT 0 u) := by
  unfold weightedPhysicalJet
  rw [spacesPhysicalDecoded_pullback]
  rfl

theorem spacesNormalizedJet_memLp (a b c : ℕ) (u : PhysicalJetProjectiveLimit hT) :
    MemLp (spacesNormalizedJet hT a b c u) 2 materialCylinderMeasure := by
  rw [spacesNormalizedJet_eq_weighted]
  exact (spacesPhysicalDecoded_heightMember hT 0 u).2.2.2.2 a b c

theorem spacesNormalizedJet_lpNorm_le (a b c s : ℕ) (hs : a + b + c ≤ s)
    (u : PhysicalJetProjectiveLimit hT) :
    lpNorm (spacesNormalizedJet hT a b c u) 2 materialCylinderMeasure ≤ spacesPhysicalGrading hT s u := by
  rw [spacesNormalizedJet_eq_weighted]
  exact spaces_decoded_jet_lpNorm_le hT 0 u a b c s hs

theorem spacesNormalizedMixed_pointwise (a b : ℕ) (u : PhysicalJetProjectiveLimit hT) (p : PolarPoint) :
    |mixedDerivative a b (spacesPhysicalRepresentative hT u) p| ≤
      (4 * Real.sqrt Real.pi) * spacesPhysicalGrading hT (a + b + 2) u := by
  have h := spaces_decoded_mixed_pointwise hT 0 u a b (a + b + 2) le_rfl p
  rw [spacesPhysicalDecoded_pullback] at h
  exact h

def spacesWeightedJetProduct {ι : Type*} [Fintype ι] (a b : ι → ℕ) (c : ℕ)
    (u : ι → PhysicalJetProjectiveLimit hT) (p : PolarPoint) : ℝ :=
  T.M (T.radius p.1) ^ c * ∏ i, mixedDerivative (a i) (b i) (spacesPhysicalRepresentative hT (u i)) p

theorem spacesWeightedJetProduct_prebound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (c : ℕ) (i : ι) (u : ι → PhysicalJetProjectiveLimit hT) :
    MemLp (spacesWeightedJetProduct hT a b c u) 2 materialCylinderMeasure ∧
      lpNorm (spacesWeightedJetProduct hT a b c u) 2 materialCylinderMeasure ≤
        (1 + 4 * Real.sqrt Real.pi) ^ Fintype.card ι *
          ∏ j, spacesPhysicalGrading hT (a j + b j + (if j = i then c else 0) + 2) (u j) := by
  let K := 1 + 4 * Real.sqrt Real.pi
  have hK : 1 ≤ K := by
    have h : 0 ≤ 4 * Real.sqrt Real.pi := by positivity
    dsimp only [K]
    linarith
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  let J (j : ι) : PolarPoint → ℝ :=
    mixedDerivative (a j) (b j) (spacesPhysicalRepresentative hT (u j))
  let B (j : ι) := K * spacesPhysicalGrading hT (a j + b j + (if j = i then c else 0) + 2) (u j)
  have hB (j : ι) : 0 ≤ B j := mul_nonneg hK0 (apply_nonneg _ _)
  have hJ (j : ι) : Continuous (J j) :=
    (contDiff_mixedDerivative (spacesPhysicalRepresentative_contDiff hT (u j)) (a j) (b j)).continuous
  let g (p : PolarPoint) := ∏ j ∈ Finset.univ.erase i, J j p
  have hg : Continuous g := continuous_finsetProd _ (fun j _ => hJ j)
  have hgb (p : PolarPoint) : |g p| ≤ ∏ j ∈ Finset.univ.erase i, B j := by
    calc
      |g p| = ‖∏ j ∈ Finset.univ.erase i, J j p‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∏ j ∈ Finset.univ.erase i, ‖J j p‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ j ∈ Finset.univ.erase i, B j := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        have hb := spacesNormalizedMixed_pointwise hT (a j) (b j) (u j) p
        calc
          ‖J j p‖ ≤ (4 * Real.sqrt Real.pi) * spacesPhysicalGrading hT (a j + b j + 2) (u j) := hb
          _ ≤ K * spacesPhysicalGrading hT (a j + b j + 2) (u j) :=
            mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) (apply_nonneg _ _)
          _ = B j := by simp only [B, ite_eq_right hji, add_zero]
  have hf := spacesNormalizedJet_memLp hT (a i) (b i) c (u i)
  have hnonneg : 0 ≤ ∏ j ∈ Finset.univ.erase i, B j := Finset.prod_nonneg (fun j _ => hB j)
  have he : spacesWeightedJetProduct hT a b c u = fun p => spacesNormalizedJet hT (a i) (b i) c (u i) p * g p := by
    funext p
    rw [spacesWeightedJetProduct, ← Finset.mul_prod_erase Finset.univ (fun j => J j p) (Finset.mem_univ i)]
    exact (mul_assoc _ _ _).symm
  rw [he]
  refine ⟨spaces_memLp_mul_bounded hf hg.aestronglyMeasurable hgb, ?_⟩
  calc
    lpNorm (fun p => spacesNormalizedJet hT (a i) (b i) c (u i) p * g p) 2 materialCylinderMeasure ≤
        (∏ j ∈ Finset.univ.erase i, B j) * lpNorm (spacesNormalizedJet hT (a i) (b i) c (u i)) 2 materialCylinderMeasure :=
      spaces_lpNorm_mul_bounded hf hg.aestronglyMeasurable hnonneg hgb
    _ ≤ (∏ j ∈ Finset.univ.erase i, B j) * B i := by
      apply mul_le_mul_of_nonneg_left _ hnonneg
      calc
        _ ≤ spacesPhysicalGrading hT (a i + b i + c + 2) (u i) :=
          spacesNormalizedJet_lpNorm_le hT (a i) (b i) c _ (by omega) (u i)
        _ ≤ K * spacesPhysicalGrading hT (a i + b i + c + 2) (u i) :=
          le_mul_of_one_le_left (apply_nonneg _ _) hK
        _ = B i := by simp only [B, ite_true]
    _ = ∏ j, B j := by rw [mul_comm, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    _ = _ := by simp only [B, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, K]

/-- The fixed base and loss work for every finite number of jet factors. -/
theorem spaces_weighted_jet_product_one_high
    (hI : HasInterpolation (spacesPhysicalGrading hT)) :
    ∃ base loss : ℕ, ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι],
      ∀ (a b : ι → ℕ) (c s : ℕ), (∑ i, (a i + b i)) + c ≤ s →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ι → PhysicalJetProjectiveLimit hT,
          MemLp (spacesWeightedJetProduct hT a b c u) 2 materialCylinderMeasure ∧
          lpNorm (spacesWeightedJetProduct hT a b c u) 2 materialCylinderMeasure ≤
            C * ∑ i, spacesPhysicalGrading hT (s + loss) (u i) *
              ∏ j ∈ Finset.univ.erase i, spacesPhysicalGrading hT base (u j) := by
  obtain ⟨base, loss, hprod⟩ := spaces_interpolation_product_bound (spacesPhysicalGrading hT)
    (fun u i j hij => gradedSeminorm_monotone _ _ hij u) hI
  refine ⟨base, loss, ?_⟩
  intro ι _ _ _ a b c s hs
  let i : ι := Classical.choice inferInstance
  let order (j : ι) := a j + b j + if j = i then c else 0
  have horder : (∑ j, order j) ≤ s := by
    simpa only [order, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hs
  obtain ⟨C, hC, hbound⟩ := hprod order s horder
  let K := (1 + 4 * Real.sqrt Real.pi) ^ Fintype.card ι
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K * C, mul_nonneg hK hC, fun u => ?_⟩
  have hpre := spacesWeightedJetProduct_prebound hT a b c i u
  refine ⟨hpre.1, hpre.2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left (hbound u) hK).trans_eq (mul_assoc K C _).symm

end ContinuousFlexibility.Statements
