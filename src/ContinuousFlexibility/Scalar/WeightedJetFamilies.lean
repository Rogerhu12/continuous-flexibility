module

public import ContinuousFlexibility.Scalar.WeightedMonomialL2

/-!
# Fixed-loss bounds for actual material jet families

The argument uses only the genuine weighted L² and pointwise estimates of
the jet family. In particular it applies to the normalized derivatives of
the decoded field, as well as derivatives of its normalized pullback.
All constants from individual spatial orders are absorbed after the common
interpolation base and loss have been fixed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

/-- A family of actual material jets with the standard zero-loss L² bound
and the fixed two-order cylinder point-evaluation bound. -/
structure MaterialJetFamily (T : MaterialData) (A : SobolevModelData) where
  jet : ℕ → ℕ → A.Space → PolarPoint → ℝ
  continuous : ∀ a b u, Continuous (jet a b u)
  pointwise : ∀ a b, ∃ C : ℝ, 0 ≤ C ∧ ∀ u p,
    |jet a b u p| ≤ C * A.grading (a + b + 2) u
  weightedL2 : ∀ a b c, ∃ C : ℝ, 0 ≤ C ∧ ∀ u,
    MemLp (fun p => T.M (T.radius p.1) ^ c * jet a b u p) 2 materialCylinderMeasure ∧
    (eLpNorm (fun p => T.M (T.radius p.1) ^ c * jet a b u p)
      2 materialCylinderMeasure).toReal ≤ C * A.grading (a + b + c) u

def materialFamilyMonomial {T : MaterialData} {A : SobolevModelData}
    (J : MaterialJetFamily T A) {k : ℕ} (coefficient : PolarPoint → ℝ)
    (a b : Fin (k + 1) → ℕ) (c : ℕ) (u : Fin (k + 1) → A.Space) : PolarPoint → ℝ :=
  fun p => coefficient p * T.M (T.radius p.1) ^ c *
    ∏ i, J.jet (a i) (b i) (u i) p

/-- One factor carries the weight and the L² norm; the other finitely many
factors need only their pointwise bounds. -/
theorem materialWeightedProduct_memLp_and_norm_le
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {k : ℕ} (f : Fin (k + 1) → PolarPoint → ℝ) (c : ℕ)
    (N : Fin (k + 1) → ℝ) (hN : ∀ i, 0 ≤ N i)
    (hf : ∀ i, Continuous (f i)) (hfbound : ∀ i p, |f i p| ≤ N i)
    {coefficient : PolarPoint → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hc : AEStronglyMeasurable coefficient materialCylinderMeasure)
    (hcBound : ∀ p, |coefficient p| ≤ K * T.M (T.radius p.1))
    (hF : MemLp (fun p => T.M (T.radius p.1) ^ (c + 1) * f 0 p)
      2 materialCylinderMeasure) :
    MemLp (fun p => coefficient p * T.M (T.radius p.1) ^ c * ∏ i, f i p)
      2 materialCylinderMeasure ∧
    (eLpNorm (fun p => coefficient p * T.M (T.radius p.1) ^ c * ∏ i, f i p)
      2 materialCylinderMeasure).toReal ≤
      (K * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), N i) *
        (eLpNorm (fun p => T.M (T.radius p.1) ^ (c + 1) * f 0 p)
          2 materialCylinderMeasure).toReal := by
  classical
  let W : PolarPoint → ℝ := fun p => T.M (T.radius p.1)
  let F : PolarPoint → ℝ := fun p => W p ^ (c + 1) * f 0 p
  let B : ℝ := K * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), N i
  have hB : 0 ≤ B := mul_nonneg hK (Finset.prod_nonneg (fun i _ => hN i))
  have hW : Continuous W := by
    obtain ⟨hsmooth, _, _, _, _, _, hrad, hInv, _⟩ := hT
    exact (hsmooth T.M (by simp)).continuousOn.comp_continuous
      (hrad.continuous.comp continuous_fst) (fun p => (hInv p.1).1)
  have hW0 (p : PolarPoint) : 0 ≤ W p := by
    obtain ⟨_, hpos, _, _, _, _, _, hInv, _⟩ := hT
    exact zero_le_one.trans (hpos (T.radius p.1) (hInv p.1).1).2.2.2
  have hg : AEStronglyMeasurable
      (fun p => coefficient p * W p ^ c * ∏ i, f i p) materialCylinderMeasure :=
    (hc.mul (hW.pow c).aestronglyMeasurable).mul
      (continuous_finsetProd Finset.univ (fun i _ => hf i)).aestronglyMeasurable
  have hpoint (p : PolarPoint) :
      ‖coefficient p * W p ^ c * ∏ i, f i p‖ ≤ B * ‖F p‖ := by
    have htail : (∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), |f i p|) ≤
        ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), N i :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hfbound i p)
    simp only [Real.norm_eq_abs, F]
    rw [abs_mul, abs_mul, Finset.abs_prod, abs_of_nonneg (pow_nonneg (hW0 p) c),
      abs_mul, abs_of_nonneg (pow_nonneg (hW0 p) (c + 1))]
    calc
      |coefficient p| * W p ^ c * (∏ i, |f i p|) ≤
          (K * W p) * W p ^ c * (∏ i, |f i p|) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hcBound p) (pow_nonneg (hW0 p) c))
          (Finset.prod_nonneg (fun i _ => abs_nonneg _))
      _ = (K * W p ^ (c + 1)) *
          (|f 0 p| * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), |f i p|) := by
        rw [pow_succ, Finset.mul_prod_erase Finset.univ
          (fun i => |f i p|) (Finset.mem_univ (0 : Fin (k + 1)))]
        ring
      _ ≤ (K * W p ^ (c + 1)) *
          (|f 0 p| * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), N i) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left htail (abs_nonneg _))
          (mul_nonneg hK (pow_nonneg (hW0 p) (c + 1)))
      _ = B * (W p ^ (c + 1) * |f 0 p|) := by dsimp [B]; ring
  have hae : ∀ᵐ p ∂materialCylinderMeasure,
      ‖coefficient p * W p ^ c * ∏ i, f i p‖ ≤ B * ‖F p‖ :=
    Eventually.of_forall hpoint
  refine ⟨hF.of_le_mul hg hae, ?_⟩
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hg hae 2
  have hfinite : ENNReal.ofReal B * eLpNorm F 2 materialCylinderMeasure ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.eLpNorm_lt_top).ne
  have hr := ENNReal.toReal_mono hfinite he
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB] at hr
  exact hr

private theorem family_input_product_le
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) {k : ℕ}
    (a b d : Fin (k + 1) → ℕ) (c : ℕ)
    {K Q₀ : ℝ} (Q : Fin (k + 1) → ℝ)
    (hK : 0 ≤ K) (hQ₀ : 0 ≤ Q₀) (hQ : ∀ i, 0 ≤ Q i)
    (hd0 : a 0 + b 0 + (c + 1) ≤ d 0 + 2)
    (hdi : ∀ i, a i + b i + 2 ≤ d i + 2) (u : Fin (k + 1) → E) :
    (K * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)),
        Q i * p (a i + b i + 2) (u i)) *
        (Q₀ * p (a 0 + b 0 + (c + 1)) (u 0)) ≤
      (K * (Q₀ * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), Q i)) *
        ∏ i, p (d i + 2) (u i) := by
  classical
  have hprod :
      p (a 0 + b 0 + (c + 1)) (u 0) *
        (∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), p (a i + b i + 2) (u i)) ≤
      ∏ i, p (d i + 2) (u i) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => p (d i + 2) (u i))
      (Finset.mem_univ (0 : Fin (k + 1)))]
    exact mul_le_mul (hp hd0 (u 0))
      (Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _) (fun i _ => hp (hdi i) (u i)))
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) (apply_nonneg _ _)
  calc
    _ = (K * (Q₀ * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), Q i)) *
        (p (a 0 + b 0 + (c + 1)) (u 0) *
          ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), p (a i + b i + 2) (u i)) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod
      (mul_nonneg hK (mul_nonneg hQ₀ (Finset.prod_nonneg (fun i _ => hQ i))))

/-- A fixed finite allocation first gives the direct product of input
seminorms. This step contains no interpolation or directional-order choice. -/
theorem MaterialJetFamily.inputProduct
    {D : ReferenceData} {T : MaterialData} {A : SobolevModelData}
    (hT : IsMaterialData D T) (J : MaterialJetFamily T A)
    {k : ℕ} (a b : Fin (k + 1) → ℕ) (c : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (coefficient : PolarPoint → ℝ) (K : ℝ), 0 ≤ K →
      AEStronglyMeasurable coefficient materialCylinderMeasure →
      (∀ p, |coefficient p| ≤ K * T.M (T.radius p.1)) →
      ∀ u : Fin (k + 1) → A.Space,
        MemLp (materialFamilyMonomial J coefficient a b c u) 2 materialCylinderMeasure ∧
        (eLpNorm (materialFamilyMonomial J coefficient a b c u)
          2 materialCylinderMeasure).toReal ≤
          (K * P) * ∏ i, A.grading
            (a i + b i + (if i = 0 then c + 1 else 0) + 2) (u i) := by
  classical
  have hp : Monotone A.grading := gradedSeminorm_monotone (fun n => A.level n) A.bond
  choose Q hQ hQbound using fun i : Fin (k + 1) => J.pointwise (a i) (b i)
  obtain ⟨Q₀, hQ₀, hQnorm⟩ := J.weightedL2 (a 0) (b 0) (c + 1)
  let P : ℝ := Q₀ * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), Q i
  have hP : 0 ≤ P := mul_nonneg hQ₀ (Finset.prod_nonneg (fun i _ => hQ i))
  refine ⟨P, hP, ?_⟩
  intro coefficient K hK hc hcBound u
  have hN (i : Fin (k + 1)) :
      0 ≤ Q i * A.grading (a i + b i + 2) (u i) := mul_nonneg (hQ i) (apply_nonneg _ _)
  obtain ⟨hm, hn⟩ := materialWeightedProduct_memLp_and_norm_le hT
    (fun i => J.jet (a i) (b i) (u i)) c
    (fun i => Q i * A.grading (a i + b i + 2) (u i)) hN
    (fun i => J.continuous (a i) (b i) (u i)) (fun i p => hQbound i (u i) p)
    hK hc hcBound (hQnorm (u 0)).1
  refine ⟨hm, ?_⟩
  have hn' := hn.trans (mul_le_mul_of_nonneg_left (hQnorm (u 0)).2
    (mul_nonneg hK (Finset.prod_nonneg (fun i _ => hN i))))
  let d : Fin (k + 1) → ℕ := fun i => a i + b i + if i = 0 then c + 1 else 0
  have hd0 : a 0 + b 0 + (c + 1) ≤ d 0 + 2 := by simp [d]
  have hdi (i : Fin (k + 1)) : a i + b i + 2 ≤ d i + 2 := by
    dsimp [d]
    split_ifs <;> omega
  exact hn'.trans (family_input_product_le hp a b d c Q hK hQ₀ hQ hd0 hdi u)

private theorem family_weighted_interpolation
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hinterp : HasInterpolation p) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ k s : ℕ,
      ∀ (a b : Fin (k + 1) → ℕ) (c : ℕ),
      (∑ i, (a i + b i)) + c ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Fin (k + 1) → E,
        (∏ i, p (a i + b i + (if i = 0 then c + 1 else 0) + 2) (u i)) ≤
          C * ∑ i, p (s + loss) (u i) *
            ∏ j ∈ Finset.univ.erase i, p base (u j) := by
  classical
  obtain ⟨base, loss, hbase, hproduct⟩ := hinterp.oneHigh_product hp
  refine ⟨base, loss + 1, hbase, ?_⟩
  intro k s a b c horder
  let d : Fin (k + 1) → ℕ := fun i => a i + b i + if i = 0 then c + 1 else 0
  have hd : (∑ i, d i) ≤ s + 1 := by
    have heq : (∑ i, d i) = (∑ i, (a i + b i)) + (c + 1) := by
      simp [d, Finset.sum_add_distrib]
    rw [heq]
    omega
  obtain ⟨C, hC, hCu⟩ := hproduct k (s + 1) d hd
  refine ⟨C, hC, ?_⟩
  intro u
  have hindex : s + 1 + loss = s + (loss + 1) := by omega
  simpa only [hindex] using hCu u

private theorem family_bound_combine {N K P C X Y : ℝ}
    (hKP : 0 ≤ K * P) (hN : N ≤ (K * P) * X) (hX : X ≤ C * Y) :
    N ≤ K * (P * C) * Y := by
  calc
    N ≤ (K * P) * (C * Y) := hN.trans (mul_le_mul_of_nonneg_left hX hKP)
    _ = K * (P * C) * Y := by simp only [mul_assoc]

/-- One interpolation base and loss control every positive-arity monomial
of any material jet family, before any spatial or directional order is chosen. -/
theorem MaterialJetFamily.oneHigh
    {D : ReferenceData} {T : MaterialData} {A : SobolevModelData}
    (hT : IsMaterialData D T) (J : MaterialJetFamily T A)
    (hinterp : HasInterpolation A.grading) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ k s : ℕ,
      ∀ (a b : Fin (k + 1) → ℕ) (c : ℕ),
      (∑ i, (a i + b i)) + c ≤ s →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (coefficient : PolarPoint → ℝ) (K : ℝ), 0 ≤ K →
        AEStronglyMeasurable coefficient materialCylinderMeasure →
        (∀ p, |coefficient p| ≤ K * T.M (T.radius p.1)) →
        ∀ u : Fin (k + 1) → A.Space,
          MemLp (materialFamilyMonomial J coefficient a b c u) 2 materialCylinderMeasure ∧
          (eLpNorm (materialFamilyMonomial J coefficient a b c u)
            2 materialCylinderMeasure).toReal ≤
            K * C * ∑ i, A.grading (s + loss) (u i) *
              ∏ j ∈ Finset.univ.erase i, A.grading base (u j) := by
  have hp : Monotone A.grading := gradedSeminorm_monotone (fun n => A.level n) A.bond
  obtain ⟨base, loss, hbase, hproduct⟩ := family_weighted_interpolation hp hinterp
  refine ⟨base, loss, hbase, ?_⟩
  intro k s a b c horder
  obtain ⟨C, hC, hCu⟩ := hproduct k s a b c horder
  obtain ⟨P, hP, hPu⟩ := J.inputProduct hT a b c
  refine ⟨P * C, mul_nonneg hP hC, ?_⟩
  intro coefficient K hK hc hcBound u
  obtain ⟨hm, hn⟩ := hPu coefficient K hK hc hcBound u
  exact ⟨hm, family_bound_combine (mul_nonneg hK hP) hn (hCu u)⟩

end ContinuousFlexibility.Statements
