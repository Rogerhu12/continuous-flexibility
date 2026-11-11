import ContinuousFlexibility.Analysis.MaterialDivergenceEnergy

/-!
# Common weighted energy envelopes for coefficient families

The envelopes below dominate the actual mixed derivatives. A uniform
coefficient bound uses one fixed extra power of the material weight,
independently of both spatial derivative orders. Finite Leibniz sums
therefore give one nonnegative L² envelope for the entire family.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

/-- One common integrable bound for each actual weighted mixed jet. -/
def WeightedMixedJetEnvelopes {ι : Type*}
    (W : PolarPoint → ℝ) (f : ι → PolarPoint → ℝ) : Prop :=
  ∀ a b c, ∃ G : PolarPoint → ℝ,
    MemLp G 2 materialCylinderMeasure ∧ (∀ p, 0 ≤ G p) ∧
      ∀ i p, |W p ^ c * mixedDerivative a b (f i) p| ≤ G p

/-- The corresponding property for the actual physical jets. -/
def PhysicalJetEnvelopes {ι : Type*}
    (T : MaterialData) (γ : ℝ) (f : ι → PolarPoint → ℝ) : Prop :=
  ∀ a b c, ∃ G : PolarPoint → ℝ,
    MemLp G 2 materialCylinderMeasure ∧ (∀ p, 0 ≤ G p) ∧
      ∀ i p, |weightedPhysicalJet T γ a b c (f i) p| ≤ G p

theorem physicalJetEnvelopes_iff_material {ι : Type*}
    {T : MaterialData} {γ : ℝ} {f : ι → PolarPoint → ℝ} :
    PhysicalJetEnvelopes T γ f ↔
      WeightedMixedJetEnvelopes (fun p => T.M (T.radius p.1))
        (fun i => materialPullback T γ (f i)) := Iff.rfl

theorem WeightedMixedJetEnvelopes.congr {ι : Type*}
    {W : PolarPoint → ℝ} {f g : ι → PolarPoint → ℝ}
    (h : WeightedMixedJetEnvelopes W f) (heq : ∀ i, f i = g i) :
    WeightedMixedJetEnvelopes W g := by
  intro a b c
  obtain ⟨G, hG, hGpos, hb⟩ := h a b c
  refine ⟨G, hG, hGpos, fun i p => ?_⟩
  rw [← heq i]
  exact hb i p

theorem weightedMixedJetEnvelopes_const {ι : Type*}
    {W g : PolarPoint → ℝ}
    (hLp : ∀ a b c, MemLp (fun p => W p ^ c * mixedDerivative a b g p)
      2 materialCylinderMeasure) :
    WeightedMixedJetEnvelopes W (fun _ : ι => g) := by
  intro a b c
  refine ⟨fun p => ‖W p ^ c * mixedDerivative a b g p‖,
    (hLp a b c).norm, fun p => norm_nonneg _, fun i p => ?_⟩
  exact (Real.norm_eq_abs _).symm.le

theorem physicalJetEnvelopes_const {ι : Type*}
    {T : MaterialData} {γ : ℝ} {g : PolarPoint → ℝ}
    (hLp : ∀ a b c, MemLp (weightedPhysicalJet T γ a b c g)
      2 materialCylinderMeasure) :
    PhysicalJetEnvelopes T γ (fun _ : ι => g) := by
  exact physicalJetEnvelopes_iff_material.mpr (weightedMixedJetEnvelopes_const hLp)

theorem WeightedMixedJetEnvelopes.add {ι : Type*}
    {W : PolarPoint → ℝ} {f g : ι → PolarPoint → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hfenv : WeightedMixedJetEnvelopes W f) (hgenv : WeightedMixedJetEnvelopes W g) :
    WeightedMixedJetEnvelopes W (fun i p => f i p + g i p) := by
  intro a b c
  obtain ⟨F, hF, hFpos, hfb⟩ := hfenv a b c
  obtain ⟨G, hG, hGpos, hgb⟩ := hgenv a b c
  refine ⟨fun p => F p + G p, hF.add hG,
    fun p => add_nonneg (hFpos p) (hGpos p), fun i p => ?_⟩
  rw [mixedDerivative_add_of_contDiff (hf i) (hg i), mul_add]
  exact (abs_add_le _ _).trans (add_le_add (hfb i p) (hgb i p))

private theorem weighted_coefficient_product_bound
    (w f g K : ℝ) (c d : ℕ) (hw : 0 ≤ w)
    (hf : |f| ≤ K * w ^ d) :
    |w ^ c * f * g| ≤ K * |w ^ (c + d) * g| := by
  simp only [abs_mul, abs_of_nonneg (pow_nonneg hw c),
    abs_of_nonneg (pow_nonneg hw d), abs_of_nonneg (pow_nonneg hw (c + d)), pow_add]
  calc
    w ^ c * |f| * |g| ≤ w ^ c * (K * w ^ d) * |g| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hf (pow_nonneg hw c)) (abs_nonneg g)
    _ = K * (w ^ c * w ^ d * |g|) := by ring

theorem WeightedMixedJetEnvelopes.bounded_mul {ι : Type*}
    {W : PolarPoint → ℝ} {f g : ι → PolarPoint → ℝ}
    (hW : ∀ p, 0 ≤ W p)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (d : ℕ)
    (hbound : ∀ a b, ∃ K : ℝ, 0 ≤ K ∧
      ∀ i p, |mixedDerivative a b (f i) p| ≤ K * W p ^ d)
    (henv : WeightedMixedJetEnvelopes W g) :
    WeightedMixedJetEnvelopes W (fun i p => f i p * g i p) := by
  classical
  choose K hK hcoeff using hbound
  change ∀ a b c, ∃ G : PolarPoint → ℝ,
    MemLp G 2 materialCylinderMeasure ∧ (∀ p, 0 ≤ G p) ∧
      ∀ i p, |W p ^ c * mixedDerivative a b (g i) p| ≤ G p at henv
  choose G hGLp hGpos hgb using henv
  intro a b c
  let V (j k : ℕ) (p : PolarPoint) : ℝ :=
    ((b.choose j : ℝ) * (a.choose k : ℝ) * K k j) * G (a - k) (b - j) (c + d) p
  have hV (j k : ℕ) : MemLp (V j k) 2 materialCylinderMeasure :=
    (hGLp (a - k) (b - j) (c + d)).const_mul _
  have hVpos (j k : ℕ) (p : PolarPoint) : 0 ≤ V j k p :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (hK k j)) (hGpos (a - k) (b - j) (c + d) p)
  refine ⟨fun p => ∑ j ∈ Finset.range (b + 1), ∑ k ∈ Finset.range (a + 1), V j k p,
    memLp_finsetSum _ (fun j _ => memLp_finsetSum _ (fun k _ => hV j k)),
    fun p => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hVpos j k p)),
    fun i p => ?_⟩
  rw [weighted_mixedDerivative_mul (hf i) (hg i)]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hbin : 0 ≤ (b.choose j : ℝ) * (a.choose k : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [abs_mul, abs_of_nonneg hbin]
  have hterm := weighted_coefficient_product_bound (W p)
    (mixedDerivative k j (f i) p) (mixedDerivative (a - k) (b - j) (g i) p)
    (K k j) c d (hW p) (hcoeff k j i p)
  calc
    (b.choose j : ℝ) * (a.choose k : ℝ) *
        |W p ^ c * mixedDerivative k j (f i) p *
          mixedDerivative (a - k) (b - j) (g i) p| ≤
        (b.choose j : ℝ) * (a.choose k : ℝ) *
          (K k j * |W p ^ (c + d) * mixedDerivative (a - k) (b - j) (g i) p|) :=
      mul_le_mul_of_nonneg_left hterm hbin
    _ ≤ (b.choose j : ℝ) * (a.choose k : ℝ) *
          (K k j * G (a - k) (b - j) (c + d) p) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hgb (a - k) (b - j) (c + d) i p) (hK k j)) hbin
    _ = V j k p := by dsimp only [V]; ring

theorem materialCoordinate_comp_family_fderiv_bounded
    {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {f : ι → PolarPoint → F}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (annularOpen D))
    (hbound : ∀ n : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ i p, p ∈ annularOpen D →
      ‖iteratedFDeriv ℝ n (f i) p‖ ≤ A) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i p,
      ‖iteratedFDeriv ℝ n (fun q => f i (T.radius q.1, q.2)) p‖ ≤ A := by
  have hr : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  have hinside (r : ℝ) : T.radius r ∈ Ioo D.a D.b := (hT.2.2.2.2.2.2.2.1 r).1
  let g (p : PolarPoint) : PolarPoint := (T.radius p.1, p.2)
  have hg : ContDiff ℝ ∞ g := (hr.comp contDiff_fst).prodMk contDiff_snd
  have hout (k : ℕ) (_ : k ≤ n) :
      ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ i p, p ∈ (univ : Set PolarPoint) →
        ‖iteratedFDeriv ℝ k (f i) (g p)‖ ≤ A * (1 : ℝ) ^ P := by
    obtain ⟨A, hA, hb⟩ := hbound k
    exact ⟨A, 0, hA, le_rfl, fun i p _ => by
      simpa only [Real.rpow_zero, mul_one] using hb i (g p) ⟨hinside p.1, mem_univ _⟩⟩
  have hin (k : ℕ) (hk : 1 ≤ k) (_ : k ≤ n) :
      ∃ A P : ℝ, 0 ≤ A ∧ 0 ≤ P ∧ ∀ (_ : ι) p, p ∈ (univ : Set PolarPoint) →
        ‖iteratedFDeriv ℝ k g p‖ ≤ A * (1 : ℝ) ^ P := by
    obtain ⟨A, hA, hb⟩ := materialCoordinate_positive_fderiv_bounded hT k hk
    exact ⟨A, 0, hA, le_rfl, fun _ p _ => by
      simpa only [Real.rpow_zero, mul_one] using hb p⟩
  obtain ⟨A, P, hA, _, hb⟩ := norm_iteratedFDeriv_comp_polynomial_bound
    (fun _ : ι => (1 : ℝ)) (fun _ => le_rfl) (fun _ => univ) (fun _ => annularOpen D)
    (fun _ => isOpen_univ) (fun _ => isOpen_Ioo.prod isOpen_univ)
    (fun _ => g) f (fun _ => hg.contDiffOn) hf
    (fun _ p _ => ⟨hinside p.1, mem_univ _⟩) n hout hin
  exact ⟨A, hA, fun i p => by
    simpa only [Real.one_rpow, mul_one] using hb i p (mem_univ _)⟩

theorem materialCoordinate_comp_family_mixed_bounded
    {ι : Type*} {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {f : ι → PolarPoint → ℝ}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (annularOpen D))
    (hbound : ∀ n : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ i p, p ∈ annularOpen D →
      ‖iteratedFDeriv ℝ n (f i) p‖ ≤ A) (a b : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i p,
      |mixedDerivative a b (fun q => f i (T.radius q.1, q.2)) p| ≤ A := by
  have hr : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  have hinside (r : ℝ) : T.radius r ∈ Ioo D.a D.b := (hT.2.2.2.2.2.2.2.1 r).1
  have hg (i : ι) : ContDiff ℝ ∞ (fun q : PolarPoint => f i (T.radius q.1, q.2)) :=
    (hf i).comp_contDiff ((hr.comp contDiff_fst).prodMk contDiff_snd)
      (fun p => ⟨hinside p.1, mem_univ _⟩)
  obtain ⟨A, hA, hb⟩ := materialCoordinate_comp_family_fderiv_bounded hT hf hbound (a + b)
  exact ⟨A, hA, fun i p => (mixedDerivative_abs_le_norm_iteratedFDeriv
    isOpen_univ (hg i).contDiffOn a b (mem_univ p)).trans (hb i p)⟩

theorem PhysicalJetEnvelopes.bounded_mul
    {ι : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {f u : ι → PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (annularOpen D))
    (hbound : ∀ n : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ i p, p ∈ annularOpen D →
      ‖iteratedFDeriv ℝ n (f i) p‖ ≤ A)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (annularOpen D))
    (henv : PhysicalJetEnvelopes T γ u) :
    PhysicalJetEnvelopes T γ (fun i p => f i p * u i p) := by
  let W (p : PolarPoint) : ℝ := T.M (T.radius p.1)
  let F (i : ι) (p : PolarPoint) : ℝ := f i (T.radius p.1, p.2)
  let G (i : ι) : PolarPoint → ℝ := materialPullback T γ (u i)
  have hr : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  have hinside (r : ℝ) : T.radius r ∈ Ioo D.a D.b := (hT.2.2.2.2.2.2.2.1 r).1
  have hW (p : PolarPoint) : 0 ≤ W p :=
    zero_le_one.trans (hT.2.1 _ (hinside p.1)).2.2.2
  have hF (i : ι) : ContDiff ℝ ∞ (F i) :=
    (hf i).comp_contDiff ((hr.comp contDiff_fst).prodMk contDiff_snd)
      (fun p => ⟨hinside p.1, mem_univ _⟩)
  have hG (i : ι) : ContDiff ℝ ∞ (G i) := contDiff_materialPullback hT (hu i)
  have hFb (a b : ℕ) : ∃ K : ℝ, 0 ≤ K ∧
      ∀ i p, |mixedDerivative a b (F i) p| ≤ K * W p ^ 0 := by
    obtain ⟨K, hK, hb⟩ := materialCoordinate_comp_family_mixed_bounded hT hf hbound a b
    exact ⟨K, hK, fun i p => by simpa only [pow_zero, mul_one] using hb i p⟩
  have hGenv : WeightedMixedJetEnvelopes W G := physicalJetEnvelopes_iff_material.mp henv
  have hprod := WeightedMixedJetEnvelopes.bounded_mul hW hF hG 0 hFb hGenv
  apply physicalJetEnvelopes_iff_material.mpr
  apply hprod.congr
  intro i
  funext p
  dsimp only [F, G, materialPullback]
  ring

end ContinuousFlexibility.Statements
