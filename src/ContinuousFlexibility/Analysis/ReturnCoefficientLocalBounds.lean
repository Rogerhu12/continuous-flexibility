import ContinuousFlexibility.Analysis.ReturnCorrectionSourceEnvelopes
import ContinuousFlexibility.Analysis.N01NeighborhoodRestriction
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine

/-!
# Local coefficient bounds with one fixed material and derivative loss

The material exponent, low order, and loss are chosen before the spatial
order. Two adjacent parameter orders share their finite maximum and a
smaller low-order neighborhood. The same bounds supply common actual
coefficient envelopes along each short scalar segment.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {U : Set E}

def CoefficientMaterialOneHighBound
    (p : ℕ → Seminorm ℝ E)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D))
    (n base loss d : ℕ) (V : Set E) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ V, ∀ v : Fin n → E,
    ∀ a b : ℕ, a + b ≤ k → ∀ q : PolarPoint,
      |mixedDerivative a b (fun y => ((A n x v).val (T.radius y.1, y.2)).1) q| ≤
        C * oneHighVariationWeight p base (k + loss) x v * T.M (T.radius q.1) ^ d ∧
      |mixedDerivative a b (fun y => ((A n x v).val (T.radius y.1, y.2)).2) q| ≤
        C * oneHighVariationWeight p base (k + loss) x v * T.M (T.radius q.1) ^ d

def LocalCoefficientMaterialTameBounds
    (p : ℕ → Seminorm ℝ E)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D)) : Prop :=
  ∀ n x₀, x₀ ∈ U → ∃ base loss d : ℕ, ∃ δ : ℝ, 0 < δ ∧
    CoefficientMaterialOneHighBound (T := T) p A n base loss d
      (U ∩ {x | p base (x - x₀) < δ})

theorem CoefficientMaterialOneHighBound.mono
    (hT : IsMaterialData D T) {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D)}
    {n base loss d base' loss' d' : ℕ} {V V' : Set E}
    (h : CoefficientMaterialOneHighBound (T := T) p A n base loss d V)
    (hb : base ≤ base') (hl : loss ≤ loss') (hd : d ≤ d') (hV : V' ⊆ V) :
    CoefficientMaterialOneHighBound (T := T) p A n base' loss' d' V' := by
  intro k
  obtain ⟨C, hC, hbound⟩ := h k
  refine ⟨C, hC, fun x hx v a b hab q => ?_⟩
  have hw := oneHighVariationWeight_mono hp hb (Nat.add_le_add_left hl k) x v
  have hw0 : 0 ≤ oneHighVariationWeight p base (k + loss) x v :=
    multilinearTameSize_nonneg _ _ _ (add_nonneg zero_le_one (apply_nonneg _ _)) v
  have hM : 1 ≤ T.M (T.radius q.1) :=
    (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 q.1).1).2.2.2
  have hpow := pow_le_pow_right₀ hM hd
  have hupper := mul_le_mul
    (mul_le_mul_of_nonneg_left hw hC) hpow
    (pow_nonneg (zero_le_one.trans hM) d)
    (mul_nonneg hC (hw0.trans hw))
  have hvalue := hbound x (hV hx) v a b hab q
  exact ⟨hvalue.1.trans hupper, hvalue.2.trans hupper⟩

theorem LocalCoefficientMaterialTameBounds.adjacent
    (hT : IsMaterialData D T) {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D)}
    (h : LocalCoefficientMaterialTameBounds (T := T) (U := U) p A)
    (n : ℕ) (x₀ : E) (hx₀ : x₀ ∈ U) :
    ∃ base loss d : ℕ, ∃ δ : ℝ, 0 < δ ∧
      CoefficientMaterialOneHighBound (T := T) p A n base loss d
        (U ∩ {x | p base (x - x₀) < δ}) ∧
      CoefficientMaterialOneHighBound (T := T) p A (n + 1) base loss d
        (U ∩ {x | p base (x - x₀) < δ}) := by
  obtain ⟨b₀, l₀, d₀, δ₀, hδ₀, h₀⟩ := h n x₀ hx₀
  obtain ⟨b₁, l₁, d₁, δ₁, hδ₁, h₁⟩ := h (n + 1) x₀ hx₀
  refine ⟨max b₀ b₁, max l₀ l₁, max d₀ d₁, min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_, ?_⟩
  · apply h₀.mono hT hp (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
    intro x hx
    exact ⟨hx.1, (hp (le_max_left b₀ b₁) (x - x₀)).trans_lt
      (hx.2.trans_le (min_le_left _ _))⟩
  · apply h₁.mono hT hp (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
    intro x hx
    exact ⟨hx.1, (hp (le_max_right b₀ b₁) (x - x₀)).trans_lt
      (hx.2.trans_le (min_le_right _ _))⟩

private theorem seminorm_affine_abs_le_one
    (p : Seminorm ℝ E) (x w : E) {t : ℝ} (ht : |t| ≤ 1) :
    p (x + t • w) ≤ p x + p w := by
  have h := map_add_le_add p x (t • w)
  rw [map_smul_eq_mul, Real.norm_eq_abs] at h
  exact h.trans (add_le_add (le_refl (p x))
    ((mul_le_mul_of_nonneg_right ht (apply_nonneg p w)).trans_eq (one_mul _)))

theorem LocalCoefficientMaterialTameBounds.lineBounds
    (hT : IsMaterialData D T)
    {p : ℕ → Seminorm ℝ E} (hp : ∀ k, Continuous (p k)) (hmono : Monotone p)
    (hU : IsOpen U)
    {A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D)}
    (h : LocalCoefficientMaterialTameBounds (T := T) (U := U) p A) :
    MaterialCoefficientJetLineBounds (T := T) (U := U) A := by
  intro n x hx w
  obtain ⟨base, loss, d, δ, hδ, hb⟩ := h n x hx
  have hlineCont : Continuous (fun t : ℝ => x + t • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, x + t • w ∈ U := by
    simpa only [zero_smul, add_zero] using
      hlineCont.continuousAt.eventually (hU.mem_nhds hx)
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, p base (x + t • w - x) < δ := by
    have hc : Continuous (fun t : ℝ => p base (x + t • w - x)) :=
      (hp base).comp (hlineCont.sub continuous_const)
    have hval : p base (x + (0 : ℝ) • w - x) < δ := by
      simpa only [zero_smul, add_zero, sub_self, map_zero] using hδ
    exact hc.continuousAt.eventually (isOpen_Iio.mem_nhds hval)
  obtain ⟨ε, hε, hεbound⟩ := Metric.eventually_nhds_iff.mp (hmem.and hnear)
  let ε' : ℝ := min ε 1
  have hε' : 0 < ε' := lt_min hε zero_lt_one
  have htmem {t : ℝ} (ht : |t| < ε') :
      x + t • w ∈ U ∩ {y | p base (y - x) < δ} := by
    apply hεbound
    simpa only [Real.dist_eq, sub_zero] using ht.trans_le (min_le_left _ _)
  refine ⟨ε', hε', fun t ht => (htmem ht).1, fun v => ⟨d, ?_⟩⟩
  intro a b
  obtain ⟨C, hC, hCbound⟩ := hb (a + b)
  let q : Seminorm ℝ E := p (max base (a + b + loss))
  let W : ℝ := ((n : ℝ) + 1) * (1 + q x + q w) * ∏ i, q (v i)
  have hW : 0 ≤ W := mul_nonneg
    (mul_nonneg (add_nonneg (Nat.cast_nonneg _) zero_le_one)
      (add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _)))
    (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
  refine ⟨C * W, mul_nonneg hC hW, fun t ht r => ?_⟩
  have htone : |t| ≤ 1 := ht.le.trans (min_le_right _ _)
  have hw := oneHighVariationWeight_le_seminorm_product p q base (a + b + loss)
    (hmono (le_max_left _ _)) (hmono (le_max_right _ _)) (x + t • w) v
  have hq := seminorm_affine_abs_le_one q x w htone
  have hweight : oneHighVariationWeight p base (a + b + loss) (x + t • w) v ≤ W := by
    apply hw.trans
    apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
    exact mul_le_mul_of_nonneg_left (by linarith only [hq])
      (add_nonneg (Nat.cast_nonneg _) zero_le_one)
  have hcoeff := hCbound (x + t • w) (htmem ht) v a b le_rfl r
  have hM : 0 ≤ T.M (T.radius r.1) ^ d := pow_nonneg
    (zero_le_one.trans (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 r.1).1).2.2.2) d
  have hupper := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hweight hC) hM
  exact ⟨hcoeff.1.trans hupper, hcoeff.2.trans hupper⟩

end ContinuousFlexibility.Statements
