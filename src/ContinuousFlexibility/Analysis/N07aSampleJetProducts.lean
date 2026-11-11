import ContinuousFlexibility.Analysis.N07aSampleJetBounds
import ContinuousFlexibility.Analysis.N07aFiniteStateProduct

/-!
# Multiplication of actual coefficient jets with fixed loss

The genuine Leibniz terms are estimated at their own derivative orders.
Interpolation is applied to the complete pair of state factors before
summing, on one low-order ball for every output order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

private theorem n07a_twoJetProduct_bound {k A B C u v P Q R : ℝ}
    (hk : 0 ≤ k) (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ P)
    (hu : |u| ≤ A * P) (hv : |v| ≤ B * Q) (hpq : P * Q ≤ C * R) :
    |k * u * v| ≤ (k * A * B * C) * R := by
  rw [abs_mul, abs_mul, abs_of_nonneg hk]
  calc
    _ ≤ (k * (A * P)) * (B * Q) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hu hk) hv (abs_nonneg _)
        (mul_nonneg hk (mul_nonneg hA hP))
    _ = (k * A * B) * (P * Q) := by ring
    _ ≤ (k * A * B) * (C * R) :=
      mul_le_mul_of_nonneg_left hpq (mul_nonneg (mul_nonneg hk hA) hB)
    _ = _ := by ring

theorem n07a_mixedDerivative_mul_fin {W : Set PolarPoint} (hW : IsOpen W)
    {f g : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g W)
    (i j : ℕ) {x : PolarPoint} (hx : x ∈ W) :
    mixedDerivative i j (fun y => f y * g y) x =
      ∑ k : Fin (j + 1) × Fin (i + 1),
        (j.choose k.1.val : ℝ) * (i.choose k.2.val : ℝ) *
          mixedDerivative k.2.val k.1.val f x *
            mixedDerivative (i - k.2.val) (j - k.1.val) g x := by
  rw [Fintype.sum_prod_type]
  let term : ℕ → ℕ → ℝ := fun q r =>
    (j.choose q : ℝ) * (i.choose r : ℝ) *
      mixedDerivative r q f x * mixedDerivative (i - r) (j - q) g x
  change mixedDerivative i j (fun y => f y * g y) x =
    ∑ q : Fin (j + 1), ∑ r : Fin (i + 1), term q.val r.val
  rw [Fin.sum_univ_eq_sum_range (fun q => ∑ r : Fin (i + 1), term q r.val)]
  have he : (∑ q ∈ Finset.range (j + 1), ∑ r : Fin (i + 1), term q r.val) =
      ∑ q ∈ Finset.range (j + 1), ∑ r ∈ Finset.range (i + 1), term q r := by
    apply Finset.sum_congr rfl
    intro q _
    exact Fin.sum_univ_eq_sum_range (term q) (i + 1)
  rw [he]
  exact n07a_mixedDerivative_mul_on hW hf hg i j hx

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

/-- One fixed low-order ball handles every coefficient product derivative. -/
theorem n07a_sampleJetBounds_mul_uniform
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hIp : HasSmoothing p)
    (U : Set E) (W : ℕ → Set PolarPoint) (hW : ∀ m, IsOpen (W m))
    (d : ℕ) :
    ∃ low loss : ℕ, ∀ f g : E → ℕ → PolarPoint → ℝ,
      N07aSampleJetBounds T K p U W d f →
      N07aSampleJetBounds T K p U W d g →
      (∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (f z m) (W m)) →
      (∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (g z m) (W m)) →
      N07aSampleJetBounds T K p {z | z ∈ U ∧ p low z ≤ 1} W loss
        (fun z m x => f z m x * g z m x) := by
  classical
  obtain ⟨low, loss, hprod⟩ := n07a_finite_state_product p hp hIp d
  refine ⟨low, loss, fun f g hf hg hfs hgs i j => ?_⟩
  let I := Fin (j + 1) × Fin (i + 1)
  choose e he he0 heb using fun k : I => hf k.2.val k.1.val
  choose a ha ha0 hab using fun k : I => hg (i - k.2.val) (j - k.1.val)
  have htwo (k : I) := hprod 2
    ![k.2.val + k.1.val, (i - k.2.val) + (j - k.1.val)] (i + j)
    (by simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
  choose C hC hCb using htwo
  let factor : I → ℝ := fun k => (j.choose k.1.val : ℝ) * (i.choose k.2.val : ℝ)
  have hfactor (k : I) : 0 ≤ factor k := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  let v : I → ℕ → ℝ := fun k m => factor k * e k m * a k m * C k
  have hv (k : I) : N07aSampleSubpower T K (v k) :=
    N07aSampleSubpower.mul hD hT
      (N07aSampleSubpower.mul hD hT
        (N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT (factor k)) (he k))
        (ha k)) (N07aSampleSubpower.const hD hT (C k))
  have hv0 (k : I) (m : ℕ) : 0 ≤ v k m :=
    mul_nonneg (mul_nonneg (mul_nonneg (hfactor k) (he0 k m)) (ha0 k m)) (hC k)
  refine ⟨fun m => ∑ k : I, v k m,
    N07aSampleSubpower.finset_sum hD hT Finset.univ v (fun k _ => hv k),
    fun m => Finset.sum_nonneg (fun k _ => hv0 k m), ?_⟩
  intro z hz m x hx
  rw [n07a_mixedDerivative_mul_fin (hW m) (hfs z hz.1 m) (hgs z hz.1 m) i j hx,
    Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  have hpair : (1 + p (k.2.val + k.1.val + d) z) *
      (1 + p ((i - k.2.val) + (j - k.1.val) + d) z) ≤
      C k * (1 + p (i + j + loss) z) := by
    simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
      hCb k z hz.2
  exact n07a_twoJetProduct_bound (hfactor k) (he0 k m) (ha0 k m)
    (add_nonneg zero_le_one (apply_nonneg _ _))
    (heb k z hz.1 m x hx) (hab k z hz.1 m x hx) hpair


/-- A selected pair inherits the same product estimate. -/
theorem n07a_sampleJetBounds_mul
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hIp : HasSmoothing p)
    (U : Set E) (W : ℕ → Set PolarPoint) (hW : ∀ m, IsOpen (W m))
    (d : ℕ) (f g : E → ℕ → PolarPoint → ℝ)
    (hf : N07aSampleJetBounds T K p U W d f)
    (hg : N07aSampleJetBounds T K p U W d g)
    (hfs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (f z m) (W m))
    (hgs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (g z m) (W m)) :
    ∃ low loss : ℕ,
      N07aSampleJetBounds T K p {z | z ∈ U ∧ p low z ≤ 1} W loss
        (fun z m x => f z m x * g z m x) := by
  obtain ⟨low, loss, hb⟩ :=
    n07a_sampleJetBounds_mul_uniform hD hT p hp hIp U W hW d
  exact ⟨low, loss, hb f g hf hg hfs hgs⟩

end ContinuousFlexibility.Analysis
