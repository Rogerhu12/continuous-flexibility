import ContinuousFlexibility.Analysis.N07aSampleJetProducts
import ContinuousFlexibility.Analysis.N07aFiniteParameterProduct

/-!
# Actual source-linear mixed jets with one fixed loss

A finite multiplication by a geometric coefficient preserves the same
one-high form. The proof applies the product interpolation theorem to the
actual Leibniz terms, including the source low-norm term.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

def N07aSampleLinearJetBounds (T : MaterialData) {S : PhysicalSpacesData}
    (K : CanonicalData S) (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (U : Set E) (W : ℕ → Set PolarPoint) (w : ℕ → ℕ → ℝ)
    (low loss : ℕ) (f : E → F → ℕ → PolarPoint → ℝ) : Prop :=
  ∀ a b c : ℕ, ∃ e : ℕ → ℝ,
    N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      ∀ z ∈ U, ∀ u m x, x ∈ W m →
        |mixedDerivative a b (f z u m) x| ≤ e m * w c m *
          (q (c + (a + b) + loss) u +
            (1 + p (c + (a + b) + loss) z) * q low u)

theorem N07aSampleLinearJetBounds.restrict
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U U' : Set E} {W : ℕ → Set PolarPoint} {w : ℕ → ℕ → ℝ}
    {low loss : ℕ} {f : E → F → ℕ → PolarPoint → ℝ}
    (hf : N07aSampleLinearJetBounds T K p q U W w low loss f) (hU : U' ⊆ U) :
    N07aSampleLinearJetBounds T K p q U' W w low loss f := by
  intro a b c
  obtain ⟨e, he, he0, heb⟩ := hf a b c
  exact ⟨e, he, he0, fun z hz => heb z (hU hz)⟩

theorem N07aSampleLinearJetBounds.low_mono
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} {W : ℕ → Set PolarPoint} {w : ℕ → ℕ → ℝ}
    {low low' loss : ℕ} {f : E → F → ℕ → PolarPoint → ℝ}
    (hq : Monotone q) (hw : ∀ c m, 0 ≤ w c m) (hlow : low ≤ low')
    (hf : N07aSampleLinearJetBounds T K p q U W w low loss f) :
    N07aSampleLinearJetBounds T K p q U W w low' loss f := by
  intro a b c
  obtain ⟨e, he, he0, heb⟩ := hf a b c
  refine ⟨e, he, he0, fun z hz u m x hx => (heb z hz u m x hx).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hq hlow u)
      (add_nonneg zero_le_one (apply_nonneg _ _))))
    (mul_nonneg (he0 m) (hw c m))

private theorem n07a_linearJet_term_numeric {k e a w P Q R L C₁ C₂ : ℝ}
    (hk : 0 ≤ k) (he : 0 ≤ e) (ha : 0 ≤ a) (hw : 0 ≤ w)
    (hP : 0 ≤ P)
    {u v : ℝ} (hu : |u| ≤ e * P) (hv : |v| ≤ a * w * (Q + R * L))
    {B : ℝ} (h₁ : Q * P ≤ C₁ * B) (h₂ : L * (R * P) ≤ C₂ * B) :
    |k * u * v| ≤ (k * e * a * (C₁ + C₂)) * w * B := by
  rw [abs_mul, abs_mul, abs_of_nonneg hk]
  calc
    _ ≤ (k * (e * P)) * (a * w * (Q + R * L)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hu hk) hv (abs_nonneg _)
        (mul_nonneg hk (mul_nonneg he hP))
    _ = (k * e * a * w) * (Q * P + L * (R * P)) := by ring
    _ ≤ (k * e * a * w) * ((C₁ + C₂) * B) :=
      mul_le_mul_of_nonneg_left ((add_le_add h₁ h₂).trans_eq (by ring))
        (mul_nonneg (mul_nonneg (mul_nonneg hk he) ha) hw)
    _ = _ := by ring

variable [TopologicalSpace E] [TopologicalSpace F]

theorem n07a_sampleLinearJetBounds_mul
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (hp : Monotone p) (hq : Monotone q) (hIp : HasSmoothing p) (hIq : HasSmoothing q)
    (U : Set E) (W : ℕ → Set PolarPoint) (hW : ∀ m, IsOpen (W m))
    (w : ℕ → ℕ → ℝ) (hw : ∀ c m, 0 ≤ w c m)
    (A : E → ℕ → PolarPoint → ℝ) (f : E → F → ℕ → PolarPoint → ℝ)
    (dA low df : ℕ) (hA : N07aSampleJetBounds T K p U W dA A)
    (hf : N07aSampleLinearJetBounds T K p q U W w low df f)
    (hAs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (A z m) (W m))
    (hfs : ∀ z ∈ U, ∀ u m, ContDiffOn ℝ ∞ (f z u m) (W m)) :
    ∃ low' loss : ℕ,
      N07aSampleLinearJetBounds T K p q {z | z ∈ U ∧ p low' z ≤ 1} W w low' loss
        (fun z u m x => A z m x * f z u m x) := by
  classical
  let d := max dA (max df low)
  have hdA : dA ≤ d := le_max_left _ _
  have hdf : df ≤ d := (le_max_left df low).trans (le_max_right _ _)
  have hdl : low ≤ d := (le_max_right df low).trans (le_max_right _ _)
  obtain ⟨low', loss, hprod⟩ := n07a_finite_parameter_source_product p q hp hq hIp hIq d
  refine ⟨low', loss, fun i j c => ?_⟩
  let I := Fin (j + 1) × Fin (i + 1)
  choose e he he0 heb using fun k : I => hA k.2.val k.1.val
  choose a ha ha0 hab using fun k : I => hf (i - k.2.val) (j - k.1.val) c
  let t : I → ℕ := fun k => c + ((i - k.2.val) + (j - k.1.val))
  let r : I → ℕ := fun k => k.2.val + k.1.val
  have hbudget (k : I) : t k + r k = c + (i + j) := by
    dsimp only [t, r]
    have hki := k.2.isLt
    have hkj := k.1.isLt
    omega
  have hfirst (k : I) := hprod 1 (fun _ => r k) (t k) (c + (i + j))
    (by simpa only [Fin.sum_univ_one] using (hbudget k).le)
  have hsecond (k : I) := hprod 2 ![t k, r k] 0 (c + (i + j))
    (by simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_add] using (hbudget k).le)
  choose C₁ hC₁ hC₁b using hfirst
  choose C₂ hC₂ hC₂b using hsecond
  let factor : I → ℝ := fun k => (j.choose k.1.val : ℝ) * (i.choose k.2.val : ℝ)
  have hfactor (k : I) : 0 ≤ factor k := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  let env : I → ℕ → ℝ := fun k m => factor k * e k m * a k m * (C₁ k + C₂ k)
  have henv (k : I) : N07aSampleSubpower T K (env k) :=
    N07aSampleSubpower.mul hD hT
      (N07aSampleSubpower.mul hD hT
        (N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT (factor k)) (he k))
        (ha k)) (N07aSampleSubpower.const hD hT (C₁ k + C₂ k))
  have henv0 (k : I) (m : ℕ) : 0 ≤ env k m :=
    mul_nonneg (mul_nonneg (mul_nonneg (hfactor k) (he0 k m)) (ha0 k m))
      (add_nonneg (hC₁ k) (hC₂ k))
  refine ⟨fun m => ∑ k, env k m,
    N07aSampleSubpower.finset_sum hD hT Finset.univ env (fun k _ => henv k),
    fun m => Finset.sum_nonneg (fun k _ => henv0 k m), ?_⟩
  intro z hz u m x hx
  rw [n07a_mixedDerivative_mul_fin (hW m) (hAs z hz.1 m) (hfs z hz.1 u m) i j hx,
    Finset.sum_mul, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  have hP : 0 ≤ 1 + p (r k + d) z := add_nonneg zero_le_one (apply_nonneg _ _)
  have hR : 0 ≤ 1 + p (t k + d) z := add_nonneg zero_le_one (apply_nonneg _ _)
  have hAc : |mixedDerivative k.2.val k.1.val (A z m) x| ≤
      e k m * (1 + p (r k + d) z) :=
    (heb k z hz.1 m x hx).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (hp (Nat.add_le_add_left hdA (r k)) z)) (he0 k m))
  have hfc : |mixedDerivative (i - k.2.val) (j - k.1.val) (f z u m) x| ≤
      a k m * w c m * (q (t k + d) u + (1 + p (t k + d) z) * q d u) := by
    apply (hab k z hz.1 u m x hx).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (ha0 k m) (hw c m))
    exact add_le_add (hq (Nat.add_le_add_left hdf (t k)) u)
      (mul_le_mul (add_le_add le_rfl (hp (Nat.add_le_add_left hdf (t k)) z))
        (hq hdl u) (apply_nonneg _ _) hR)
  have h₁ := hC₁b k z hz.2 u
  have h₂ := hC₂b k z hz.2 u
  simp only [Fin.prod_univ_one] at h₁
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zero_add] at h₂
  exact n07a_linearJet_term_numeric (hfactor k) (he0 k m) (ha0 k m) (hw c m)
    hP hAc hfc h₁ h₂

end ContinuousFlexibility.Analysis
