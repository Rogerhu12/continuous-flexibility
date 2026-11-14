module

public import ContinuousFlexibility.Analysis.N07aCompositionBudget
public import ContinuousFlexibility.Analysis.N07aSampleEnvelopes

/-!
# The complete actual composition estimate

The actual Faà di Bruno terms are bounded before the finite sum is taken.
The source block count and chart block charges share one derivative budget;
the low parameter ball and loss are independent of the output order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

theorem n07a_sampleComposition_fixedLoss
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (hp : Monotone p) (hq : Monotone q)
    (hIp : HasSmoothing p) (hIq : HasSmoothing q)
    (U : Set E) (W : ℕ → Set PolarPoint) (d : ℕ)
    (f : F → PolarPoint → ℝ) (Φ : E → ℕ → PolarPoint → PolarPoint)
    (w : ℕ → ℕ → ℝ) (hw : ∀ c m, 0 ≤ w c m)
    (hfs : ∀ z ∈ U, ∀ u m x, x ∈ W m → ContDiffAt ℝ ∞ (f u) (Φ z m x))
    (hΦs : ∀ z ∈ U, ∀ m x, x ∈ W m → ContDiffAt ℝ ∞ (Φ z m) x)
    (houter : ∀ n c : ℕ, ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, ∀ u m x, x ∈ W m →
          ‖iteratedFDeriv ℝ n (f u) (Φ z m x)‖ ≤
            e m * w c m * q (c + n + d) u)
    (hchart : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, ∀ m x, x ∈ W m →
          ‖iteratedFDeriv ℝ n (Φ z m) x‖ ≤
            e m * (1 + p ((n - 1) + d) z)) :
    ∃ low loss : ℕ, ∀ n c : ℕ, ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, p low z ≤ 1 → ∀ u m x, x ∈ W m →
          ‖iteratedFDeriv ℝ n (f u ∘ Φ z m) x‖ ≤
            e m * w c m *
              (q (c + n + loss) u + (1 + p (c + n + loss) z) * q low u) := by
  classical
  obtain ⟨low, loss, hprod⟩ := n07a_chainrule_oneHigh_product p q hp hq hIp hIq d
  refine ⟨low, loss, fun n c => ?_⟩
  choose a ha ha0 hab using fun k : OrderedFinpartition n => houter k.length c
  choose b hb hb0 hbb using fun k : OrderedFinpartition n =>
    fun j : Fin k.length => hchart (k.partSize j) (k.partSize_pos j)
  choose C hC hCb using fun k : OrderedFinpartition n => hprod n c k
  let e : OrderedFinpartition n → ℕ → ℝ :=
    fun k m => a k m * (∏ j, b k j m) * C k
  have he (k : OrderedFinpartition n) : N07aSampleSubpower T K (e k) :=
    N07aSampleSubpower.mul hD hT
      (N07aSampleSubpower.mul hD hT (ha k)
        (N07aSampleSubpower.finset_prod hD hT Finset.univ (b k) (fun j _ => hb k j)))
      (N07aSampleSubpower.const hD hT (C k))
  have he0 (k : OrderedFinpartition n) (m : ℕ) : 0 ≤ e k m :=
    mul_nonneg (mul_nonneg (ha0 k m)
      (Finset.prod_nonneg (fun j _ => hb0 k j m))) (hC k)
  refine ⟨fun m => ∑ k, e k m,
    N07aSampleSubpower.finset_sum hD hT Finset.univ e (fun k _ => he k),
    fun m => Finset.sum_nonneg (fun k _ => he0 k m), ?_⟩
  intro z hz hzlow u m x hx
  apply (norm_iteratedFDeriv_comp_le_partition_sum (hfs z hz u m x hx)
    (hΦs z hz m x hx) n).trans
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  have hφ : (∏ j, ‖iteratedFDeriv ℝ (k.partSize j) (Φ z m) x‖) ≤
      (∏ j, b k j m) * (∏ j, (1 + p ((k.partSize j - 1) + d) z)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
      (fun j _ => hbb k j z hz m x hx)
  have hbprod : 0 ≤ ∏ j, b k j m := Finset.prod_nonneg (fun j _ => hb0 k j m)
  calc
    _ ≤ (a k m * w c m * q (c + k.length + d) u) *
        ((∏ j, b k j m) * (∏ j, (1 + p ((k.partSize j - 1) + d) z))) :=
      mul_le_mul (hab k z hz u m x hx) hφ
        (Finset.prod_nonneg (fun j _ => norm_nonneg _))
        (mul_nonneg (mul_nonneg (ha0 k m) (hw c m)) (apply_nonneg _ _))
    _ = (a k m * (∏ j, b k j m) * w c m) *
        (q (c + k.length + d) u * (∏ j, (1 + p ((k.partSize j - 1) + d) z))) := by ring
    _ ≤ (a k m * (∏ j, b k j m) * w c m) *
        (C k * (q (c + n + loss) u + (1 + p (c + n + loss) z) * q low u)) :=
      mul_le_mul_of_nonneg_left (hCb k z hzlow u)
        (mul_nonneg (mul_nonneg (ha0 k m) hbprod) (hw c m))
    _ = _ := by dsimp only [e]; ring

end ContinuousFlexibility.Analysis
