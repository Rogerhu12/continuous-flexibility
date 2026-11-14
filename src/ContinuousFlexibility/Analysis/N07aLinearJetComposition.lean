module

public import ContinuousFlexibility.Analysis.N07aLinearJetFrechetBounds
public import ContinuousFlexibility.Analysis.N07aFiniteOneHighProduct
public import ContinuousFlexibility.Analysis.N07aCompositionBudget

/-!
# Composition of the actual source-linear jets with the actual chart

Both functions may depend on the same state and piece. The derivative
partition is charged once, including the high-state term already present
in the outer estimate.
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

theorem n07a_sampleLinearJetBounds_comp
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (hp : Monotone p) (hq : Monotone q) (hIp : HasSmoothing p) (hIq : HasSmoothing q)
    (U : Set E) (W V : ℕ → Set PolarPoint)
    (hW : ∀ m, IsOpen (W m)) (hV : ∀ m, IsOpen (V m))
    (w : ℕ → ℕ → ℝ) (hw : ∀ c m, 0 ≤ w c m)
    (f : E → F → ℕ → PolarPoint → ℝ) (Φ : E → ℕ → PolarPoint → PolarPoint)
    (low df dΦ : ℕ) (hf : N07aSampleLinearJetBounds T K p q U V w low df f)
    (hfs : ∀ z ∈ U, ∀ u m, ContDiffOn ℝ ∞ (f z u m) (V m))
    (hΦs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (Φ z m) (W m))
    (hmap : ∀ z ∈ U, ∀ m, MapsTo (Φ z m) (W m) (V m))
    (hchart : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, ∀ m x, x ∈ W m →
          ‖iteratedFDeriv ℝ n (Φ z m) x‖ ≤ e m * (1 + p ((n - 1) + dΦ) z)) :
    ∃ low' loss : ℕ,
      N07aSampleLinearJetBounds T K p q {z | z ∈ U ∧ p low' z ≤ 1}
        W w low' loss (fun z u m => f z u m ∘ Φ z m) := by
  classical
  let d := max low (max df dΦ)
  have hdl : low ≤ d := le_max_left _ _
  have hdf : df ≤ d := (le_max_left df dΦ).trans (le_max_right _ _)
  have hdΦ : dΦ ≤ d := (le_max_right df dΦ).trans (le_max_right _ _)
  obtain ⟨low', loss, hprod⟩ := n07a_finite_oneHigh_source_product p q hp hq hIp hIq d
  refine ⟨low', loss, fun a b c => ?_⟩
  let n := a + b
  choose e he he0 heb using fun k : OrderedFinpartition n =>
    hf.iteratedFDeriv hD hT hw hV hfs k.length c
  choose B hB hB0 hBb using fun k : OrderedFinpartition n =>
    fun j : Fin k.length => hchart (k.partSize j) (k.partSize_pos j)
  choose C hC hCb using fun k : OrderedFinpartition n =>
    hprod k.length (fun j => k.partSize j - 1) (c + k.length) (c + n)
      (by have hh := n07a_partition_source_order k; omega)
  let E₀ : OrderedFinpartition n → ℕ → ℝ :=
    fun k m => e k m * (∏ j, B k j m) * C k
  have hE (k : OrderedFinpartition n) : N07aSampleSubpower T K (E₀ k) :=
    N07aSampleSubpower.mul hD hT
      (N07aSampleSubpower.mul hD hT (he k)
        (N07aSampleSubpower.finset_prod hD hT Finset.univ (B k) (fun j _ => hB k j)))
      (N07aSampleSubpower.const hD hT (C k))
  have hE0 (k : OrderedFinpartition n) (m : ℕ) : 0 ≤ E₀ k m :=
    mul_nonneg (mul_nonneg (he0 k m) (Finset.prod_nonneg (fun j _ => hB0 k j m))) (hC k)
  refine ⟨fun m => ∑ k, E₀ k m,
    N07aSampleSubpower.finset_sum hD hT Finset.univ E₀ (fun k _ => hE k),
    fun m => Finset.sum_nonneg (fun k _ => hE0 k m), ?_⟩
  intro z hz u m x hx
  have houter (k : OrderedFinpartition n) :
      ‖iteratedFDeriv ℝ k.length (f z u m) (Φ z m x)‖ ≤ e k m * w c m *
        (q (c + k.length + d) u + (1 + p (c + k.length + d) z) * q d u) := by
    apply (heb k z hz.1 u m (Φ z m x) (hmap z hz.1 m hx)).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (he0 k m) (hw c m))
    exact add_le_add (hq (Nat.add_le_add_left hdf _) u)
      (mul_le_mul (add_le_add le_rfl (hp (Nat.add_le_add_left hdf _) z))
        (hq hdl u) (apply_nonneg _ _) (add_nonneg zero_le_one (apply_nonneg _ _)))
  have hcomp : ContDiffOn ℝ ∞ (f z u m ∘ Φ z m) (W m) :=
    (hfs z hz.1 u m).comp (hΦs z hz.1 m) (hmap z hz.1 m)
  apply (n07a_mixedDerivative_norm_le_iteratedFDeriv (hW m) hcomp a b hx).trans
  apply (norm_iteratedFDeriv_comp_le_partition_sum
    ((hfs z hz.1 u m).contDiffAt ((hV m).mem_nhds (hmap z hz.1 m hx)))
    ((hΦs z hz.1 m).contDiffAt ((hW m).mem_nhds hx)) n).trans
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  have hφ : (∏ j, ‖iteratedFDeriv ℝ (k.partSize j) (Φ z m) x‖) ≤
      (∏ j, B k j m) * (∏ j, (1 + p ((k.partSize j - 1) + d) z)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
    intro j _
    exact (hBb k j z hz.1 m x hx).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hp (Nat.add_le_add_left hdΦ _) z)) (hB0 k j m))
  have hbprod : 0 ≤ ∏ j, B k j m := Finset.prod_nonneg (fun j _ => hB0 k j m)
  have houter0 : 0 ≤ e k m * w c m *
      (q (c + k.length + d) u + (1 + p (c + k.length + d) z) * q d u) :=
    mul_nonneg (mul_nonneg (he0 k m) (hw c m))
      (add_nonneg (apply_nonneg _ _)
        (mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _)))
  calc
    _ ≤ (e k m * w c m *
        (q (c + k.length + d) u + (1 + p (c + k.length + d) z) * q d u)) *
          ((∏ j, B k j m) * (∏ j, (1 + p ((k.partSize j - 1) + d) z))) :=
      mul_le_mul (houter k) hφ (Finset.prod_nonneg (fun j _ => norm_nonneg _)) houter0
    _ = (e k m * (∏ j, B k j m) * w c m) *
        ((q (c + k.length + d) u + (1 + p (c + k.length + d) z) * q d u) *
          (∏ j, (1 + p ((k.partSize j - 1) + d) z))) := by ring
    _ ≤ (e k m * (∏ j, B k j m) * w c m) *
        (C k * (q (c + n + loss) u + (1 + p (c + n + loss) z) * q low' u)) :=
      mul_le_mul_of_nonneg_left (hCb k z hz.2 u)
        (mul_nonneg (mul_nonneg (he0 k m) hbprod) (hw c m))
    _ = _ := by dsimp only [E₀, n]; ring

end ContinuousFlexibility.Analysis
