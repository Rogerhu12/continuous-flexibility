import ContinuousFlexibility.Analysis.N07aStateSampleFrechetBounds
import ContinuousFlexibility.Analysis.N07aStateSampleJetProducts
import ContinuousFlexibility.Analysis.N07aCompositionBudget

/-! Composition estimates on the actual state-dependent source domain. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}

theorem n07a_stateSampleJetBounds_comp
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hIp : HasSmoothing p)
    (U : Set E) (W V : E → ℕ → Set PolarPoint)
    (hW : ∀ z ∈ U, ∀ m, IsOpen (W z m))
    (hV : ∀ z ∈ U, ∀ m, IsOpen (V z m))
    (f : E → ℕ → PolarPoint → ℝ) (Φ : E → ℕ → PolarPoint → PolarPoint)
    (df dΦ : ℕ) (hf : N07aStateSampleJetBounds T K p U V df f)
    (hfs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (f z m) (V z m))
    (hΦs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (Φ z m) (W z m))
    (hmap : ∀ z ∈ U, ∀ m, MapsTo (Φ z m) (W z m) (V z m))
    (hchart : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, ∀ m x, x ∈ W z m →
          ‖iteratedFDeriv ℝ n (Φ z m) x‖ ≤ e m * (1 + p ((n - 1) + dΦ) z)) :
    ∃ low loss : ℕ,
      N07aStateSampleJetBounds T K p {z | z ∈ U ∧ p low z ≤ 1}
        W loss (fun z m => f z m ∘ Φ z m) := by
  classical
  let d := max df dΦ
  obtain ⟨low, loss, hprod⟩ := n07a_finite_state_product p hp hIp d
  refine ⟨low, loss, fun a b => ?_⟩
  let n := a + b
  choose e he he0 heb using fun k : OrderedFinpartition n =>
    hf.iteratedFDeriv hD hT hV hfs k.length
  choose B hB hB0 hBb using fun k : OrderedFinpartition n =>
    fun j : Fin k.length => hchart (k.partSize j) (k.partSize_pos j)
  have hbudget (k : OrderedFinpartition n) :
      (∑ j : Fin (k.length + 1), (Fin.cons k.length (fun i => k.partSize i - 1)) j) ≤ n := by
    simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using
      (n07a_partition_source_order k).le
  choose C hC hCb using fun k : OrderedFinpartition n =>
    hprod (k.length + 1) (Fin.cons k.length (fun j => k.partSize j - 1)) n (hbudget k)
  let A : OrderedFinpartition n → ℕ → ℝ := fun k m => e k m * (∏ j, B k j m) * C k
  have hA (k : OrderedFinpartition n) : N07aSampleSubpower T K (A k) :=
    N07aSampleSubpower.mul hD hT
      (N07aSampleSubpower.mul hD hT (he k)
        (N07aSampleSubpower.finset_prod hD hT Finset.univ (B k) (fun j _ => hB k j)))
      (N07aSampleSubpower.const hD hT (C k))
  have hA0 (k : OrderedFinpartition n) (m : ℕ) : 0 ≤ A k m :=
    mul_nonneg (mul_nonneg (he0 k m) (Finset.prod_nonneg (fun j _ => hB0 k j m))) (hC k)
  refine ⟨fun m => ∑ k, A k m,
    N07aSampleSubpower.finset_sum hD hT Finset.univ A (fun k _ => hA k),
    fun m => Finset.sum_nonneg (fun k _ => hA0 k m), ?_⟩
  intro z hz m x hx
  have hcomp := (hfs z hz.1 m).comp (hΦs z hz.1 m) (hmap z hz.1 m)
  apply (n07a_mixedDerivative_norm_le_iteratedFDeriv (hW z hz.1 m) hcomp a b hx).trans
  apply (norm_iteratedFDeriv_comp_le_partition_sum
    ((hfs z hz.1 m).contDiffAt ((hV z hz.1 m).mem_nhds (hmap z hz.1 m hx)))
    ((hΦs z hz.1 m).contDiffAt ((hW z hz.1 m).mem_nhds hx)) n).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  have houter : ‖iteratedFDeriv ℝ k.length (f z m) (Φ z m x)‖ ≤
      e k m * (1 + p (k.length + d) z) :=
    (heb k z hz.1 m _ (hmap z hz.1 m hx)).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_left _ _) _) z)) (he0 k m))
  have hφ : (∏ j, ‖iteratedFDeriv ℝ (k.partSize j) (Φ z m) x‖) ≤
      (∏ j, B k j m) * (∏ j, (1 + p ((k.partSize j - 1) + d) z)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
    intro j _
    exact (hBb k j z hz.1 m x hx).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_right _ _) _) z)) (hB0 k j m))
  have hproduct : (1 + p (k.length + d) z) *
      (∏ j, (1 + p ((k.partSize j - 1) + d) z)) ≤ C k * (1 + p (n + loss) z) := by
    simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] using hCb k z hz.2
  calc
    _ ≤ (e k m * (1 + p (k.length + d) z)) *
        ((∏ j, B k j m) * (∏ j, (1 + p ((k.partSize j - 1) + d) z))) :=
      mul_le_mul houter hφ (Finset.prod_nonneg (fun j _ => norm_nonneg _))
        (mul_nonneg (he0 k m) (add_nonneg zero_le_one (apply_nonneg _ _)))
    _ = (e k m * (∏ j, B k j m)) *
        ((1 + p (k.length + d) z) * (∏ j, (1 + p ((k.partSize j - 1) + d) z))) := by ring
    _ ≤ (e k m * (∏ j, B k j m)) * (C k * (1 + p (n + loss) z)) :=
      mul_le_mul_of_nonneg_left hproduct
        (mul_nonneg (he0 k m) (Finset.prod_nonneg (fun j _ => hB0 k j m)))
    _ = _ := by dsimp only [A, n]; ring

end ContinuousFlexibility.Analysis
