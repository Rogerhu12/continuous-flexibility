import ContinuousFlexibility.Analysis.N07aSampleJetBounds
import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# Fréchet operator norms of the actual sampled scalar jets
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

theorem N07aSampleJetBounds.iteratedFDeriv
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {p : ℕ → Seminorm ℝ E} {U : Set E} {W : ℕ → Set PolarPoint}
    {d : ℕ} {f : E → ℕ → PolarPoint → ℝ}
    (hf : N07aSampleJetBounds T K p U W d f)
    (hW : ∀ m, IsOpen (W m))
    (hfs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (f z m) (W m)) (n : ℕ) :
    ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      ∀ z ∈ U, ∀ m x, x ∈ W m →
        ‖iteratedFDeriv ℝ n (f z m) x‖ ≤ e m * (1 + p (n + d) z) := by
  classical
  choose e he he0 heb using fun i : Fin (n + 1) => hf i.val (n - i.val)
  let E : ℕ → ℝ := fun m => ∑ i, e i m
  have hE : N07aSampleSubpower T K E :=
    N07aSampleSubpower.finset_sum hD hT Finset.univ e (fun i _ => he i)
  have hE0 (m : ℕ) : 0 ≤ E m := Finset.sum_nonneg (fun i _ => he0 i m)
  have hiE (i : Fin (n + 1)) (m : ℕ) : e i m ≤ E m :=
    Finset.single_le_sum (fun j _ => he0 j m) (Finset.mem_univ i)
  refine ⟨fun m => 2 ^ n * E m,
    N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT (2 ^ n)) hE,
    fun m => mul_nonneg (pow_nonneg (by norm_num) _) (hE0 m), ?_⟩
  intro z hz m x hx
  have hP : 0 ≤ 1 + p (n + d) z := add_nonneg zero_le_one (apply_nonneg _ _)
  have hb := norm_iteratedFDeriv_le_of_mixedDerivative (hW m) (hfs z hz m) n hx
    (mul_nonneg (hE0 m) hP) (fun a b hab => by
      let i : Fin (n + 1) := ⟨a, by omega⟩
      have hnb : n - a = b := by omega
      have hh := heb i z hz m x hx
      change |mixedDerivative a (n - a) (f z m) x| ≤
        e i m * (1 + p (a + (n - a) + d) z) at hh
      rw [hnb, hab] at hh
      rw [Real.norm_eq_abs]
      exact hh.trans (mul_le_mul_of_nonneg_right (hiE i m) hP))
  exact hb.trans_eq (by ring)

end ContinuousFlexibility.Analysis
