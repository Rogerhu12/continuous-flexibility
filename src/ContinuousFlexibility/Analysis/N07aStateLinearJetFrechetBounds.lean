module

public import ContinuousFlexibility.Analysis.N07aStateSampleLinearJets
public import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# Fréchet norms of the genuine source-linear mixed jets
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

theorem N07aStateSampleLinearJetBounds.iteratedFDeriv
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} {W : E → ℕ → Set PolarPoint} {w : ℕ → ℕ → ℝ}
    {low loss : ℕ} {f : E → F → ℕ → PolarPoint → ℝ}
    (hf : N07aStateSampleLinearJetBounds T K p q U W w low loss f)
    (hw : ∀ c m, 0 ≤ w c m) (hW : ∀ z ∈ U, ∀ m, IsOpen (W z m))
    (hfs : ∀ z ∈ U, ∀ u m, ContDiffOn ℝ ∞ (f z u m) (W z m)) (n c : ℕ) :
    ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      ∀ z ∈ U, ∀ u m x, x ∈ W z m →
        ‖iteratedFDeriv ℝ n (f z u m) x‖ ≤ e m * w c m *
          (q (c + n + loss) u + (1 + p (c + n + loss) z) * q low u) := by
  classical
  choose e he he0 heb using fun i : Fin (n + 1) => hf i.val (n - i.val) c
  let A : ℕ → ℝ := fun m => ∑ i, e i m
  have hA : N07aSampleSubpower T K A :=
    N07aSampleSubpower.finset_sum hD hT Finset.univ e (fun i _ => he i)
  have hA0 (m : ℕ) : 0 ≤ A m := Finset.sum_nonneg (fun i _ => he0 i m)
  have hiA (i : Fin (n + 1)) (m : ℕ) : e i m ≤ A m :=
    Finset.single_le_sum (fun j _ => he0 j m) (Finset.mem_univ i)
  refine ⟨fun m => 2 ^ n * A m,
    N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT (2 ^ n)) hA,
    fun m => mul_nonneg (pow_nonneg (by norm_num) _) (hA0 m), ?_⟩
  intro z hz u m x hx
  let B := q (c + n + loss) u + (1 + p (c + n + loss) z) * q low u
  have hB : 0 ≤ B :=
    add_nonneg (apply_nonneg _ _)
      (mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _))
  have hb := norm_iteratedFDeriv_le_of_mixedDerivative (hW z hz m) (hfs z hz u m) n hx
    (mul_nonneg (mul_nonneg (hA0 m) (hw c m)) hB) (fun a b hab => by
      let i : Fin (n + 1) := ⟨a, by omega⟩
      have hnb : n - a = b := by omega
      have hh := heb i z hz u m x hx
      change |mixedDerivative a (n - a) (f z u m) x| ≤ e i m * w c m *
        (q (c + (a + (n - a)) + loss) u +
          (1 + p (c + (a + (n - a)) + loss) z) * q low u) at hh
      rw [hnb, hab] at hh
      rw [Real.norm_eq_abs]
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hiA i m) (hw c m)) hB))
  exact hb.trans_eq (by dsimp only [B]; ring)

end ContinuousFlexibility.Analysis
