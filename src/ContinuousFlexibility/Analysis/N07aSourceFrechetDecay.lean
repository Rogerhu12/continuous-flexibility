module

public import ContinuousFlexibility.Analysis.N07aSourceJetDecay
public import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# Full physical source derivatives with the same fixed material loss

The actual mixed-jet bounds control the operator norm of each actual
Fréchet derivative. The finite coordinate sum changes only its constant.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

theorem n07a_iteratedFDeriv_decode_decay
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (n c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : A.Space) (p : PolarPoint), p ∈ annularOpen D →
      ‖iteratedFDeriv ℝ n (A.decode u) p‖ ≤
        C * T.H p.1 ^ γ * (T.M p.1 ^ c)⁻¹ * A.grading (n + c + 3) u := by
  classical
  choose B hB hBb using fun i : Fin (n + 1) =>
    n07a_mixedDerivative_decode_decay hT hA i.val (n - i.val) c
  let C : ℝ := ∑ i, B i
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => hB i)
  have hBC (i : Fin (n + 1)) : B i ≤ C :=
    Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)
  refine ⟨2 ^ n * C, mul_nonneg (pow_nonneg (by norm_num) _) hC,
    fun u p hp => ?_⟩
  have hH : 0 ≤ T.H p.1 ^ γ :=
    (Real.rpow_pos_of_pos (hT.2.1 _ hp.1).2.1 γ).le
  have hM : 0 ≤ (T.M p.1 ^ c)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (zero_le_one.trans (hT.2.1 _ hp.1).2.2.2) _)
  have hbound : 0 ≤ C * T.H p.1 ^ γ * (T.M p.1 ^ c)⁻¹ * A.grading (n + c + 3) u :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hH) hM) (apply_nonneg _ _)
  have h := norm_iteratedFDeriv_le_of_mixedDerivative
    (isOpen_Ioo.prod isOpen_univ) (hA.2.2.2.1 u).1 n hp hbound
    (fun a b hab => by
      let i : Fin (n + 1) := ⟨a, by omega⟩
      have hb : n - a = b := by omega
      have hbnd := hBb i u p hp
      change |mixedDerivative a (n - a) (A.decode u) p| ≤
        B i * T.H p.1 ^ γ * (T.M p.1 ^ c)⁻¹ * A.grading (a + (n - a) + c + 3) u at hbnd
      rw [hb, hab] at hbnd
      rw [Real.norm_eq_abs]
      exact hbnd.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hBC i) hH) hM)
        (apply_nonneg _ _)))
  exact h.trans_eq (by ring)

end ContinuousFlexibility.Analysis
