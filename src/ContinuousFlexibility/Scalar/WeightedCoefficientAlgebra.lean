module

public import ContinuousFlexibility.Scalar.WeightedReferenceCoefficients
public import ContinuousFlexibility.Analysis.MaterialOrdinaryJets

/-!
# Coefficients with arbitrarily small material-envelope growth

Reference coefficient products are collected before charging an envelope
loss.  Bounds by every positive power of `M` are stable under all finite
products and differentiation.  Consequently a whole fixed coefficient
expression costs one power of `M`, independently of its number of factors.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

/-- Coefficient growth is measured after the actual material coordinate
pullback.  The exponent can be chosen after the derivative order. -/
def MaterialSubpower (T : MaterialData) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv n f x| ≤ C * T.M (T.radius x) ^ ε

theorem materialE0_rpow_le_subpowerM {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Ioo D.a D.b, T.E0 r ^ A ≤ C * T.M r ^ ε := by
  obtain ⟨C, hC, hb⟩ := hT.2.2.2.2.2.2.2.2.2.2.2.1 (A / ε)
  refine ⟨C ^ ε, Real.rpow_pos_of_pos hC _, fun r hr => ?_⟩
  have hE := (hT.2.1 r hr).2.2.1
  have hM : 0 ≤ T.M r := zero_le_one.trans (hT.2.1 r hr).2.2.2
  have h := Real.rpow_le_rpow (Real.rpow_pos_of_pos hE _).le (hb r hr) hε.le
  rwa [← Real.rpow_mul hE.le, div_mul_cancel₀ A hε.ne', Real.mul_rpow hC.le hM] at h

theorem referenceInverseJet_le_subpowerM {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ r ∈ Ioo D.a D.b,
      |radialJet n (fun t => (D.w t)⁻¹) r| ≤ K * T.M r ^ ε := by
  obtain ⟨B, hB⟩ := hD
  have hBn := hB.2.2.1 n
  obtain ⟨C, hC, hb⟩ := referenceCellCoefficient_le_materialM ⟨B, hB⟩ hT
    (div_nonneg hBn.le hε.le)
  refine ⟨B n * C ^ ε, mul_pos hBn (Real.rpow_pos_of_pos hC _), fun r hr => ?_⟩
  obtain ⟨m, hrm⟩ := hB.2.1.exists_cell hr
  have hE : 0 < radialE (D.cellIndex m) := Real.exp_pos _
  have hM : 0 ≤ T.M r := zero_le_one.trans (hT.2.1 r hr).2.2.2
  have h := Real.rpow_le_rpow (Real.rpow_pos_of_pos hE _).le (hb m r hrm) hε.le
  rw [← Real.rpow_mul hE.le, div_mul_cancel₀ (B n) hε.ne', Real.mul_rpow hC.le hM] at h
  calc
    _ ≤ B n * radialE (D.cellIndex m) ^ (B n) :=
      hB.2.2.2.2.2.2.2.2.2.1 m r hrm n
    _ ≤ B n * (C ^ ε * T.M r ^ ε) := mul_le_mul_of_nonneg_left h hBn.le
    _ = _ := (mul_assoc _ _ _).symm

theorem MaterialSubpower.deriv {T : MaterialData} {f : ℝ → ℝ}
    (hf : MaterialSubpower T f) : MaterialSubpower T (deriv f) := by
  refine ⟨(contDiff_infty_iff_deriv.mp hf.1).2, fun n ε hε => ?_⟩
  obtain ⟨C, hC, hb⟩ := hf.2 (n + 1) ε hε
  exact ⟨C, hC, fun x => by rw [← iteratedDeriv_succ']; exact hb x⟩

theorem MaterialSubpower.add {T : MaterialData} {f g : ℝ → ℝ}
    (hf : MaterialSubpower T f) (hg : MaterialSubpower T g) :
    MaterialSubpower T (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, fun n ε hε => ?_⟩
  obtain ⟨C, hC, hCb⟩ := hf.2 n ε hε
  obtain ⟨K, hK, hKb⟩ := hg.2 n ε hε
  refine ⟨C + K, add_nonneg hC hK, fun x => ?_⟩
  rw [iteratedDeriv_fun_add (hf.1.contDiffAt.of_le (by simp))
    (hg.1.contDiffAt.of_le (by simp))]
  exact (abs_add_le _ _).trans (by nlinarith only [hCb x, hKb x])

theorem MaterialSubpower.mul {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {f g : ℝ → ℝ}
    (hf : MaterialSubpower T f) (hg : MaterialSubpower T g) :
    MaterialSubpower T (fun x => f x * g x) := by
  classical
  refine ⟨hf.1.mul hg.1, fun n ε hε => ?_⟩
  have hfB (i : Fin (n + 1)) := hf.2 i.val (ε / 2) (half_pos hε)
  have hgB (i : Fin (n + 1)) := hg.2 (n - i.val) (ε / 2) (half_pos hε)
  choose A hA hAb using hfB
  choose B hB hBb using hgB
  let C (i : Fin (n + 1)) : ℝ := (n.choose i.val : ℝ) * A i * B i
  have hC (i : Fin (n + 1)) : 0 ≤ C i :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB i)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun x => ?_⟩
  have hM : 0 < T.M (T.radius x) := zero_lt_one.trans_le
    (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 x).1).2.2.2
  have hpow : T.M (T.radius x) ^ (ε / 2) * T.M (T.radius x) ^ (ε / 2) =
      T.M (T.radius x) ^ ε := by
    rw [← Real.rpow_add hM]
    congr 1
    ring
  let term (i : ℕ) : ℝ :=
    (n.choose i : ℝ) * iteratedDeriv i f x * iteratedDeriv (n - i) g x
  have hformula : iteratedDeriv n (fun t => f t * g t) x =
      ∑ i : Fin (n + 1), term i.val := by
    rw [Fin.sum_univ_eq_sum_range term]
    exact iteratedDeriv_mul (hf.1.contDiffAt.of_le (by simp)) (hg.1.contDiffAt.of_le (by simp))
  rw [hformula, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  dsimp only [term]
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n.choose i.val))]
  calc
    _ ≤ (n.choose i.val : ℝ) * (A i * T.M (T.radius x) ^ (ε / 2)) *
        (B i * T.M (T.radius x) ^ (ε / 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hAb i x) (Nat.cast_nonneg _))
        (hBb i x) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA i) (Real.rpow_pos_of_pos hM _).le))
    _ = C i * (T.M (T.radius x) ^ (ε / 2) * T.M (T.radius x) ^ (ε / 2)) := by
      dsimp only [C]
      ring
    _ = _ := by rw [hpow]

/-- A whole fixed coefficient expression uses one envelope power, after all
its products have been collected. -/
theorem MaterialSubpower.le_materialM {T : MaterialData} {f : ℝ → ℝ}
    (hf : MaterialSubpower T f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n f x| ≤ C * T.M (T.radius x) := by
  simpa only [Real.rpow_one] using hf.2 n 1 zero_lt_one

end ContinuousFlexibility.Statements
