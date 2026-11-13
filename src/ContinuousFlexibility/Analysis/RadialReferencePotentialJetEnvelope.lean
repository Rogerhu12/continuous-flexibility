import ContinuousFlexibility.Analysis.OneHighCompositionJets

/-!
# Finite jets of the actual radial reference potential

The potential is a product of a composed height and the derivative of
the composed physical flux. The partition formula uses only positive
jets of the inverse coordinate. Its zeroth value is used solely as the
point at which the physical profile jets are evaluated.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff BigOperators

theorem referencePotential_product_envelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {A B : ℝ}, 0 ≤ A → 0 ≤ B →
      ∀ (f g : ℝ → ℝ) (x : ℝ), ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ g x →
      (∀ j, j ≤ N → |iteratedDeriv j f x| ≤ A) →
      (∀ j, j ≤ N → |iteratedDeriv j g x| ≤ B) →
      ∀ k, k ≤ N → |iteratedDeriv k (fun t => f t * g t) x| ≤ C * A * B := by
  classical
  let D (k : ℕ) : ℝ := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)
  have hD (k : ℕ) : 0 ≤ D k := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  let C : ℝ := 1 + ∑ k ∈ Finset.range (N + 1), D k
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hD k)
  have hDC (k : ℕ) (hk : k ≤ N) : D k ≤ C :=
    (Finset.single_le_sum (fun j _ => hD j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans
        (le_add_of_nonneg_left zero_le_one)
  refine ⟨C, hC, ?_⟩
  intro A B hA hB f g x hf hg hfj hgj k hk
  rw [iteratedDeriv_fun_mul (hf.of_le (by simp)) (hg.of_le (by simp))]
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1),
        |(k.choose j : ℝ) * iteratedDeriv j f x * iteratedDeriv (k - j) g x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfj j (hjk.trans hk)) (Nat.cast_nonneg _))
        (hgj (k - j) ((Nat.sub_le k j).trans hk)) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = D k * A * B := by dsimp only [D]; rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ C * A * B := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hDC k hk) hA) hB

theorem referencePotential_composition_envelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {A B : ℝ}, 0 ≤ A → 1 ≤ B →
      ∀ (f g : ℝ → ℝ) (x : ℝ),
      ContDiffAt ℝ ∞ f (g x) → ContDiffAt ℝ ∞ g x →
      (∀ j, j ≤ N → |iteratedDeriv j f (g x)| ≤ A) →
      (∀ j, 1 ≤ j → j ≤ N → |iteratedDeriv j g x| ≤ B) →
      ∀ k, k ≤ N → |iteratedDeriv k (f ∘ g) x| ≤ C * A * B ^ N := by
  classical
  let D (k : ℕ) : ℝ := Fintype.card (OrderedFinpartition k)
  have hD (k : ℕ) : 0 ≤ D k := Nat.cast_nonneg _
  let C : ℝ := 1 + ∑ k ∈ Finset.range (N + 1), D k
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hD k)
  have hDC (k : ℕ) (hk : k ≤ N) : D k ≤ C :=
    (Finset.single_le_sum (fun j _ => hD j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans
        (le_add_of_nonneg_left zero_le_one)
  refine ⟨C, hC, ?_⟩
  intro A B hA hB f g x hf hg hfj hgj k hk
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hstart := norm_iteratedDeriv_comp_le_partition_sum hf hg k
  simp only [Real.norm_eq_abs] at hstart
  apply hstart.trans
  calc
    _ ≤ ∑ c : OrderedFinpartition k, A * B ^ N := by
      apply Finset.sum_le_sum
      intro c _
      have hp : (∏ j, |iteratedDeriv (c.partSize j) g x|) ≤ B ^ N := by
        calc
          _ ≤ ∏ _j : Fin c.length, B :=
            Finset.prod_le_prod₀ (s := Finset.univ)
              (f := fun j : Fin c.length => |iteratedDeriv (c.partSize j) g x|)
              (g := fun _ : Fin c.length => B)
              (fun _ _ => abs_nonneg _)
              (fun j _ => hgj _ (c.partSize_pos j) ((c.partSize_le j).trans hk))
          _ = B ^ c.length := by simp
          _ ≤ B ^ N := pow_le_pow_right₀ hB (c.length_le.trans hk)
      exact mul_le_mul (hfj c.length (c.length_le.trans hk)) hp
        (Finset.prod_nonneg fun _ _ => abs_nonneg _) hA
    _ = D k * (A * B ^ N) := by simp only [D, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    _ ≤ C * (A * B ^ N) := mul_le_mul_of_nonneg_right (hDC k hk)
      (mul_nonneg hA (pow_nonneg hB0 N))
    _ = C * A * B ^ N := by ring

/-- Actual finite profile, height, and positive inverse-coordinate jets
bound the flux form of the reference potential. The coefficient is
chosen before all functions, envelopes and evaluation points. -/
theorem exists_radialReferencePotential_jet_envelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {P M : ℝ}, 0 ≤ P → 1 ≤ M →
      ∀ (w H χ : ℝ → ℝ) (x : ℝ),
      ContDiff ℝ ∞ w → ContDiff ℝ ∞ H → ContDiff ℝ ∞ χ →
      (∀ k, k ≤ N + 1 → |iteratedDeriv k w (χ x)| ≤ P) →
      (∀ k, k ≤ N + 2 → |iteratedDeriv k H (χ x)| ≤ M) →
      (∀ k, 1 ≤ k → k ≤ N + 1 → |iteratedDeriv k χ x| ≤ M) →
      |iteratedDeriv N
        (fun t => -(H (χ t) * deriv ((fun r => w r * deriv H r) ∘ χ) t)) x| ≤
          C * P * M ^ (2 * N + 3) := by
  obtain ⟨CP, hCP, hprod⟩ := referencePotential_product_envelope N
  obtain ⟨CP1, hCP1, hprod1⟩ := referencePotential_product_envelope (N + 1)
  obtain ⟨CC, hCC, hcomp⟩ := referencePotential_composition_envelope N
  obtain ⟨CC1, hCC1, hcomp1⟩ := referencePotential_composition_envelope (N + 1)
  let C : ℝ := CP * CC * CC1 * CP1
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hCP hCC) hCC1) hCP1
  refine ⟨C, hC, ?_⟩
  intro P M hP hM w H χ x hw hH hχ hwj hHj hχj
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hHd : ContDiff ℝ ∞ (deriv H) := (contDiff_infty_iff_deriv.mp hH).2
  let F : ℝ → ℝ := fun r => w r * deriv H r
  have hF : ContDiff ℝ ∞ F := hw.mul hHd
  have hFj (k : ℕ) (hk : k ≤ N + 1) :
      |iteratedDeriv k F (χ x)| ≤ CP1 * P * M := by
    apply hprod1 hP hM0 w (deriv H) (χ x) hw.contDiffAt hHd.contDiffAt hwj _ k hk
    intro j hj
    rw [← iteratedDeriv_succ']
    exact hHj (j + 1) (by omega)
  have hHcomp (k : ℕ) (hk : k ≤ N) :
      |iteratedDeriv k (H ∘ χ) x| ≤ CC * M * M ^ N :=
    hcomp hM0 hM H χ x hH.contDiffAt hχ.contDiffAt
      (fun j hj => hHj j (by omega))
      (fun j hj hjN => hχj j hj (by omega)) k hk
  have hFbound : 0 ≤ CP1 * P * M :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hCP1) hP) hM0
  have hFdcomp (k : ℕ) (hk : k ≤ N) :
      |iteratedDeriv k (deriv (F ∘ χ)) x| ≤ CC1 * (CP1 * P * M) * M ^ (N + 1) := by
    rw [← iteratedDeriv_succ']
    exact hcomp1 hFbound hM F χ x hF.contDiffAt hχ.contDiffAt hFj hχj
      (k + 1) (by omega)
  have hA : 0 ≤ CC * M * M ^ N :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hCC) hM0) (pow_nonneg hM0 N)
  have hB : 0 ≤ CC1 * (CP1 * P * M) * M ^ (N + 1) :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hCC1) hFbound) (pow_nonneg hM0 _)
  have hb := hprod hA hB (H ∘ χ) (deriv (F ∘ χ)) x
    (hH.comp hχ).contDiffAt
    (contDiff_infty_iff_deriv.mp (hF.comp hχ)).2.contDiffAt
    hHcomp hFdcomp N le_rfl
  rw [iteratedDeriv_fun_neg, abs_neg]
  apply hb.trans_eq
  have hpower : M ^ N * M ^ (N + 1) * M ^ 2 = M ^ (2 * N + 3) := by
    rw [← pow_add, ← pow_add]
    congr 1 <;> omega
  calc
    _ = C * P * (M ^ N * M ^ (N + 1) * M ^ 2) := by dsimp only [C]; ring
    _ = _ := by rw [hpower]

end ContinuousFlexibility.Analysis
