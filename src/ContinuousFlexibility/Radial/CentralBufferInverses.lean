module

public import ContinuousFlexibility.Radial.CentralModelColumnInverse

/-!
# One finite full-model inverse bound for all positive even modes

The mode-two map is the actual true-column inverse. The higher modes
reuse the already proved central resolvent; adjoining their required
zero scalar does not enlarge its norm. No spectral inverse is reproved.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements

def centralUnborderedPairMap (R : RadialL2 →L[ℝ] RadialL2) :
    (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ) :=
  (R.comp (ContinuousLinearMap.fst ℝ RadialL2 ℝ)).prod 0

theorem centralUnborderedPairMap_apply (R : RadialL2 →L[ℝ] RadialL2)
    (F : RadialL2 × ℝ) :
    centralUnborderedPairMap R F = (R F.1, 0) := by
  simp only [centralUnborderedPairMap, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.zero_apply]

theorem centralUnborderedPairMap_norm_le (R : RadialL2 →L[ℝ] RadialL2) :
    ‖centralUnborderedPairMap R‖ ≤ ‖R‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro F
  rw [centralUnborderedPairMap_apply]
  change max ‖R F.1‖ ‖(0 : ℝ)‖ ≤ ‖R‖ * ‖F‖
  rw [norm_zero, max_eq_left (norm_nonneg _)]
  have hfst : ‖F.1‖ ≤ ‖F‖ := by
    change ‖F.1‖ ≤ max ‖F.1‖ ‖F.2‖
    exact le_max_left _ _
  exact (R.le_opNorm F.1).trans (mul_le_mul_of_nonneg_left hfst (norm_nonneg R))

theorem exists_centralUnborderedPairMap {V : ℝ → ℝ} {C : ℝ}
    (hR : WeakResolventBound V 0 C) (g : RadialL2) :
    ∃ H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ), ‖H‖ ≤ C ∧
      (∀ F, F.2 = 0 → BorderedFullGraph V g false (H F) F) ∧
      (∀ U F, BorderedFullGraph V g false U F → H F = U) := by
  obtain ⟨R, hnorm, hsolve, hunique⟩ := hR
  refine ⟨centralUnborderedPairMap R,
    (centralUnborderedPairMap_norm_le R).trans hnorm, ?_, ?_⟩
  · intro F hF
    rw [centralUnborderedPairMap_apply]
    change WeakSchrodingerGraph V (R F.1) F.1 ∧ (0 : ℝ) = 0 ∧ F.2 = 0
    exact ⟨by simpa only [zero_smul, add_zero] using hsolve F.1, rfl, hF⟩
  · intro U F hU
    have hu : WeakSchrodingerGraph V U.1 F.1 ∧ U.2 = 0 ∧ F.2 = 0 := by
      change WeakSchrodingerGraph V U.1 F.1 ∧ U.2 = 0 ∧ F.2 = 0 at hU
      exact hU
    rw [centralUnborderedPairMap_apply]
    apply Prod.ext
    · apply hunique U.1 F.1
      simpa only [zero_smul, add_zero] using hu.1
    · exact hu.2.1.symm

def centralModelBordered (n : ℕ) : Bool := if n = 1 then true else false

@[simp] theorem centralModelBordered_one : centralModelBordered 1 = true := rfl

theorem centralModelBordered_of_ne {n : ℕ} (hn : n ≠ 1) :
    centralModelBordered n = false := by
  simp only [centralModelBordered, if_neg hn]

/-- The same finite bound works for the actual true border at mode two
and all of the existing unbordered higher even resolvents. -/
theorem exists_central_even_full_inverse_bound (g : RadialL2)
    (hg : ⟪centralModelGroundVector, g⟫_ℝ ≠ 0) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ), ‖H‖ ≤ B₀ ∧
        (∀ F, (centralModelBordered n = false → F.2 = 0) →
          BorderedFullGraph (centralPotential (2 * (n : ℝ))) g
            (centralModelBordered n) (H F) F) ∧
        (∀ U F, BorderedFullGraph (centralPotential (2 * (n : ℝ))) g
          (centralModelBordered n) U F → H F = U) := by
  have hgap : 0 < 2 / centralGapDelta :=
    div_pos (by norm_num) centralGapDelta_pos
  refine ⟨‖centralModelColumnInverse g‖ + 2 / centralGapDelta + 1, by positivity, ?_⟩
  intro n hn
  by_cases hn1 : n = 1
  · subst n
    refine ⟨centralModelColumnInverse g, by linarith, ?_, ?_⟩
    · intro F _
      simpa only [Nat.cast_one, mul_one, centralModelBordered_one] using
        centralModelColumnInverse_solves g hg F
    · intro U F hU
      apply centralModelColumnInverse_unique g hg U F
      simpa only [Nat.cast_one, mul_one, centralModelBordered_one] using hU
  · have hn2 : 2 ≤ n := by omega
    obtain ⟨H, hnorm, hsolve, hunique⟩ :=
      exists_centralUnborderedPairMap (centralWeakResolventBound_statement n hn2) g
    refine ⟨H, ?_, ?_, ?_⟩
    · linarith [norm_nonneg (centralModelColumnInverse g)]
    · intro F hF
      have hzero : F.2 = 0 := hF (centralModelBordered_of_ne hn1)
      simpa only [centralModelBordered_of_ne hn1] using hsolve F hzero
    · intro U F hU
      apply hunique U F
      simpa only [centralModelBordered_of_ne hn1] using hU

end ContinuousFlexibility.Radial
