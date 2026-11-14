module

public import ContinuousFlexibility.Analysis.N04SourceColumnsScalarComposition
public import ContinuousFlexibility.Analysis.ScalarRpowJetGrowth
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Positive powers of the actual divided radial coordinate

The value interval is allowed to vary by material powers. Its lower
endpoint controls the true scalar power derivatives explicitly. The
finite scalar chain rule then preserves the state neighborhood, the low
seminorm and a single positive-state height factor.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- One material envelope bounds every scalar outer jet in the prefix.
No compactness constant depending on the selected component is used. -/
theorem n04NegativeChart_rpow_outerJets_material_bound
    {l A P Q : ℝ} (hl : 0 < l) (hA : 0 ≤ A) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (r : ℝ) (N : ℕ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ E t : ℝ, 1 ≤ E →
      l * E ^ (-P) ≤ t → t ≤ A * E ^ Q →
      ∀ a b : ℕ, a + b ≤ N →
        ‖iteratedFDeriv ℝ a (iteratedDeriv b (fun u : ℝ => u ^ r)) t‖ ≤ C * E ^ D := by
  classical
  choose c d hc hd hb using fun n : Fin (N + 1) =>
    iteratedDeriv_rpow_polynomial_bound hl hA hP hQ r n.val
  let C : ℝ := ∑ n : Fin (N + 1), c n
  let D : ℝ := ∑ n : Fin (N + 1), d n
  have hC : 0 ≤ C := Finset.sum_nonneg (fun n _ => hc n)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun n _ => hd n)
  refine ⟨C, D, hC, hD, fun E t hE hlo hhi a b hab => ?_⟩
  let n : Fin (N + 1) := ⟨a + b, by omega⟩
  have hcC : c n ≤ C := Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ n)
  have hdD : d n ≤ D := Finset.single_le_sum (fun i _ => hd i) (Finset.mem_univ n)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    n04SourceColumns_iteratedDeriv_add, Real.norm_eq_abs]
  exact (hb n E t hE hlo hhi).trans
    (mul_le_mul hcC (Real.rpow_le_rpow_of_exponent_le hE hdD)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) hC)

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- A genuine positive power retains the finite parameter cost in the
high order. The constants precede all actual components and towers. -/
theorem n04NegativeChart_positivePower_positive_oneHigh
    (K s shift : ℕ) (RH r : ℝ)
    {l A P Q Cf Af : ℝ}
    (hl : 0 < l) (hA : 0 ≤ A) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hCf : 0 ≤ Cf) (hAf : 0 ≤ Af) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (p : ℕ → Seminorm ℝ X) (center : X) (base high : ℕ),
      ∀ (U : Set X), IsOpen U → ∀ (Ω : Set PolarPoint), IsOpen Ω →
      ∀ f : X → PolarPoint → ℝ, ∀ F : MixedJetRegularity U Ω f,
      (∀ y ∈ U, ∀ q ∈ Ω, 0 < f y q) →
      ∀ q (hq : q ∈ Ω), ∀ E H : ℝ, 1 ≤ E → 0 ≤ H → H ≤ RH →
      ∀ x ∈ U, p base (x - center) ≤ 1 →
      l * E ^ (-P) ≤ f x q → f x q ≤ A * E ^ Q →
      (∀ j : ℕ, j ≤ K → ∀ u w : ℕ, u + w ≤ s →
        ∀ z : Fin j → X, (∀ i, p base (z i) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R → (∀ i, p high (z i) ≤ R) →
        ‖(F.parameter u w q hq).D j x z‖ ≤ Cf * E ^ Af * parameterHeightWeight H j *
          R ^ (((u + w + shift * j : ℕ) : ℝ) /
            (((s + shift * K : ℕ) : ℝ) + 1))) →
      ∀ k : ℕ, k ≤ K → 0 < k → ∀ a b : ℕ, a + b ≤ s →
      ∀ J : SmoothDirections U (fun y => mixedDerivative a b (fun z => f y z ^ r) q),
      ∀ v : Fin k → X, ‖J.D k x v‖ ≤ B * E ^ B * H *
        oneHighVariationWeight p base high (x - center) v := by
  obtain ⟨Co, Ao, hCo, hAo, houter⟩ :=
    n04NegativeChart_rpow_outerJets_material_bound hl hA hP hQ r (K + s)
  obtain ⟨C, hC, hcomp⟩ :=
    n04SourceColumns_scalarComposition_positive_oneHigh (X := X) K s shift RH
  let M₀ : ℝ := 1 + Co + Cf
  let A₀ : ℝ := Ao + Af
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack
    (C * M₀ ^ (K + s + 1)) (A₀ * (K + s + 1 : ℕ))
  refine ⟨B, hB, fun p center base high U hU Ω hΩ f F hpos q hq E H hE hH hHR
    x hx hlow hlo hhi hraw k hk hkpos a b hab J v => ?_⟩
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  let M : ℝ := M₀ * E ^ A₀
  have hM₀ : 1 ≤ M₀ := by dsimp only [M₀]; linarith only [hCo, hCf]
  have hA₀ : 0 ≤ A₀ := add_nonneg hAo hAf
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hM₀ (Real.one_le_rpow hE hA₀)
  have hCoM : Co * E ^ Ao ≤ M :=
    mul_le_mul (by dsimp only [M₀]; linarith only [hCf])
      (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_right hAf))
      (Real.rpow_nonneg hEpos.le _) (zero_le_one.trans hM₀)
  have hCfM : Cf * E ^ Af ≤ M :=
    mul_le_mul (by dsimp only [M₀]; linarith only [hCo])
      (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_left hAo))
      (Real.rpow_nonneg hEpos.le _) (zero_le_one.trans hM₀)
  have hg : ContDiffOn ℝ ∞ (fun t : ℝ => t ^ r) (Ioi (0 : ℝ)) :=
    fun t ht => (Real.contDiffAt_rpow_const_of_ne (ne_of_gt ht)).contDiffWithinAt
  have hb := hcomp p center base high U hU Ω hΩ (Ioi (0 : ℝ)) isOpen_Ioi
    f (fun t : ℝ => t ^ r) F hg (fun y hy z hz => hpos y hy z hz)
    q hq H M hH hHR hM x hx hlow
    (fun m hm j hj => (houter E (f x q) hE hlo hhi j m (by omega)).trans hCoM)
    (fun j hj u w huw z hz R hR hxR hzR => (hraw j hj u w huw z hz R hR hxR hzR).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCfM (parameterHeightWeight_nonneg hH j))
        (Real.rpow_nonneg (zero_le_one.trans hR) _)))
    k hk hkpos a b hab J v
  have hcoef : C * M ^ (K + s + 1) ≤ B * E ^ B := by
    calc
      _ = (C * M₀ ^ (K + s + 1)) * E ^ (A₀ * (K + s + 1 : ℕ)) := by
        dsimp only [M]
        rw [mul_pow, ← Real.rpow_mul_natCast hEpos.le A₀ (K + s + 1)]
        ring
      _ ≤ _ := hpack E hE
  exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hH)
    (oneHighVariationWeight_nonneg p base high (x - center) v))

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_positivePower_positive_oneHigh'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_positivePower_positive_oneHigh
