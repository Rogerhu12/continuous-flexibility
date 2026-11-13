import ContinuousFlexibility.Analysis.N04RealizationFiniteScalarComposition
import ContinuousFlexibility.Analysis.N04RealizationParameterRescale
import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization
import ContinuousFlexibility.Analysis.N01cOuterDenominatorJets

/-!
# Scalar kernels with a finite parameter cost

Direction rescaling pays the parameter-order interpolation cost only once,
at the total output order. Normalizing the genuine output multilinear map
then leaves one high seminorm and preserves the positive parameter height
factor. The original low order, spatial domain, and parameter neighborhood
are retained throughout.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Iterating scalar derivatives adds their two orders. -/
theorem n04SourceColumns_iteratedDeriv_add (f : ℝ → ℝ) (a b : ℕ) :
    iteratedDeriv a (iteratedDeriv b f) = iteratedDeriv (a + b) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

/-- The normalized reciprocal has uniformly bounded outer derivatives
through any mixed scalar prefix on the same fixed compact interval. -/
theorem n04SourceColumns_inverse_outerJets_bound (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ),
      ∀ a b : ℕ, a + b ≤ N →
        ‖iteratedFDeriv ℝ a (iteratedDeriv b (fun u : ℝ => u⁻¹)) t‖ ≤ C := by
  obtain ⟨B, hB, hb⟩ := normalizedDenominator_outerJets_bound N
  refine ⟨max 1 B, le_max_left _ _, fun t ht a b hab => ?_⟩
  have h := (hb (a + b) hab t ht).1
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    n04SourceColumns_iteratedDeriv_add]
  apply le_trans _ (le_max_right 1 B)
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Nat.add_comm] using h

/-- The equivalent kernel on the relative error is smooth at every point
of its fixed compact range and has uniform scalar outer jets. -/
theorem n04SourceColumns_shiftedInverse_outerJets_bound (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ),
      ∀ a b : ℕ, a + b ≤ N →
        ‖iteratedFDeriv ℝ a (iteratedDeriv b (fun u : ℝ => (1 + u)⁻¹)) t‖ ≤ C := by
  have hreg : ∀ t ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ),
      ContDiffAt ℝ ∞ (fun u : ℝ => (1 + u)⁻¹) t := by
    intro t ht
    have hpos : 0 < 1 + t := by linarith [ht.1]
    exact (contDiffAt_const.add contDiffAt_id).inv hpos.ne'
  obtain ⟨B, hB, hb⟩ := compact_iteratedFDeriv_bound isCompact_Icc hreg N
  refine ⟨max 1 B, le_max_left _ _, fun t ht a b hab => ?_⟩
  have h := hb (a + b) hab t ht
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    n04SourceColumns_iteratedDeriv_add]
  apply le_trans _ (le_max_right 1 B)
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Nat.add_comm] using h

/-- The finite scalar chain rule with an interpolation cost for each
parameter slot. All constants precede the functions and numerical data. -/
theorem n04SourceColumns_scalarComposition_shifted_bound (k a b : ℕ) (RH : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (U : Set X), IsOpen U → ∀ (Ω : Set PolarPoint), IsOpen Ω →
      ∀ (V : Set ℝ), IsOpen V → ∀ (f : X → PolarPoint → ℝ) (g : ℝ → ℝ),
      ∀ F : MixedJetRegularity U Ω f, ContDiffOn ℝ ∞ g V →
      (∀ y ∈ U, MapsTo (f y) Ω V) →
      ∀ q (hq : q ∈ Ω), ∀ J : SmoothDirections U
        (fun y => mixedDerivative a b (fun p => g (f y p)) q),
      ∀ x ∈ U, ∀ (P : X → Prop) (v : Fin k → X), (∀ i, P (v i)) →
      ∀ H M R : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ M → 1 ≤ R →
      ∀ budget shift : ℕ,
      (∀ m : ℕ, m ≤ a + b → ∀ j : ℕ, j ≤ k →
        ‖iteratedFDeriv ℝ j (iteratedDeriv m g) (f x q)‖ ≤ M) →
      (∀ j : ℕ, j ≤ k → ∀ u w : ℕ, u + w ≤ a + b →
        ∀ z : Fin j → X, (∀ i, P (z i)) →
        ‖(F.parameter u w q hq).D j x z‖ ≤
          M * parameterHeightWeight H j *
            R ^ (((u + w + shift * j : ℕ) : ℝ) / ((budget : ℝ) + 1))) →
      ‖J.D k x v‖ ≤ B * M ^ (k + a + b + 1) * parameterHeightWeight H k *
        R ^ (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) := by
  obtain ⟨B, hB, hb⟩ := n04Realization_finiteScalarComposition_bound (X := X) k a b RH
  refine ⟨B, hB, ?_⟩
  intro U hU Ω hΩ V hV f g F hg hmap q hq J x hx P v hv H M R hH hHR hM hR
    budget shift houter hraw
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let α : ℝ := (shift : ℝ) / ((budget : ℝ) + 1)
  let t : ℝ := R ^ (1 / ((budget : ℝ) + 1))
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have htpow (n : ℕ) : t ^ n = R ^ ((n : ℝ) / ((budget : ℝ) + 1)) := by
    dsimp only [t]
    rw [← Real.rpow_mul_natCast hRpos.le]
    congr 1
    ring
  have hcancel (w : X) : R ^ α • (R ^ (-α) • w) = w := by
    rw [smul_smul, ← Real.rpow_add hRpos, add_neg_cancel, Real.rpow_zero, one_smul]
  have hcancel' (w : X) : R ^ (-α) • (R ^ α • w) = w := by
    rw [smul_smul, ← Real.rpow_add hRpos, neg_add_cancel, Real.rpow_zero, one_smul]
  let P' : X → Prop := fun w => P (R ^ α • w)
  let v' : Fin k → X := fun i => R ^ (-α) • v i
  have hv' (i : Fin k) : P' (v' i) := by
    change P (R ^ α • (R ^ (-α) • v i))
    rw [hcancel]
    exact hv i
  have hraw' (j : ℕ) (hj : j ≤ k) (u w : ℕ) (huw : u + w ≤ a + b)
      (z : Fin j → X) (hz : ∀ i, P' (z i)) :
      ‖(F.parameter u w q hq).D j x z‖ ≤
        M * parameterHeightWeight H j * t ^ (u + w) := by
    let z₀ : Fin j → X := fun i => R ^ α • z i
    have hz₀ (i : Fin j) : P (z₀ i) := hz i
    have hr := hraw j hj u w huw z₀ hz₀
    have hexp : (((u + w + shift * j : ℕ) : ℝ) / ((budget : ℝ) + 1)) =
        ((u + w : ℕ) : ℝ) / ((budget : ℝ) + 1) + α * (j : ℝ) := by
      dsimp only [α]
      push_cast
      ring
    rw [hexp] at hr
    have hs := n04Realization_parameter_rescale_bound ((F.parameter u w q hq).D j x)
      z₀ hRpos α (((u + w : ℕ) : ℝ) / ((budget : ℝ) + 1))
      (M * parameterHeightWeight H j) hr
    have hz_eq : (fun i => R ^ (-α) • z₀ i) = z := by
      funext i
      exact hcancel' (z i)
    rw [hz_eq] at hs
    rw [htpow]
    exact hs
  have hs := hb U hU Ω hΩ V hV f g F hg hmap q hq J x hx P' v' hv'
    H M t hH hHR hM ht houter hraw'
  rw [htpow] at hs
  have hout := n04Realization_parameter_unscale_bound (J.D k x) v hRpos α
    (((a + b : ℕ) : ℝ) / ((budget : ℝ) + 1))
    (B * M ^ (k + a + b + 1) * parameterHeightWeight H k) hs
  have hexp : (((a + b : ℕ) : ℝ) / ((budget : ℝ) + 1)) + α * (k : ℝ) =
      (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) := by
    dsimp only [α]
    push_cast
    ring
  rw [hexp] at hout
  exact hout

/-- Normalize a complete scalar-composition jet once. The finite prefix
changes only the high order and the material coefficient; the low order
and the domain are supplied unchanged by the caller. -/
theorem n04SourceColumns_scalarComposition_positive_oneHigh (K s shift : ℕ) (RH : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (p : ℕ → Seminorm ℝ X) (center : X) (base high : ℕ),
      ∀ (U : Set X), IsOpen U → ∀ (Ω : Set PolarPoint), IsOpen Ω →
      ∀ (V : Set ℝ), IsOpen V → ∀ (f : X → PolarPoint → ℝ) (g : ℝ → ℝ),
      ∀ F : MixedJetRegularity U Ω f, ContDiffOn ℝ ∞ g V →
      (∀ y ∈ U, MapsTo (f y) Ω V) →
      ∀ q (hq : q ∈ Ω), ∀ H M : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ M →
      ∀ x ∈ U, p base (x - center) ≤ 1 →
      (∀ m : ℕ, m ≤ s → ∀ j : ℕ, j ≤ K →
        ‖iteratedFDeriv ℝ j (iteratedDeriv m g) (f x q)‖ ≤ M) →
      (∀ j : ℕ, j ≤ K → ∀ u w : ℕ, u + w ≤ s →
        ∀ z : Fin j → X, (∀ i, p base (z i) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R → (∀ i, p high (z i) ≤ R) →
        ‖(F.parameter u w q hq).D j x z‖ ≤ M * parameterHeightWeight H j *
          R ^ (((u + w + shift * j : ℕ) : ℝ) /
            (((s + shift * K : ℕ) : ℝ) + 1))) →
      ∀ k : ℕ, k ≤ K → 0 < k → ∀ a b : ℕ, a + b ≤ s →
      ∀ J : SmoothDirections U (fun y => mixedDerivative a b (fun z => g (f y z)) q),
      ∀ v : Fin k → X, ‖J.D k x v‖ ≤ B * M ^ (K + s + 1) * H *
        oneHighVariationWeight p base high (x - center) v := by
  classical
  let I : Type := Fin (K + 1) × Fin (s + 1) × Fin (s + 1)
  choose c hc hb using fun i : I =>
    n04SourceColumns_scalarComposition_shifted_bound (X := X)
      i.1.val i.2.1.val i.2.2.val RH
  let B : ℝ := 1 + ∑ i : I, c i
  have hB : 1 ≤ B := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun i _ => zero_le_one.trans (hc i)))
  have hcB (i : I) : c i ≤ B :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hc j)) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨B, hB, ?_⟩
  intro p center base high U hU Ω hΩ V hV f g F hg hmap q hq H M hH hHR hM
    x hx hlow houter hraw k hk hkpos a b hab J
  let i : I := (⟨k, Nat.lt_succ_of_le hk⟩, ⟨a, by omega⟩, ⟨b, by omega⟩)
  let C : ℝ := B * M ^ (K + s + 1) * H
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (zero_le_one.trans hB) (pow_nonneg (zero_le_one.trans hM) _)) hH
  have hn := multilinear_bound_of_unitBall (J.D k x) (normSeminorm ℝ ℝ)
    (p base) (p high) hC (a := 1 + p high (x - center)) (fun v hv => by
      let R : ℝ := (1 + p high (x - center)) + ∑ t, p high (v t)
      have hsum : 0 ≤ ∑ t, p high (v t) :=
        Finset.sum_nonneg (fun t _ => apply_nonneg _ _)
      have hR : 1 ≤ R := by
        dsimp only [R]
        linarith [apply_nonneg (p high) (x - center)]
      have hxR : p high (x - center) ≤ R := by dsimp only [R]; linarith
      have hvR (t : Fin k) : p high (v t) ≤ R :=
        (Finset.single_le_sum (fun j _ => apply_nonneg _ _) (Finset.mem_univ t)).trans
          (le_add_of_nonneg_left (by positivity))
      let P : X → Prop := fun w => p base w ≤ 1 ∧ p high w ≤ R
      have hvP (t : Fin k) : P (v t) := ⟨(hv t).le, hvR t⟩
      have hr := hb i U hU Ω hΩ V hV f g F hg hmap q hq J x hx P v hvP
        H M R hH hHR hM hR (s + shift * K) shift
        (fun m hm j hj => houter m (hm.trans hab) j (hj.trans hk))
        (fun j hj u w huw z hz => hraw j (hj.trans hk) u w (huw.trans hab) z
          (fun t => (hz t).1) R hR hxR (fun t => (hz t).2))
      have hr' : ‖J.D k x v‖ ≤ (c i * M ^ (k + a + b + 1) * H) *
          R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
        simpa only [i, parameterHeightWeight, if_neg (Nat.ne_of_gt hkpos)] using hr
      have hcoef : c i * M ^ (k + a + b + 1) * H ≤ C :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (hcB i) (pow_le_pow_right₀ hM (by omega))
            (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hB)) hH
      have hbudget : a + b + shift * k ≤ s + shift * K := by
        have hmul := Nat.mul_le_mul_left shift hk
        omega
      have hpow := Real.rpow_le_self_of_one_le hR (spatialOrder_fraction_le_one hbudget)
      have hbound : ‖J.D k x v‖ ≤ C * R := hr'.trans
        ((mul_le_mul_of_nonneg_right hcoef
          (Real.rpow_nonneg (zero_le_one.trans hR) _)).trans
            (mul_le_mul_of_nonneg_left hpow hC))
      simpa only [coe_normSeminorm, R] using hbound)
  simpa only [coe_normSeminorm, multilinearTameSize, oneHighVariationWeight, C] using hn

end ContinuousFlexibility.Analysis
