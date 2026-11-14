module

public import ContinuousFlexibility.Analysis.N04PrincipalWeightedPrefix
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Finite products of weighted current towers

Every external piece weight occurs exactly once. Interpolation precedes
the product estimate, and multilinear normalization is performed after
the product has been formed. The low order is independent of both the
parameter and spatial derivative orders.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {ι : Type*} {U : Set X} {Ω : Set PolarPoint}

/-- Finite products preserve complete weighted tower bounds, after one
fixed increase of the low order. -/
theorem n04Principal_weightedTower_product
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hI : HasInterpolation p)
    (oldBase requestedBase : ℕ) {r : ℕ}
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    (E : ι → ℝ) (W : Fin r → ι → ℝ)
    (hE : ∀ m, 1 ≤ E m) (hW : ∀ i m, 0 < W i m)
    (f : Fin r → ι → X → PolarPoint → ℝ)
    (R : ∀ i m, MixedJetRegularity U Ω (f i m))
    (RP : ∀ m, MixedJetRegularity U Ω (fun x q => ∏ i, f i m x q))
    (hb : ∀ i, N04PrincipalWeightedTowerBounds p oldBase E (W i) (R i)) :
    ∃ base : ℕ, max oldBase requestedBase ≤ base ∧
      N04PrincipalWeightedTowerBounds p base E (fun m => ∏ i, W i m) RP := by
  classical
  have hprefix := n04Principal_weightedTower_prefix p hp hI oldBase requestedBase
    E W hE (fun i m => (hW i m).le) f R hb
  let base : ℕ := hprefix.choose
  refine ⟨base, hprefix.choose_spec.1, fun k => ?_⟩
  have hpk := hprefix.choose_spec.2 k
  let shift : ℕ := hpk.choose
  let d : ℕ := shift * k
  let loss : ℕ := base + r * d + d + 1
  refine ⟨loss, fun s => ?_⟩
  let top : ℕ := s + r * d
  have hps := hpk.choose_spec top
  let C : ℝ := hps.choose
  let A : ℝ := hps.choose_spec.choose
  have hC : 1 ≤ C := hps.choose_spec.choose_spec.1
  have hA : 0 ≤ A := hps.choose_spec.choose_spec.2.1
  have hraw := hps.choose_spec.choose_spec.2.2
  have hproduct := n04Realization_fullWeightProduct_oneHigh (X := X) r k s
  let B : ℝ := hproduct.choose
  have hB : 0 < B := hproduct.choose_spec.1
  have hpack := coefficientEnvelope_pack (B * C ^ r) (A * (r : ℝ))
  refine ⟨hpack.choose, hpack.choose_spec.1, ?_⟩
  intro m a b hab q hq x hx hlow v
  let weights : Fin r → PolarPoint → ℝ := fun i _ => C * E m ^ A * W i m
  let high : ℕ := base + top + shift * k + 1
  have hhigh : high = s + loss := by dsimp only [high, loss, top, d]; omega
  have hweights (i : Fin r) (y : PolarPoint) (hy : y ∈ Ω) : 0 < weights i y :=
    mul_pos (mul_pos (zero_lt_one.trans_le hC)
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hE m)) _)) (hW i m)
  have hsum : (∑ _i : Fin r, d) = r * d := by simp
  have hraw' : ∀ i : Fin r, ∀ j : ℕ, j ≤ k → ∀ u w : ℕ, u + w ≤ s →
      ∀ y (hy : y ∈ Ω), ∀ z ∈ U, p base (z - 0) ≤ 1 →
      ∀ vs : Fin j → X, (∀ t, p base (vs t) ≤ 1) →
      ∀ V : ℝ, 1 ≤ V → p high (z - 0) ≤ V →
        (∀ t, p high (vs t) ≤ V) →
      ‖((R i m).parameter u w y hy).D j z vs‖ ≤ weights i y *
        V ^ (((u + w + d : ℕ) : ℝ) /
          (((s + ∑ _i : Fin r, d : ℕ) : ℝ) + 1)) := by
    intro i j hj u w huw y hy z hz hzlow vs hvs V hV hzV hvsV
    simp only [sub_zero] at hzlow hzV
    have htop : u + w ≤ top := huw.trans (Nat.le_add_right _ _)
    have h := hraw i m j hj u w htop y hy z hz hzlow vs hvs V hV hzV hvsV
    have hnum : ((u + w + shift * j : ℕ) : ℝ) ≤ ((u + w + d : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_left shift hj) (u + w)
    have hden : (((s + r * d : ℕ) : ℝ) + 1) ≤
        (((top + shift * k : ℕ) : ℝ) + 1) := by
      exact_mod_cast Nat.add_le_add_right (Nat.le_add_right (s + r * d) (shift * k)) 1
    have hexp : ((u + w + shift * j : ℕ) : ℝ) /
        (((top + shift * k : ℕ) : ℝ) + 1) ≤
        ((u + w + d : ℕ) : ℝ) / (((s + r * d : ℕ) : ℝ) + 1) :=
      (div_le_div_of_nonneg_right hnum (by positivity)).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
    rw [hsum]
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hV hexp) (hweights i y hy).le)
  have hfinal := hproduct.choose_spec.2 p 0 base high (fun _ : Fin r => d)
    U hU Ω hΩ (fun i => f i m) (fun i => R i m) weights hweights hraw'
    k le_rfl a b hab q hq ((RP m).parameter a b q hq) x hx
    (by simpa only [sub_zero] using hlow) v
  have he0 : 0 ≤ E m := zero_le_one.trans (hE m)
  have hprod : (∏ i, weights i q) = C ^ r * E m ^ (A * (r : ℝ)) * ∏ i, W i m := by
    simp only [weights, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [← Real.rpow_mul_natCast he0]
  rw [hprod, sub_zero, hhigh] at hfinal
  have hw : 0 ≤ (∏ i, W i m) * oneHighVariationWeight p base (s + loss) x v :=
    mul_nonneg (Finset.prod_nonneg (fun i _ => (hW i m).le))
      (oneHighVariationWeight_nonneg _ _ _ _ _)
  have hp := mul_le_mul_of_nonneg_right (hpack.choose_spec.2 (E m) (hE m)) hw
  apply hfinal.trans
  convert hp using 1 <;> ring

end ContinuousFlexibility.Analysis
