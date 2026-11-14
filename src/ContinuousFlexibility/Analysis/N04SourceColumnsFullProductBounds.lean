module

public import ContinuousFlexibility.Analysis.N04SourceColumnsFullProduct

/-!
# Fixed low order for products of full current towers

All factors are interpolated on one finite prefix. Their height gain is
used only for positive parameter derivatives, as required by the actual
reference-plus-difference estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04SourceColumns_fullProduct_oneHigh
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hI : HasInterpolation p)
    (oldBase : ℕ) (L : ℕ → ℕ)
    {m : ℕ} {U : Set X} {Ω : Set PolarPoint}
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    (E H : I → ℝ) (RH : ℝ)
    (hE : ∀ t, 1 ≤ E t) (hH : ∀ t, 0 ≤ H t ∧ H t ≤ RH)
    (f : Fin m → I → X → PolarPoint → ℝ)
    (RF : ∀ i t, MixedJetRegularity U Ω (f i t))
    (hbound : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i t q (hq : q ∈ Ω) a b, a + b ≤ s →
      ∀ x ∈ U, ∀ v : Fin k → X,
        |((RF i t).parameter a b q hq).D k x v| ≤
          B * E t ^ B * parameterHeightWeight (H t) k *
            oneHighVariationWeight p oldBase (s + L k) x v) :
    ∃ base : ℕ, oldBase ≤ base ∧ ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ t q (hq : q ∈ Ω) a b, a + b ≤ s →
      ∀ J : SmoothDirections U
        (fun x => mixedDerivative a b (fun y => ∏ i, f i t x y) q),
      ∀ x ∈ U, p base x ≤ 1 → ∀ v : Fin k → X,
        |J.D k x v| ≤ B * E t ^ B * parameterHeightWeight (H t) k *
          oneHighVariationWeight p base (s + loss) x v := by
  classical
  have hinput : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ t : Fin m × I, ∀ q (hq : q ∈ Ω) a b, a + b ≤ s →
      ∀ x ∈ U, ∀ v : Fin k → X,
        |((RF t.1 t.2).parameter a b q hq).D k x v| ≤
          B * E t.2 ^ B * parameterHeightWeight (H t.2) k *
            oneHighVariationWeight p oldBase (s + L k) x v := by
    intro k s
    have h := hbound k s
    exact ⟨h.choose, h.choose_spec.1,
      fun t q hq a b hab x hx v => h.choose_spec.2 t.1 t.2 q hq a b hab x hx v⟩
  have hc := n04SourceColumns_prefix_power p hp hI oldBase L
    (fun t : Fin m × I => E t.2) (fun k t => parameterHeightWeight (H t.2) k)
    (fun t => hE t.2) (fun k t => parameterHeightWeight_nonneg (hH t.2).1 k)
    (fun t => f t.1 t.2) (fun t => RF t.1 t.2) hinput
  refine ⟨hc.choose, hc.choose_spec.1, fun k => ?_⟩
  let base : ℕ := hc.choose
  have hk := hc.choose_spec.2 k
  let shift : ℕ := hk.choose
  let offset : ℕ := shift * k
  let loss : ℕ := base + m * offset + offset + 1
  refine ⟨loss, fun s => ?_⟩
  have hs := hk.choose_spec (s + m * offset)
  let A : ℝ := hs.choose
  have hA : 0 < A := hs.choose_spec.1
  have hAb := hs.choose_spec.2
  obtain ⟨P, hP, hPb⟩ := n04SourceColumns_fullProduct_raw_oneHigh (X := X) m k s RH
  obtain ⟨B, hB, hBb⟩ := coefficientEnvelope_pack (P * A ^ m) (A * (m : ℝ))
  have hhigh : base + (s + m * offset) + shift * k + 1 = s + loss := by
    dsimp only [loss, offset]
    omega
  have hsum : (∑ _i : Fin m, offset) = m * offset := by simp
  refine ⟨B, hB, ?_⟩
  intro t q hq a b hab J x hx hlow v
  let weights : Fin m → PolarPoint → ℝ := fun _ _ => A * E t ^ A
  have hweights (i : Fin m) (q : PolarPoint) (hq : q ∈ Ω) : 0 < weights i q :=
    mul_pos hA (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hE t)) _)
  have hraw : ∀ i : Fin m, ∀ j : ℕ, j ≤ k → ∀ u w : ℕ, u + w ≤ s →
      ∀ r (hr : r ∈ Ω), ∀ z ∈ U, p base z ≤ 1 →
      ∀ v' : Fin j → X, (∀ n, p base (v' n) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p (s + loss) z ≤ R →
        (∀ n, p (s + loss) (v' n) ≤ R) →
      ‖((RF i t).parameter u w r hr).D j z v'‖ ≤
        weights i r * parameterHeightWeight (H t) j *
          R ^ (((u + w + offset : ℕ) : ℝ) /
            (((s + ∑ _i : Fin m, offset : ℕ) : ℝ) + 1)) := by
    intro i j hj u w huw r hr z hz hzlow v' hv R hR hzR hvR
    have hzR' : p (base + (s + m * offset) + shift * k + 1) z ≤ R := by
      simpa only [hhigh] using hzR
    have hvR' : ∀ n, p (base + (s + m * offset) + shift * k + 1) (v' n) ≤ R := by
      simpa only [hhigh] using hvR
    have h := hAb j hj (i, t) r hr u w (huw.trans (Nat.le_add_right _ _)) z hz
      hzlow v' hv R hR hzR' hvR'
    have hnum : (u + w + shift * j : ℕ) ≤ u + w + offset := by
      dsimp only [offset]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left shift hj) _
    have hden : ((s + m * offset : ℕ) : ℝ) + 1 ≤
        ((s + m * offset + shift * k : ℕ) : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right (Nat.le_add_right _ _) 1
    have hexp : ((u + w + shift * j : ℕ) : ℝ) /
        (((s + m * offset + shift * k : ℕ) : ℝ) + 1) ≤
        ((u + w + offset : ℕ) : ℝ) / (((s + m * offset : ℕ) : ℝ) + 1) :=
      div_le_div₀ (by positivity) (by exact_mod_cast hnum) (by positivity) hden
    have hcost : 0 ≤ A * E t ^ A * parameterHeightWeight (H t) j :=
      mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg (zero_le_one.trans (hE t)) _))
        (parameterHeightWeight_nonneg (hH t).1 j)
    have hfinal := h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hR hexp) hcost)
    simpa only [Real.norm_eq_abs, hsum, weights] using hfinal
  have hb := hPb p base (s + loss) (fun _i : Fin m => offset) U hU Ω hΩ
    (fun i => f i t) (fun i => RF i t) weights hweights (fun _ => H t)
    (fun _ _ => hH t) hraw k le_rfl a b hab q hq J x hx hlow v
  have hprod : (∏ i, weights i q) = A ^ m * E t ^ (A * (m : ℝ)) := by
    dsimp only [weights]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans (hE t)) A m]
  have hcoef : P * (∏ i, weights i q) ≤ B * E t ^ B := by
    calc
      P * (∏ i, weights i q) = P * (A ^ m * E t ^ (A * (m : ℝ))) :=
        congrArg (fun y : ℝ => P * y) hprod
      _ = (P * A ^ m) * E t ^ (A * (m : ℝ)) := (mul_assoc _ _ _).symm
      _ ≤ B * E t ^ B := hBb (E t) (hE t)
  have hfinal := hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (parameterHeightWeight_nonneg (hH t).1 k))
    (oneHighVariationWeight_nonneg p base (s + loss) x v))
  exact (Real.norm_eq_abs _).symm.trans_le hfinal

end ContinuousFlexibility.Analysis
