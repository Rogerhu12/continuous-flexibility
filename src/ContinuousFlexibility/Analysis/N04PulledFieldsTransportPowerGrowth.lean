import ContinuousFlexibility.Analysis.JointTransportPowerBounds

/-!
# Power growth with a fixed low order and a parameter charge

The interpolation denominator is the spatial top plus one. A finite
parameter prefix has an independent high loss and one charge per state
derivative. Increasing the top by the total parameter charge recovers
the original flat mixed growth without changing the low order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : I → Set PolarPoint}

def N04PulledFieldsMixedPowerGrowth
    (p : ℕ → Seminorm ℝ E) (W F : I → ℝ)
    {f : I → E × PolarPoint → ℝ}
    (J : ∀ i, SmoothDirections (U ×ˢ V i) (f i))
    (nmax base highLoss shift : ℕ) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ N k : ℕ, k ≤ nmax →
    ∀ a b : ℕ, a + b ≤ N → ∃ C P : ℝ, 0 ≤ C ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U → p base x ≤ R → ∀ w, p base w ≤ 1 → ∀ y ∈ V i,
        |jointMixedDiagonal (J i) k a b x w y| ≤ C * W i ^ P * F i *
          (1 + p (N + highLoss) x + p (N + highLoss) w) ^
            (((a + b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1))

def N04PulledFieldsAngularPowerGrowth
    (p : ℕ → Seminorm ℝ E) (W F : I → ℝ)
    {f : I → E × PolarPoint → ℝ}
    (J : ∀ i, SmoothDirections (U ×ˢ V i) (f i))
    (nmax base highLoss shift : ℕ) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ N k : ℕ, k ≤ nmax →
    ∀ b : ℕ, b ≤ N → ∃ C P : ℝ, 0 ≤ C ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U → p base x ≤ R → ∀ w, p base w ≤ 1 → ∀ y ∈ V i,
        |jointMixedDiagonal (J i) k 0 b x w y| ≤ C * W i ^ P * F i *
          (1 + p (N + highLoss) x + p (N + highLoss) w) ^
            (((b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1))

/-- The parameter charge is paid once in the high loss. The base and
the label factor are retained for every spatial order and low-ball radius. -/
theorem N04PulledFieldsMixedPowerGrowth.flat
    {p : ℕ → Seminorm ℝ E} {W F : I → ℝ}
    (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {nmax base highLoss shift : ℕ}
    (hg : N04PulledFieldsMixedPowerGrowth p W F J nmax base highLoss shift) :
    FlatMixedDiagonalGrowth p W F J nmax base (highLoss + shift * nmax) := by
  classical
  intro R hR s
  let N : ℕ := s + shift * nmax
  let T := {t : Fin (nmax + 1) × (Fin (s + 1) × Fin (s + 1)) //
    t.2.1.val + t.2.2.val ≤ s}
  have hfinite (t : T) := hg R hR N t.val.1.val
    (Nat.le_of_lt_succ t.val.1.isLt) t.val.2.1.val t.val.2.2.val
    (t.property.trans (Nat.le_add_right s (shift * nmax)))
  choose C P hC hP hb using hfinite
  let C₀ : ℝ := ∑ t : T, C t
  let P₀ : ℝ := ∑ t : T, P t
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun t _ => hC t)
  have hP₀ : 0 ≤ P₀ := Finset.sum_nonneg (fun t _ => hP t)
  refine ⟨C₀, P₀, hC₀, hP₀, fun i x hx hxB w hw y hy k hk a b hab => ?_⟩
  let t : T := ⟨(⟨k, by omega⟩, (⟨a, by omega⟩, ⟨b, by omega⟩)), hab⟩
  have hCt : C t ≤ C₀ := Finset.single_le_sum (fun u _ => hC u) (Finset.mem_univ t)
  have hPt : P t ≤ P₀ := Finset.single_le_sum (fun u _ => hP u) (Finset.mem_univ t)
  have hfactor : C t * W i ^ P t * F i ≤ C₀ * F i * W i ^ P₀ := by
    calc
      _ ≤ (C₀ * W i ^ P₀) * F i := mul_le_mul_of_nonneg_right
        (mul_le_mul hCt (Real.rpow_le_rpow_of_exponent_le (hW i) hPt)
          (Real.rpow_nonneg (zero_le_one.trans (hW i)) _) hC₀) (hF i)
      _ = _ := by ring
  let Q : ℝ := 1 + p (N + highLoss) x + p (N + highLoss) w
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    linarith only [apply_nonneg (p (N + highLoss)) x, apply_nonneg (p (N + highLoss)) w]
  have horder : a + b + shift * k ≤ N :=
    Nat.add_le_add hab (Nat.mul_le_mul_left shift hk)
  have hden : 0 < (N : ℝ) + 1 := by positivity
  have horder' : ((a + b + shift * k : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
    have hcast : ((a + b + shift * k : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast horder
    linarith
  have hexp : ((a + b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_div_of_nonneg_right horder' hden.le).trans_eq (div_self hden.ne')
  have hQpow : Q ^ (((a + b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1)) ≤ Q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ hexp
  have hfinal := (hb t i x hx hxB w hw y hy).trans
    (mul_le_mul hfactor hQpow (Real.rpow_nonneg (zero_le_one.trans hQ) _)
      (mul_nonneg (mul_nonneg hC₀ (hF i))
        (Real.rpow_nonneg (zero_le_one.trans (hW i)) P₀)))
  have hindex : N + highLoss = s + (highLoss + shift * nmax) := by
    dsimp only [N]
    omega
  simpa only [Q, t, hindex] using hfinal

end ContinuousFlexibility.Analysis
