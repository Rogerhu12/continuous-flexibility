import ContinuousFlexibility.Analysis.FlatMixedDiagonalGrowth
import ContinuousFlexibility.Analysis.CircleStripAngularInterpolation

/-!
# A common power scale for actual mixed jets

The transport estimates choose their low order before the spatial
budget. A finite aggregation over parameter and spatial arities turns
the fractional power bound into the affine bound used by coefficient
products, with one fixed loss and the original flat label factor.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : I → Set PolarPoint}

def MixedDiagonalPowerGrowth
    (p : ℕ → Seminorm ℝ E) (W F : I → ℝ)
    {f : I → E × PolarPoint → ℝ}
    (J : ∀ i, SmoothDirections (U ×ˢ V i) (f i))
    (nmax B : ℕ) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ N k : ℕ, k ≤ nmax →
    ∀ a b : ℕ, a + b ≤ N → ∃ C P : ℝ, 0 ≤ C ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U → p B x ≤ R → ∀ w, p B w ≤ 1 → ∀ y ∈ V i,
        |jointMixedDiagonal (J i) k a b x w y| ≤
          C * W i ^ P * F i *
            (1 + p (N + B + 1) x + p (N + B + 1) w) ^
              (((a + b : ℕ) : ℝ) / ((N : ℝ) + 1))

theorem MixedDiagonalPowerGrowth.mono_base
    {p : ℕ → Seminorm ℝ E} {W F : I → ℝ}
    (hp : Monotone p) (hW : ∀ i, 0 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {nmax B B' : ℕ} (hg : MixedDiagonalPowerGrowth p W F J nmax B)
    (hB : B ≤ B') : MixedDiagonalPowerGrowth p W F J nmax B' := by
  intro R hR N k hk a b hab
  obtain ⟨C, P, hC, hP, hb⟩ := hg R hR N k hk a b hab
  refine ⟨C, P, hC, hP, fun i x hx hxB w hw y hy => ?_⟩
  exact (hb i x hx ((hp hB x).trans hxB) w ((hp hB w).trans hw) y hy).trans
    (mul_le_mul_of_nonneg_left (common_spatial_scale_mono hp hB x w)
      (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (hW i) P)) (hF i)))

/-- The loss is chosen before the low-ball radius and every spatial
order. Only finitely many constants are aggregated at each output
order; the flat label factor is unchanged. -/
theorem MixedDiagonalPowerGrowth.flat
    {p : ℕ → Seminorm ℝ E} {W F : I → ℝ}
    (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {nmax B : ℕ} (hg : MixedDiagonalPowerGrowth p W F J nmax B) :
    FlatMixedDiagonalGrowth p W F J nmax B (B + 1) := by
  classical
  intro R hR N
  let T := {t : Fin (nmax + 1) × (Fin (N + 1) × Fin (N + 1)) //
    t.2.1.val + t.2.2.val ≤ N}
  have hfinite (t : T) := hg R hR N t.val.1.val
    (Nat.le_of_lt_succ t.val.1.isLt) t.val.2.1.val t.val.2.2.val t.property
  choose C P hC hP hb using hfinite
  let C₀ : ℝ := ∑ t : T, C t
  let P₀ : ℝ := ∑ t : T, P t
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun t _ => hC t)
  have hP₀ : 0 ≤ P₀ := Finset.sum_nonneg (fun t _ => hP t)
  refine ⟨C₀, P₀, hC₀, hP₀, fun i x hx hxB w hw y hy k hk a b hab => ?_⟩
  let t : T := ⟨(⟨k, by omega⟩, (⟨a, by omega⟩, ⟨b, by omega⟩)), hab⟩
  have hCt : C t ≤ C₀ := Finset.single_le_sum (fun u _ => hC u) (Finset.mem_univ t)
  have hPt : P t ≤ P₀ := Finset.single_le_sum (fun u _ => hP u) (Finset.mem_univ t)
  have hWp := Real.rpow_le_rpow_of_exponent_le (hW i) hPt
  have hfactor : C t * W i ^ P t * F i ≤ C₀ * F i * W i ^ P₀ := by
    calc
      _ ≤ (C₀ * W i ^ P₀) * F i :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hCt hWp (Real.rpow_nonneg (zero_le_one.trans (hW i)) _) hC₀)
          (hF i)
      _ = _ := by ring
  let Q : ℝ := 1 + p (N + B + 1) x + p (N + B + 1) w
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    linarith only [apply_nonneg (p (N + B + 1)) x,
      apply_nonneg (p (N + B + 1)) w]
  have hden : 0 < (N : ℝ) + 1 := by positivity
  have hab' : ((a + b : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
    have hcast : ((a + b : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hab
    linarith
  have hexp : ((a + b : ℕ) : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
    exact (div_le_div_of_nonneg_right hab' hden.le).trans_eq (div_self hden.ne')
  have hQpow : Q ^ (((a + b : ℕ) : ℝ) / ((N : ℝ) + 1)) ≤ Q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ hexp
  have hfinal := (hb t i x hx hxB w hw y hy).trans
    (mul_le_mul hfactor hQpow (Real.rpow_nonneg (zero_le_one.trans hQ) _)
      (mul_nonneg (mul_nonneg hC₀ (hF i))
        (Real.rpow_nonneg (zero_le_one.trans (hW i)) P₀)))
  simpa only [Q, t, Nat.add_assoc] using hfinal

end ContinuousFlexibility.Analysis
