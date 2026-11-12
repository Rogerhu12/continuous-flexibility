import ContinuousFlexibility.Analysis.N03ResidualErrorBounds

/-!
# A common fixed loss after finitely many genuine source probes

The source estimate retains both test grades. A finite group of fixed
tests and finitely many spatial orders can be bounded by constants before
the state is chosen. A recovery operation losing two spatial orders then
preserves the original low-order neighborhood and increases the loss by
exactly two. Component constants remain unrestricted in this lemma.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem finiteProbe_source_scalar_bound
    {A B H M W P Q T S : ℝ}
    (hB : 0 ≤ B) (hH : 0 ≤ H) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hP : 0 ≤ P) (hT : 0 ≤ T) (hAB : A ≤ B)
    (hweight : H * M ≤ W) (hPQ : P ≤ Q) (hTS : T ≤ S) :
    A * H * M * (1 + P) * T ≤ B * W * S * (1 + Q) := by
  have hweight' : A * (H * M) ≤ B * W :=
    mul_le_mul hAB hweight (mul_nonneg hH hM) hB
  have hstate : A * (H * M) * (1 + P) ≤ B * W * (1 + Q) :=
    mul_le_mul hweight' (add_le_add (le_refl (1 : ℝ)) hPQ) (by linarith) (mul_nonneg hB hW)
  have hQ : 0 ≤ Q := hP.trans hPQ
  calc
    _ = A * (H * M) * (1 + P) * T := by ring
    _ ≤ B * W * (1 + Q) * S :=
      mul_le_mul hstate hTS hT (mul_nonneg (mul_nonneg hB hW) (by linarith))
    _ = B * W * S * (1 + Q) := by ring

/-- The component index and every derivative order come after the same
low order and radius. The recovery premise is an actual finite-source
estimate, not a bound assumed for the desired coefficients. -/
theorem fixed_loss_bound_of_finiteProbe_recovery
    {Z F I ι : Type*} [Fintype ι]
    {U : Set Z} {Ω : Set PolarPoint}
    {p : ℕ → Z → ℝ} {t : ℕ → F → ℝ}
    {jet : ℕ → ℕ → Z → F → PolarPoint → ℝ}
    {value : I → ℕ → ℕ → Z → PolarPoint → ℝ}
    {H M : PolarPoint → ℝ} {η : I → ι → F} {V : I → Set PolarPoint}
    (hp : Monotone p) (ht : Monotone t)
    (hpn : ∀ n z, 0 ≤ p n z) (htn : ∀ n f, 0 ≤ t n f)
    {W : ℝ} (hW : 0 ≤ W)
    (hweight : ∀ x ∈ Ω, 0 ≤ H x ∧ 0 ≤ M x ∧ H x * M x ≤ W)
    (hV : ∀ m x, x ∈ V m → ∀ θ : ℝ, (x.1, θ) ∈ Ω)
    (hsource : ∃ loss low : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ a b : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ z ∈ U, p low z < δ → ∀ f : F, ∀ x ∈ Ω,
          jet a b z f x ≤ B * H x * M x * (1 + p (a + b + loss) z) *
            (t low f + t (a + b + loss) f))
    (hrecover : ∀ m a b, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ U, ∀ x ∈ V m,
      ∀ B : ℝ, 0 ≤ B →
        (∀ i j : ℕ, i + j ≤ a + b + 2 → ∀ θ : ℝ, ∀ k : ι,
          jet i j z (η m k) (x.1, θ) ≤ B) → value m a b z x ≤ C * B) :
    ∃ loss low : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ m a b, ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ U, p low z < δ →
        ∀ x ∈ V m, value m a b z x ≤ B * (1 + p (a + b + loss) z) := by
  classical
  obtain ⟨loss, low, δ, hδ, hsource⟩ := hsource
  choose A hA hjet using hsource
  refine ⟨2 + loss, low, δ, hδ, ?_⟩
  intro m a b
  obtain ⟨C, hC, hrec⟩ := hrecover m a b
  let s := a + b + 2
  let Asum : ℝ := ∑ i ∈ Finset.range (s + 1), ∑ j ∈ Finset.range (s + 1), A i j
  let Tsum : ℝ := ∑ k : ι, (t low (η m k) + t (s + loss) (η m k))
  have hAsum : 0 ≤ Asum :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hA i j
  have hTsum : 0 ≤ Tsum :=
    Finset.sum_nonneg fun k _ => add_nonneg (htn low _) (htn (s + loss) _)
  have hAle (i j : ℕ) (hij : i + j ≤ s) : A i j ≤ Asum := by
    have hi : i ∈ Finset.range (s + 1) := Finset.mem_range.mpr (by omega)
    have hj : j ∈ Finset.range (s + 1) := Finset.mem_range.mpr (by omega)
    calc
      _ ≤ ∑ k ∈ Finset.range (s + 1), A i k :=
        Finset.single_le_sum (fun k _ => hA i k) hj
      _ ≤ Asum := Finset.single_le_sum
        (fun k _ => Finset.sum_nonneg fun l _ => hA k l) hi
  have hTle (k : ι) (i j : ℕ) (hij : i + j ≤ s) :
      t low (η m k) + t (i + j + loss) (η m k) ≤ Tsum := by
    calc
      _ ≤ t low (η m k) + t (s + loss) (η m k) :=
        add_le_add (le_refl _) (ht (Nat.add_le_add_right hij loss) _)
      _ ≤ Tsum := Finset.single_le_sum
        (fun k _ => add_nonneg (htn low _) (htn (s + loss) _)) (Finset.mem_univ k)
  refine ⟨C * (Asum * W * Tsum), by positivity, ?_⟩
  intro z hz hlow x hx
  let B : ℝ := (Asum * W * Tsum) * (1 + p (s + loss) z)
  have hB : 0 ≤ B := mul_nonneg (by positivity) (by linarith [hpn (s + loss) z])
  have hb (i j : ℕ) (hij : i + j ≤ a + b + 2) (θ : ℝ) (k : ι) :
      jet i j z (η m k) (x.1, θ) ≤ B := by
    have hxΩ := hV m x hx θ
    have hw := hweight (x.1, θ) hxΩ
    apply (hjet i j z hz hlow (η m k) (x.1, θ) hxΩ).trans
    exact finiteProbe_source_scalar_bound hAsum hw.1 hw.2.1 hW
      (hpn (i + j + loss) z) (add_nonneg (htn low _) (htn (i + j + loss) _))
      (hAle i j hij) hw.2.2 (hp (Nat.add_le_add_right hij loss) z) (hTle k i j hij)
  have hh := hrec z hz x hx B hB hb
  have ho : s + loss = a + b + (2 + loss) := by dsimp only [s]; omega
  calc
    value m a b z x ≤ C * B := hh
    _ = (C * (Asum * W * Tsum)) * (1 + p (a + b + (2 + loss)) z) := by
      dsimp only [B]
      rw [ho]
      ring

end ContinuousFlexibility.Analysis
