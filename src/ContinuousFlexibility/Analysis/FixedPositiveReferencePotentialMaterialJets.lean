module

public import ContinuousFlexibility.Analysis.RadialReferencePotentialJetEnvelope
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Potential bounds for an already chosen positive reference family

The coordinate and height are inputs, and the inverse is literally the
inverse of that coordinate. Only numerical bounds are chosen here. Thus
the principal and potential estimates can use one common construction,
including its original low envelope, width, cell and sampling point.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators

private theorem fixedReferencePotential_profile_compact_bound
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (l r : ℝ) (s : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ k, k ≤ s → ∀ x ∈ Icc l r,
      |iteratedDeriv k w x| ≤ P := by
  classical
  have hbound (k : Fin (s + 1)) : ∃ A : ℝ, ∀ x ∈ Icc l r,
      ‖iteratedDeriv k.val w x‖ ≤ A :=
    isCompact_Icc.exists_bound_of_continuousOn
      (ContDiff.continuous_iteratedDeriv k.val hw (by simp)).continuousOn
  choose A hA using hbound
  refine ⟨∑ k : Fin (s + 1), |A k|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro k hk x hx
  let j : Fin (s + 1) := ⟨k, by omega⟩
  have hjet : |iteratedDeriv k w x| ≤ A j := by
    simpa only [Real.norm_eq_abs] using hA j x hx
  exact (hjet.trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun k : Fin (s + 1) => |A k|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j))

/-- Only coefficient bounds are selected. The supplied coordinate,
height, inverse, and weight remain the same at every derivative order. -/
theorem fixedPositiveReference_potential_material_jets
    {ι : Type*} {w : ℝ → ℝ} {l r : ℝ}
    (hw : ContDiff ℝ ∞ w)
    (W : ι → ℝ) (hW : ∀ i, 1 ≤ W i)
    (Y H : ι → ℝ → ℝ)
    (hH : ∀ i, ContDiff ℝ ∞ (H i))
    (hχ : ∀ i, ContDiff ℝ ∞ (Function.invFun (Y i)))
    (hrange : ∀ i x, x ∈ Ioo (0 : ℝ) 1 →
      Function.invFun (Y i) x ∈ Icc l r)
    (hjets : ∀ N : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ i,
      (∀ k, k ≤ N → ∀ x : ℝ, |iteratedDeriv k (H i) x| ≤ A * W i ^ A) ∧
      ∀ x : ℝ, |iteratedDeriv (N + 1) (Function.invFun (Y i)) x| ≤ A * W i ^ A) :
    ∀ s : ℕ, ∃ M : ℝ, 1 ≤ M ∧ ∀ i x, x ∈ Ioo (0 : ℝ) 1 →
      |iteratedDeriv s
        (fun t => -(H i (Function.invFun (Y i) t) *
          deriv ((fun u => w u * deriv (H i) u) ∘ Function.invFun (Y i)) t)) x| ≤
        M * W i ^ M := by
  classical
  choose A₀ hA₀ hactual using hjets
  intro s
  obtain ⟨P₀, hP₀, hprofile⟩ :=
    fixedReferencePotential_profile_compact_bound hw l r (s + 1)
  obtain ⟨C₁, hC₁, henvelope⟩ := exists_radialReferencePotential_jet_envelope s
  let D : ℝ := 1 + ∑ k : Fin (s + 3), A₀ k.val
  have hD : 1 ≤ D := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun k _ => zero_le_one.trans (hA₀ k.val)))
  have hAD (k : ℕ) (hk : k ≤ s + 2) : A₀ k ≤ D :=
    (Finset.single_le_sum (f := fun j : Fin (s + 3) => A₀ j.val)
      (fun j _ => zero_le_one.trans (hA₀ j.val))
      (Finset.mem_univ (⟨k, by omega⟩ : Fin (s + 3)))).trans
        (le_add_of_nonneg_left zero_le_one)
  let d : ℕ := 2 * s + 3
  let coefficient : ℝ := C₁ * P₀ * D ^ d
  let exponent : ℝ := D * (d : ℝ)
  let M : ℝ := 1 + D + coefficient + exponent
  have hcoefficient : 0 ≤ coefficient :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hC₁) hP₀)
      (pow_nonneg (zero_le_one.trans hD) _)
  have hexponent : 0 ≤ exponent :=
    mul_nonneg (zero_le_one.trans hD) (Nat.cast_nonneg _)
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hD, hcoefficient, hexponent]
  have hcoefficientM : coefficient ≤ M := by
    dsimp only [M]; linarith only [hD, hexponent]
  have hexponentM : exponent ≤ M := by
    dsimp only [M]; linarith only [hD, hcoefficient]
  refine ⟨M, hM, ?_⟩
  intro i x hx
  let Z : ℝ := D * W i ^ D
  have hZ : 1 ≤ Z := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ D * W i ^ D := mul_le_mul hD
        (Real.one_le_rpow (hW i) (zero_le_one.trans hD)) zero_le_one (zero_le_one.trans hD)
  have hbound (k : ℕ) (hk : k ≤ s + 2) : A₀ k * W i ^ A₀ k ≤ Z :=
    mul_le_mul (hAD k hk)
      (Real.rpow_le_rpow_of_exponent_le (hW i) (hAD k hk))
      (Real.rpow_nonneg (zero_le_one.trans (hW i)) _) (zero_le_one.trans hD)
  have hcost : C₁ * P₀ * Z ^ d ≤ M * W i ^ M := by
    calc
      _ = coefficient * W i ^ exponent := by
        dsimp only [Z, coefficient, exponent]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans (hW i)) D d]
        ring
      _ ≤ coefficient * W i ^ M := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hW i) hexponentM) hcoefficient
      _ ≤ M * W i ^ M := mul_le_mul_of_nonneg_right hcoefficientM
        (Real.rpow_nonneg (zero_le_one.trans (hW i)) _)
  have hheight (k : ℕ) (hk : k ≤ s + 2) (u : ℝ) :
      |iteratedDeriv k (H i) u| ≤ Z :=
    ((hactual (s + 2) i).1 k hk u).trans (hbound (s + 2) le_rfl)
  have hinverse (k : ℕ) (hk : 1 ≤ k) (hks : k ≤ s + 1) (u : ℝ) :
      |iteratedDeriv k (Function.invFun (Y i)) u| ≤ Z := by
    have he : k - 1 + 1 = k := by omega
    have hi := (hactual (k - 1) i).2 u
    rw [he] at hi
    exact hi.trans (hbound (k - 1) (by omega))
  have hb := henvelope hP₀ hZ w (H i) (Function.invFun (Y i)) x hw (hH i) (hχ i)
    (fun k hk => hprofile k hk _ (hrange i x hx))
    (fun k hk => hheight k hk _)
    (fun k hk hks => hinverse k hk hks x)
  exact hb.trans hcost

end ContinuousFlexibility.Analysis
