import ContinuousFlexibility.Statements.Analysis
import ContinuousFlexibility.Analysis.TameMultilinearNormalization
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Interpolation products with one high seminorm factor

A fixed interpolation loss gives a fixed low order and a fixed high-order
shift for every finite product whose total assigned differential order is
at most the output order.  The number of factors changes only the constant.
The final theorem normalizes a genuine multilinear map from its original
product estimate; it does not assume a one-high-factor conclusion.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

/-- Nonnegative exponents of total size at most one leave only one
affine high factor. -/
theorem prod_one_add_rpow_le_one_add_sum {k : ℕ} (z θ : Fin k → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hθ : ∀ i, 0 ≤ θ i) (hsum : ∑ i, θ i ≤ 1) :
    ∏ i, (1 + z i) ^ θ i ≤ 1 + ∑ i, z i := by
  have hsumz : 0 ≤ ∑ i, z i := Finset.sum_nonneg (fun i _ => hz i)
  have hM : 1 ≤ 1 + ∑ i, z i := by linarith
  have hMpos : 0 < 1 + ∑ i, z i := zero_lt_one.trans_le hM
  have hi (i : Fin k) : 1 + z i ≤ 1 + ∑ j, z j := by
    have hzi : z i ≤ ∑ j, z j :=
      Finset.single_le_sum (fun j _ => hz j) (Finset.mem_univ i)
    linarith
  calc
    ∏ i, (1 + z i) ^ θ i ≤ ∏ i, (1 + ∑ j, z j) ^ θ i :=
      Finset.prod_le_prod₀
        (fun i _ => Real.rpow_nonneg (by linarith [hz i]) _)
        (fun i _ => Real.rpow_le_rpow (by linarith [hz i]) (hi i) (hθ i))
    _ = (1 + ∑ j, z j) ^ (∑ i, θ i) :=
      (Real.rpow_sum_of_pos hMpos θ Finset.univ).symm
    _ ≤ 1 + ∑ i, z i := Real.rpow_le_self_of_one_le hM hsum

/-- The spatial derivative count provides the required sum of Young exponents. -/
theorem sum_order_fractions_le_one {k s : ℕ} (a : Fin k → ℕ)
    (ha : ∑ i, a i ≤ s) :
    ∑ i, (a i : ℝ) / ((s : ℝ) + 1) ≤ 1 := by
  have haR : ∑ i, (a i : ℝ) ≤ (s : ℝ) := by exact_mod_cast ha
  rw [← Finset.sum_div]
  apply (div_le_one (by positivity : 0 < (s : ℝ) + 1)).mpr
  linarith

section SeminormProducts

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The spatial order determines the interpolation exponent. The same
base and loss work before the order and the input vector are chosen. -/
theorem exists_interpolatedJetBounds (p : ℕ → Seminorm ℝ E)
    (hp : Monotone p) (hinterp : HasInterpolation p) (offset : ℕ) :
    ∃ base loss : ℕ, ∀ s a : ℕ, a ≤ s →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ x : E, p base x ≤ 1 →
        p (a + offset) x ≤
          C * (1 + p (s + loss) x) ^ ((a : ℝ) / ((s : ℝ) + 1)) := by
  classical
  obtain ⟨b₀, σ, hinterp⟩ := hinterp
  let base : ℕ := max b₀ (offset + σ)
  let loss : ℕ := base + 1
  have hb₀ : b₀ ≤ base := le_max_left _ _
  have hoff : offset + σ ≤ base := le_max_right _ _
  have hsingle (s a : ℕ) (ha : a ≤ s) :
      ∃ C : ℝ, 1 ≤ C ∧ ∀ x : E, p base x ≤ 1 →
        p (a + offset) x ≤
          C * (1 + p (s + loss) x) ^ ((a : ℝ) / ((s : ℝ) + 1)) := by
    have hden : 0 < (s : ℝ) + 1 := by positivity
    have hexp : 0 ≤ (a : ℝ) / ((s : ℝ) + 1) :=
      div_nonneg (Nat.cast_nonneg _) hden.le
    by_cases hlow : a + offset ≤ base
    · refine ⟨1, le_rfl, fun x hx => ?_⟩
      have hhigh : 1 ≤ 1 + p (s + loss) x := by
        linarith [apply_nonneg (p (s + loss)) x]
      simpa only [one_mul] using
        ((hp hlow x).trans hx).trans (Real.one_le_rpow hhigh hexp)
    · have hmid : base < a + offset := Nat.lt_of_not_ge hlow
      have htop : a + offset + σ < s + loss := by dsimp [loss]; omega
      obtain ⟨C, hC, hbound⟩ := hinterp base (a + offset) (s + loss)
        hb₀ hmid htop
      have hdeneq : ((s + loss : ℕ) : ℝ) - base = (s : ℝ) + 1 := by
        simp only [loss, Nat.cast_add, Nat.cast_one]
        ring
      have hα : 0 ≤
          (((s + loss : ℕ) : ℝ) - (a + offset : ℕ) - σ) /
            (((s + loss : ℕ) : ℝ) - base) := by
        rw [hdeneq]
        apply div_nonneg _ hden.le
        have htopR : ((a + offset : ℕ) : ℝ) + σ < (s + loss : ℕ) := by
          exact_mod_cast htop
        linarith
      have hβ : 0 ≤
          (((a + offset : ℕ) : ℝ) - base + σ) /
            (((s + loss : ℕ) : ℝ) - base) := by
        rw [hdeneq]
        apply div_nonneg _ hden.le
        have hmidR : (base : ℝ) < (a + offset : ℕ) := by exact_mod_cast hmid
        linarith [Nat.cast_nonneg (α := ℝ) σ]
      have hβle :
          (((a + offset : ℕ) : ℝ) - base + σ) /
            (((s + loss : ℕ) : ℝ) - base) ≤ (a : ℝ) / ((s : ℝ) + 1) := by
        rw [hdeneq]
        apply div_le_div_of_nonneg_right _ hden.le
        have hoffR : (offset : ℝ) + σ ≤ base := by exact_mod_cast hoff
        simp only [Nat.cast_add]
        linarith
      refine ⟨max 1 C, le_max_left _ _, fun x hx => ?_⟩
      have hp0 : 0 ≤ p (s + loss) x := apply_nonneg _ _
      have hlowpow :
          (p base x) ^
            ((((s + loss : ℕ) : ℝ) - (a + offset : ℕ) - σ) /
              (((s + loss : ℕ) : ℝ) - base)) ≤ 1 :=
        Real.rpow_le_one (apply_nonneg _ _) hx hα
      have hhighpow :
          (p (s + loss) x) ^
            ((((a + offset : ℕ) : ℝ) - base + σ) /
              (((s + loss : ℕ) : ℝ) - base)) ≤
          (1 + p (s + loss) x) ^
            ((((a + offset : ℕ) : ℝ) - base + σ) /
              (((s + loss : ℕ) : ℝ) - base)) :=
        Real.rpow_le_rpow hp0 (by linarith) hβ
      have hpower :
          (1 + p (s + loss) x) ^
            ((((a + offset : ℕ) : ℝ) - base + σ) /
              (((s + loss : ℕ) : ℝ) - base)) ≤
          (1 + p (s + loss) x) ^ ((a : ℝ) / ((s : ℝ) + 1)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hβle
      calc
        p (a + offset) x ≤
            C * (p base x) ^
              ((((s + loss : ℕ) : ℝ) - (a + offset : ℕ) - σ) /
                (((s + loss : ℕ) : ℝ) - base)) *
              (p (s + loss) x) ^
                ((((a + offset : ℕ) : ℝ) - base + σ) /
                  (((s + loss : ℕ) : ℝ) - base)) := hbound x
        _ ≤ C * 1 * (1 + p (s + loss) x) ^
              ((((a + offset : ℕ) : ℝ) - base + σ) /
                (((s + loss : ℕ) : ℝ) - base)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlowpow hC) hhighpow
            (Real.rpow_nonneg hp0 _) (mul_nonneg hC zero_le_one)
        _ ≤ C * (1 + p (s + loss) x) ^ ((a : ℝ) / ((s : ℝ) + 1)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower hC
        _ ≤ max 1 C * (1 + p (s + loss) x) ^ ((a : ℝ) / ((s : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)
  exact ⟨base, loss, hsingle⟩

/-- All finite product arities and all spatial orders use one common base
and loss.  The offset is the fixed cost of each individual jet evaluation. -/
theorem exists_oneHighProductBounds (p : ℕ → Seminorm ℝ E)
    (hp : Monotone p) (hinterp : HasInterpolation p) (offset : ℕ) :
    ∃ base loss : ℕ, ∀ k s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ a : Fin k → ℕ, (∑ i, a i ≤ s) → ∀ v : Fin k → E,
        (∀ i, p base (v i) ≤ 1) →
        ∏ i, p (a i + offset) (v i) ≤
          C * (1 + ∑ i, p (s + loss) (v i)) := by
  classical
  obtain ⟨base, loss, hsingle⟩ := exists_interpolatedJetBounds p hp hinterp offset
  refine ⟨base, loss, fun k s => ?_⟩
  choose c hc hcb using
    (fun a : Fin (s + 1) => hsingle s a.val (Nat.le_of_lt_succ a.isLt))
  let M : ℝ := ∑ a : Fin (s + 1), c a
  have hM : 0 ≤ M := Finset.sum_nonneg (fun a _ => zero_le_one.trans (hc a))
  have hcM (a : Fin (s + 1)) : c a ≤ M :=
    Finset.single_le_sum (fun j _ => zero_le_one.trans (hc j)) (Finset.mem_univ a)
  refine ⟨M ^ k, pow_nonneg hM _, fun a ha v hv => ?_⟩
  have hai (i : Fin k) : a i ≤ s :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)).trans ha
  have hfactor (i : Fin k) :
      p (a i + offset) (v i) ≤
        M * (1 + p (s + loss) (v i)) ^ ((a i : ℝ) / ((s : ℝ) + 1)) :=
    (hcb ⟨a i, Nat.lt_succ_of_le (hai i)⟩ (v i) (hv i)).trans
      (mul_le_mul_of_nonneg_right (hcM _) (Real.rpow_nonneg
        (by linarith [apply_nonneg (p (s + loss)) (v i)]) _))
  calc
    ∏ i, p (a i + offset) (v i) ≤
        ∏ i, M * (1 + p (s + loss) (v i)) ^ ((a i : ℝ) / ((s : ℝ) + 1)) :=
      Finset.prod_le_prod₀ (fun i _ => apply_nonneg _ _) (fun i _ => hfactor i)
    _ = M ^ k * ∏ i, (1 + p (s + loss) (v i)) ^ ((a i : ℝ) / ((s : ℝ) + 1)) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ M ^ k * (1 + ∑ i, p (s + loss) (v i)) :=
      mul_le_mul_of_nonneg_left
        (prod_one_add_rpow_le_one_add_sum
          (fun i => p (s + loss) (v i)) (fun i => (a i : ℝ) / ((s : ℝ) + 1))
          (fun i => apply_nonneg _ _) (fun i => by positivity)
          (sum_order_fractions_le_one a ha)) (pow_nonneg hM _)

end SeminormProducts

section MultilinearProducts

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- A raw finite product estimate for a genuine multilinear map gives the
exact homogeneous one-high-factor expression.  All choices of factor
slots, orders, base points and maps share the same base and loss. -/
theorem exists_oneHighMultilinearProductBounds (p : ℕ → Seminorm ℝ E)
    (hp : Monotone p) (hinterp : HasInterpolation p) (offset : ℕ) :
    ∃ base loss : ℕ, ∀ k factors s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ a : Fin factors → ℕ, (∑ i, a i ≤ s) →
      ∀ select : Fin factors → Fin (k + 1),
      ∀ x : E, p base x ≤ 1 →
      ∀ A : E [×k]→L[ℝ] F, ∀ q : Seminorm ℝ F, ∀ K : ℝ, 0 ≤ K →
        (∀ v : Fin k → E, q (A v) ≤
          K * ∏ i, p (a i + offset) ((Fin.cons x v : Fin (k + 1) → E) (select i))) →
        ∀ v : Fin k → E, q (A v) ≤
          K * C * multilinearTameSize (p base) (p (s + loss)) k
            (1 + p (s + loss) x) v := by
  classical
  obtain ⟨base, loss, hproduct⟩ := exists_oneHighProductBounds p hp hinterp offset
  refine ⟨base, loss, fun k factors s => ?_⟩
  obtain ⟨C, hC, hCb⟩ := hproduct factors s
  have hfactors : 0 ≤ (factors : ℝ) + 1 := by positivity
  refine ⟨C * ((factors : ℝ) + 1), mul_nonneg hC hfactors, ?_⟩
  intro a ha select x hx A q K hK hraw
  apply multilinear_bound_of_unitBall A q (p base) (p (s + loss))
    (mul_nonneg hK (mul_nonneg hC hfactors))
  intro v hv
  let w : Fin factors → E := fun i => (Fin.cons x v : Fin (k + 1) → E) (select i)
  have hw (i : Fin factors) : p base (w i) ≤ 1 := by
    exact Fin.cases
      (motive := fun j : Fin (k + 1) =>
        p base ((Fin.cons x v : Fin (k + 1) → E) j) ≤ 1)
      hx (fun j => (hv j).le) (select i)
  let U : ℝ := p (s + loss) x + ∑ j, p (s + loss) (v j)
  have hx0 : 0 ≤ p (s + loss) x := apply_nonneg _ _
  have hvsum : 0 ≤ ∑ j, p (s + loss) (v j) :=
    Finset.sum_nonneg (fun j _ => apply_nonneg _ _)
  have hU : 0 ≤ U := add_nonneg hx0 hvsum
  have hslot (i : Fin factors) : p (s + loss) (w i) ≤ U := by
    have hxU : p (s + loss) x ≤ U := le_add_of_nonneg_right hvsum
    have hvU (j : Fin k) : p (s + loss) (v j) ≤ U :=
      (Finset.single_le_sum (fun j _ => apply_nonneg (p (s + loss)) (v j))
        (Finset.mem_univ j)).trans (le_add_of_nonneg_left hx0)
    exact Fin.cases
      (motive := fun j : Fin (k + 1) =>
        p (s + loss) ((Fin.cons x v : Fin (k + 1) → E) j) ≤ U)
      hxU hvU (select i)
  have hsumw : ∑ i, p (s + loss) (w i) ≤ (factors : ℝ) * U := by
    calc
      ∑ i, p (s + loss) (w i) ≤ ∑ _i : Fin factors, U :=
        Finset.sum_le_sum (fun i _ => hslot i)
      _ = (factors : ℝ) * U := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have haffine : 1 + ∑ i, p (s + loss) (w i) ≤
      ((factors : ℝ) + 1) * (1 + U) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) factors]
  calc
    q (A v) ≤ K * ∏ i, p (a i + offset) (w i) := hraw v
    _ ≤ K * (C * (1 + ∑ i, p (s + loss) (w i))) :=
      mul_le_mul_of_nonneg_left (hCb a ha w hw) hK
    _ ≤ K * (C * (((factors : ℝ) + 1) * (1 + U))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left haffine hC) hK
    _ = K * (C * ((factors : ℝ) + 1)) *
        ((1 + p (s + loss) x) + ∑ i, p (s + loss) (v i)) := by
      dsimp [U]
      ring

end MultilinearProducts

end ContinuousFlexibility.Analysis
