import ContinuousFlexibility.Analysis.PositiveConformalFiniteInputs
import ContinuousFlexibility.Analysis.CoordinateCompositionMaterialBounds

/-!
# All actual conformal-input jets with one fixed derivative loss

The speed, shear, fourth-root height, and its logarithm are four fixed
smooth functions of the three coefficient values on the positive
definite region. A compact value set gives all outer derivatives. The
existing ordered-partition interpolation theorem then keeps one high
state factor. The common low order and loss precede the value bounds,
the coefficient family, the physical point, and the derivative order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem positiveConformalValue_all_outer_bounds
    {l κ M : ℝ} (hl : 0 < l) (hκ : 0 < κ) :
    ∃ D : ℕ → ℝ, (∀ n, 1 ≤ D n) ∧ ∀ i : Fin 4, ∀ n : ℕ,
      ∀ x : ℝ × ℝ × ℝ,
        |x.1| ≤ M → |x.2.1| ≤ M → |x.2.2| ≤ M →
        l ≤ x.1 → κ ≤ x.1 * x.2.2 - x.2.1 ^ 2 →
        ‖iteratedFDeriv ℝ n (positiveConformalValue i) x‖ ≤ D n := by
  let K : Set (ℝ × ℝ × ℝ) :=
    (Icc (-M) M ×ˢ Icc (-M) M ×ˢ Icc (-M) M) ∩
      {x | l ≤ x.1 ∧ κ ≤ x.1 * x.2.2 - x.2.1 ^ 2}
  have hK : IsCompact K :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).inter_right
      ((isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_const
          ((continuous_fst.mul continuous_snd.snd).sub (continuous_snd.fst.pow 2))))
  have hKV : K ⊆ positiveConformalValueDomain :=
    fun _ hx => ⟨hl.trans_le hx.2.1, hκ.trans_le hx.2.2⟩
  have hbound (i : Fin 4) (n : ℕ) : ∃ C : ℝ, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ n (positiveConformalValue i) x‖ ≤ C := by
    have hΦ : ContDiffOn ℝ ∞ (positiveConformalValue i) positiveConformalValueDomain :=
      fun x hx => (positiveConformalValue_contDiffAt i hx).contDiffWithinAt
    have hc := hΦ.continuousOn_iteratedFDerivWithin
      (m := n) (by simp) positiveConformalValueDomain_isOpen.uniqueDiffOn
    have hc' : ContinuousOn (iteratedFDeriv ℝ n (positiveConformalValue i))
        positiveConformalValueDomain := by
      apply hc.congr
      intro x hx
      exact (iteratedFDerivWithin_eq_iteratedFDeriv
        positiveConformalValueDomain_isOpen.uniqueDiffOn
        ((positiveConformalValue_contDiffAt i hx).of_le
          (by simp : (n : ℕ∞ω) ≤ ∞)) hx).symm
    exact hK.exists_bound_of_continuousOn (hc'.mono hKV)
  choose C hC using hbound
  let D (n : ℕ) : ℝ := 1 + ∑ i : Fin 4, |C i n|
  refine ⟨D, fun n => le_add_of_nonneg_right
    (Finset.sum_nonneg fun _ _ => abs_nonneg _), ?_⟩
  intro i n x ha hb hc hlx hκx
  have hx : x ∈ K := ⟨⟨abs_le.mp ha, abs_le.mp hb, abs_le.mp hc⟩, hlx, hκx⟩
  have hs : |C i n| ≤ ∑ j : Fin 4, |C j n| :=
    Finset.single_le_sum (f := fun j : Fin 4 => |C j n|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  exact (hC i n x hx).trans ((le_abs_self _).trans
    (hs.trans (le_add_of_nonneg_left zero_le_one)))

/-- The actual coefficient-value triple inherits the scalar mixed-jet
bound. This is also used for the negative-type characteristic speed. -/
theorem norm_iteratedFDeriv_coefficientValues_le
    {U : Set PolarPoint} (hU : IsOpen U) {A : SymmetricCoefficients}
    (hA : ∀ i : Fin 3, ContDiffOn ℝ ∞ (canonicalCoefficientComponent i A) U)
    {q : PolarPoint} (hq : q ∈ U) (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hraw : ∀ i : Fin 3, ∀ a b : ℕ, a + b = n →
      |mixedDerivative a b (canonicalCoefficientComponent i A) q| ≤ M) :
    ‖iteratedFDeriv ℝ n (fun x => (A.a x, A.b x, A.c x)) q‖ ≤ (2 : ℝ) ^ n * M := by
  have hj (i : Fin 3) :
      ‖iteratedFDeriv ℝ n (canonicalCoefficientComponent i A) q‖ ≤ (2 : ℝ) ^ n * M :=
    norm_iteratedFDeriv_le_of_mixedDerivative hU (hA i) n hq hM
      (fun a b hab => by simpa only [Real.norm_eq_abs] using hraw i a b hab)
  have ha : ContDiffAt ℝ (n : ℕ∞ω) A.a q := by
    simpa [canonicalCoefficientComponent] using
      ((hA 0).contDiffAt (hU.mem_nhds hq)).of_le (by simp : (n : ℕ∞ω) ≤ ∞)
  have hb : ContDiffAt ℝ (n : ℕ∞ω) A.b q := by
    simpa [canonicalCoefficientComponent] using
      ((hA 1).contDiffAt (hU.mem_nhds hq)).of_le (by simp : (n : ℕ∞ω) ≤ ∞)
  have hc : ContDiffAt ℝ (n : ℕ∞ω) A.c q := by
    simpa [canonicalCoefficientComponent] using
      ((hA 2).contDiffAt (hU.mem_nhds hq)).of_le (by simp : (n : ℕ∞ω) ≤ ∞)
  rw [iteratedFDeriv_prodMk ha (hb.prodMk hc) le_rfl,
    ContinuousMultilinearMap.opNorm_prod,
    iteratedFDeriv_prodMk hb hc le_rfl, ContinuousMultilinearMap.opNorm_prod]
  exact max_le (by simpa [canonicalCoefficientComponent] using hj 0)
    (max_le (by simpa [canonicalCoefficientComponent] using hj 1)
      (by simpa [canonicalCoefficientComponent] using hj 2))

def PositiveConformalInputEstimate
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (low inputLoss loss : ℕ)
    (l κ M : ℝ) (A B : ℕ → ℝ) : Prop :=
      ∀ z : E, p low z ≤ 1 →
      ∀ U : Set PolarPoint, IsOpen U → ∀ C : SymmetricCoefficients,
        (∀ i : Fin 3, ContDiffOn ℝ ∞ (canonicalCoefficientComponent i C) U) →
      ∀ q ∈ U, l ≤ C.a q → κ ≤ C.a q * C.c q - C.b q ^ 2 →
        (∀ i : Fin 3, |canonicalCoefficientComponent i C q| ≤ M) →
        (∀ n : ℕ, ∀ i : Fin 3, ∀ a b : ℕ, a + b = n →
          |mixedDerivative a b (canonicalCoefficientComponent i C) q| ≤
            A n * (1 + p (n + inputLoss) z)) →
        (∀ i : Fin 4, ∀ n : ℕ,
          ‖iteratedFDeriv ℝ n (positiveConformalInputField i C) q‖ ≤
            B n * (1 + p (n + loss) z)) ∧
        ∀ i : Fin 4, ∀ a b : ℕ,
          |mixedDerivative a b (positiveConformalInputField i C) q| ≤
            B (a + b) * (1 + p ((a + b) + loss) z)

/-- Positive coefficient values in a fixed compact set and actual raw
coefficient jets imply all actual jets of the four conformal inputs.
Only the low state order is restricted; the high seminorm is retained. -/
theorem positiveConformalInputs_fixed_loss_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ low loss : ℕ, ∀ l κ M : ℝ, 0 < l → 0 < κ →
      ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        PositiveConformalInputEstimate p low inputLoss loss l κ M A B := by
  obtain ⟨low, loss, hcomp⟩ := coordinateComposition_fixed_loss_material_bound
    (X := PolarPoint) (Y := ℝ × ℝ × ℝ) (Z := ℝ) hp hI inputLoss
  refine ⟨low, loss, ?_⟩
  intro l κ M hl hκ A hA
  obtain ⟨D, hD, houter⟩ := positiveConformalValue_all_outer_bounds hl hκ (M := M)
  let R (n : ℕ) : ℝ := max 1 (max (D n) ((2 : ℝ) ^ n * A n))
  have hR (n : ℕ) : 1 ≤ R n := le_max_left _ _
  have hDR (n : ℕ) : D n ≤ R n := (le_max_left _ _).trans (le_max_right _ _)
  have hAR (n : ℕ) : (2 : ℝ) ^ n * A n ≤ R n :=
    (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨Q, hQ, hQbound⟩ := hcomp R hR
  let B (n : ℕ) : ℝ := 1 + D 0 + Q (n - 1)
  have hB (n : ℕ) : 0 < B n := by dsimp only [B]; linarith [hD 0, hQ (n - 1)]
  have hDB : D 0 ≤ B 0 := by dsimp only [B]; linarith [hQ (0 - 1)]
  have hQB (n : ℕ) : Q n ≤ B (n + 1) := by
    simp only [B, Nat.add_sub_cancel]
    linarith [hD 0]
  refine ⟨B, hB, ?_⟩
  intro z hz U hU C hC q hq hlow hdet hvalues hraw
  have ha : ContDiffOn ℝ ∞ C.a U := by simpa [canonicalCoefficientComponent] using hC 0
  have hb : ContDiffOn ℝ ∞ C.b U := by simpa [canonicalCoefficientComponent] using hC 1
  have hc : ContDiffOn ℝ ∞ C.c U := by simpa [canonicalCoefficientComponent] using hC 2
  let v : PolarPoint → ℝ × ℝ × ℝ := fun x => (C.a x, C.b x, C.c x)
  have hv : ContDiffOn ℝ ∞ v U := ha.prodMk (hb.prodMk hc)
  have hvq : ContDiffAt ℝ ∞ v q := hv.contDiffAt (hU.mem_nhds hq)
  have hqV : v q ∈ positiveConformalValueDomain := ⟨hl.trans_le hlow, hκ.trans_le hdet⟩
  have hva : |C.a q| ≤ M := by simpa [canonicalCoefficientComponent] using hvalues 0
  have hvb : |C.b q| ≤ M := by simpa [canonicalCoefficientComponent] using hvalues 1
  have hvc : |C.c q| ≤ M := by simpa [canonicalCoefficientComponent] using hvalues 2
  have hinner (n : ℕ) (_hn : 1 ≤ n) :
      ‖iteratedFDeriv ℝ n v q‖ ≤
        R n * (1 : ℝ) ^ (R n) * (1 + p (n + inputLoss) z) := by
    have hM : 0 ≤ A n * (1 + p (n + inputLoss) z) :=
      mul_nonneg (zero_le_one.trans (hA n)) (add_nonneg zero_le_one (apply_nonneg _ _))
    have hn := norm_iteratedFDeriv_coefficientValues_le hU hC hq n hM (hraw n)
    have hstep : (2 : ℝ) ^ n * (A n * (1 + p (n + inputLoss) z)) ≤
        R n * (1 + p (n + inputLoss) z) := by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_right (hAR n)
          (add_nonneg zero_le_one (apply_nonneg (p (n + inputLoss)) z)))
    simpa only [Real.one_rpow, mul_one] using hn.trans hstep
  have hnorm (i : Fin 4) (n : ℕ) :
      ‖iteratedFDeriv ℝ n (positiveConformalInputField i C) q‖ ≤
        B n * (1 + p (n + loss) z) := by
    have he : positiveConformalInputField i C = positiveConformalValue i ∘ v := by
      funext x
      simp only [Function.comp_apply]
      unfold positiveConformalInputField positiveConformalValue
      split_ifs <;> rfl
    rw [he]
    cases n with
    | zero =>
      have hv0 := houter i 0 (v q) hva hvb hvc hlow hdet
      have hb0 := hDB.trans (le_mul_of_one_le_right (hB 0).le
        (le_add_of_nonneg_right (apply_nonneg (p (0 + loss)) z)))
      simpa only [norm_iteratedFDeriv_zero, Function.comp_apply] using hv0.trans hb0
    | succ n =>
      have hout (k : ℕ) (_hk : 1 ≤ k) :
          ‖iteratedFDeriv ℝ k (positiveConformalValue i) (v q)‖ ≤
            R k * (1 : ℝ) ^ (R k) * (1 + p (k + inputLoss) z) := by
        simpa only [Real.one_rpow, mul_one] using
          (houter i k (v q) hva hvb hvc hlow hdet).trans
            ((hDR k).trans (le_mul_of_one_le_right (zero_le_one.trans (hR k))
              (le_add_of_nonneg_right (apply_nonneg (p (k + inputLoss)) z))))
      have h := hQbound z hz 1 le_rfl (positiveConformalValue i) v q
        (positiveConformalValue_contDiffAt i hqV) hvq hout hinner n
      have h' : ‖iteratedFDeriv ℝ (n + 1) (positiveConformalValue i ∘ v) q‖ ≤
          Q n * (1 + p ((n + 1) + loss) z) := by
        simpa only [Real.one_rpow, mul_one] using h
      exact h'.trans (mul_le_mul_of_nonneg_right (hQB n)
        (add_nonneg zero_le_one (apply_nonneg _ _)))
  refine ⟨hnorm, ?_⟩
  intro i a b
  let V := U ∩ v ⁻¹' positiveConformalValueDomain
  have hV : IsOpen V := hv.continuousOn.isOpen_inter_preimage hU positiveConformalValueDomain_isOpen
  have hfield : ContDiffOn ℝ ∞ (positiveConformalInputField i C) V := by
    intro x hx
    have he : positiveConformalInputField i C = positiveConformalValue i ∘ v := by
      funext y
      simp only [Function.comp_apply]
      unfold positiveConformalInputField positiveConformalValue
      split_ifs <;> rfl
    rw [he]
    exact (ContDiffAt.comp (f := v) (g := positiveConformalValue i) x
      (positiveConformalValue_contDiffAt i hx.2)
      (hv.contDiffAt (hU.mem_nhds hx.1))).contDiffWithinAt
  exact (abs_mixedDerivative_le_norm_iteratedFDeriv hV hfield a b ⟨hq, hqV⟩).trans
    (hnorm i (a + b))

end ContinuousFlexibility.Analysis
