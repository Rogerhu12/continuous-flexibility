import ContinuousFlexibility.Analysis.PositiveConformalMaterialJets

/-!
# Actual negative characteristic speeds with one fixed derivative loss

The two characteristic speeds are fixed smooth functions of the three
coefficient values on a > 0 and b² - ac > 0. A lower bound for these two
denominators and the actual coefficient jets therefore give all speed
jets. The coefficient value bound is derived from the order-zero input
on one low state ball. The low order and derivative loss are chosen
before the lower bounds and all component-dependent jet constants.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

def negativeCharacteristicValue (plus : Bool) (x : ℝ × ℝ × ℝ) : ℝ :=
  if plus then x.2.1 / x.1 + Real.sqrt (x.2.1 ^ 2 - x.1 * x.2.2) / x.1
  else x.2.1 / x.1 - Real.sqrt (x.2.1 ^ 2 - x.1 * x.2.2) / x.1

def negativeCharacteristicField (plus : Bool) (A : SymmetricCoefficients) :
    PolarPoint → ℝ :=
  if plus then plusCharacteristicSpeed A else minusCharacteristicSpeed A

def negativeCharacteristicValueDomain : Set (ℝ × ℝ × ℝ) :=
  {x | 0 < x.1 ∧ 0 < x.2.1 ^ 2 - x.1 * x.2.2}

theorem negativeCharacteristicValueDomain_isOpen :
    IsOpen negativeCharacteristicValueDomain :=
  (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_const
      ((continuous_snd.fst.pow 2).sub (continuous_fst.mul continuous_snd.snd)))

theorem negativeCharacteristicValue_contDiffAt (plus : Bool)
    {x : ℝ × ℝ × ℝ} (hx : x ∈ negativeCharacteristicValueDomain) :
    ContDiffAt ℝ ∞ (negativeCharacteristicValue plus) x := by
  have ha : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => q.1) x := contDiffAt_fst
  have hb : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => q.2.1) x := contDiffAt_snd.fst
  have hc : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ × ℝ => q.2.2) x := contDiffAt_snd.snd
  have hd := hb.fun_div ha hx.1.ne'
  have hv := (((hb.pow 2).sub (ha.mul hc)).sqrt hx.2.ne').fun_div ha hx.1.ne'
  cases plus
  · simpa only [negativeCharacteristicValue, Bool.false_eq_true, ite_false] using hd.sub hv
  · simpa only [negativeCharacteristicValue, ite_true] using hd.add hv

private theorem negativeCharacteristicValue_outer_bounds
    {l κ M : ℝ} (hl : 0 < l) (hκ : 0 < κ) :
    ∃ D : ℕ → ℝ, (∀ n, 1 ≤ D n) ∧ ∀ plus : Bool, ∀ n : ℕ,
      ∀ x : ℝ × ℝ × ℝ,
        |x.1| ≤ M → |x.2.1| ≤ M → |x.2.2| ≤ M →
        l ≤ x.1 → κ ≤ x.2.1 ^ 2 - x.1 * x.2.2 →
        ‖iteratedFDeriv ℝ n (negativeCharacteristicValue plus) x‖ ≤ D n := by
  let K : Set (ℝ × ℝ × ℝ) :=
    (Icc (-M) M ×ˢ Icc (-M) M ×ˢ Icc (-M) M) ∩
      {x | l ≤ x.1 ∧ κ ≤ x.2.1 ^ 2 - x.1 * x.2.2}
  have hK : IsCompact K :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).inter_right
      ((isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_const
          ((continuous_snd.fst.pow 2).sub (continuous_fst.mul continuous_snd.snd))))
  have hKV : K ⊆ negativeCharacteristicValueDomain :=
    fun _ hx => ⟨hl.trans_le hx.2.1, hκ.trans_le hx.2.2⟩
  have hbound (plus : Bool) (n : ℕ) : ∃ C : ℝ, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ n (negativeCharacteristicValue plus) x‖ ≤ C := by
    have hf : ContDiffOn ℝ ∞ (negativeCharacteristicValue plus)
        negativeCharacteristicValueDomain :=
      fun x hx => (negativeCharacteristicValue_contDiffAt plus hx).contDiffWithinAt
    have hc := hf.continuousOn_iteratedFDerivWithin
      (m := n) (by simp) negativeCharacteristicValueDomain_isOpen.uniqueDiffOn
    have hc' : ContinuousOn (iteratedFDeriv ℝ n (negativeCharacteristicValue plus))
        negativeCharacteristicValueDomain := by
      apply hc.congr
      intro x hx
      exact (iteratedFDerivWithin_eq_iteratedFDeriv
        negativeCharacteristicValueDomain_isOpen.uniqueDiffOn
        ((negativeCharacteristicValue_contDiffAt plus hx).of_le
          (by simp : (n : ℕ∞ω) ≤ ∞)) hx).symm
    exact hK.exists_bound_of_continuousOn (hc'.mono hKV)
  choose C hC using hbound
  let D (n : ℕ) : ℝ := 1 + ∑ plus : Bool, |C plus n|
  refine ⟨D, fun n => le_add_of_nonneg_right
    (Finset.sum_nonneg fun _ _ => abs_nonneg _), ?_⟩
  intro plus n x ha hb hc hlx hκx
  have hx : x ∈ K := ⟨⟨abs_le.mp ha, abs_le.mp hb, abs_le.mp hc⟩, hlx, hκx⟩
  have hs : |C plus n| ≤ ∑ side : Bool, |C side n| :=
    Finset.single_le_sum (f := fun side : Bool => |C side n|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ plus)
  exact (hC plus n x hx).trans ((le_abs_self _).trans
    (hs.trans (le_add_of_nonneg_left zero_le_one)))

def NegativeCharacteristicJetEstimate
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (low inputLoss loss : ℕ)
    (l κ : ℝ) (A B : ℕ → ℝ) : Prop :=
  ∀ z : E, p low z ≤ 1 →
    ∀ U : Set PolarPoint, IsOpen U → ∀ C : SymmetricCoefficients,
      (∀ i : Fin 3, ContDiffOn ℝ ∞ (canonicalCoefficientComponent i C) U) →
    ∀ q ∈ U, l ≤ C.a q → κ ≤ C.b q ^ 2 - C.a q * C.c q →
      (∀ n : ℕ, ∀ i : Fin 3, ∀ a b : ℕ, a + b = n →
        |mixedDerivative a b (canonicalCoefficientComponent i C) q| ≤
          A n * (1 + p (n + inputLoss) z)) →
      (∀ plus : Bool, ∀ n : ℕ,
        ‖iteratedFDeriv ℝ n (negativeCharacteristicField plus C) q‖ ≤
          B n * (1 + p (n + loss) z)) ∧
      ∀ plus : Bool, ∀ a b : ℕ,
        |mixedDerivative a b (negativeCharacteristicField plus C) q| ≤
          B (a + b) * (1 + p ((a + b) + loss) z)

/-- Raw coefficient jets and genuine positive denominator bounds imply
all actual characteristic-speed jets. The common low order and loss do
not depend on either lower bound or on the raw jet constants. -/
theorem negativeCharacteristic_fixed_loss_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ low loss : ℕ, ∀ l κ : ℝ, 0 < l → 0 < κ →
      ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        NegativeCharacteristicJetEstimate p low inputLoss loss l κ A B := by
  obtain ⟨low, loss, hcomp⟩ := coordinateComposition_fixed_loss_material_bound
    (X := PolarPoint) (Y := ℝ × ℝ × ℝ) (Z := ℝ) hp hI inputLoss
  refine ⟨max low inputLoss, loss, ?_⟩
  intro l κ hl hκ A hA
  obtain ⟨D, hD, houter⟩ := negativeCharacteristicValue_outer_bounds hl hκ (M := 2 * A 0)
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
  intro z hz U hU C hC q hq hlow hdet hraw
  have hzlow : p low z ≤ 1 := (hp (le_max_left low inputLoss) z).trans hz
  have hzinput : p inputLoss z ≤ 1 := (hp (le_max_right low inputLoss) z).trans hz
  have hvalues (i : Fin 3) : |canonicalCoefficientComponent i C q| ≤ 2 * A 0 := by
    have hi : |canonicalCoefficientComponent i C q| ≤ A 0 * (1 + p inputLoss z) := by
      simpa only [mixedDerivative, iteratedDeriv_zero, zero_add] using hraw 0 i 0 0 rfl
    have hsum : 1 + p inputLoss z ≤ 2 := by linarith only [hzinput]
    exact hi.trans (by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hsum (zero_le_one.trans (hA 0)))
  have ha : ContDiffOn ℝ ∞ C.a U := by simpa [canonicalCoefficientComponent] using hC 0
  have hb : ContDiffOn ℝ ∞ C.b U := by simpa [canonicalCoefficientComponent] using hC 1
  have hc : ContDiffOn ℝ ∞ C.c U := by simpa [canonicalCoefficientComponent] using hC 2
  let v : PolarPoint → ℝ × ℝ × ℝ := fun x => (C.a x, C.b x, C.c x)
  have hv : ContDiffOn ℝ ∞ v U := ha.prodMk (hb.prodMk hc)
  have hvq : ContDiffAt ℝ ∞ v q := hv.contDiffAt (hU.mem_nhds hq)
  have hqV : v q ∈ negativeCharacteristicValueDomain := ⟨hl.trans_le hlow, hκ.trans_le hdet⟩
  have hva : |C.a q| ≤ 2 * A 0 := by simpa [canonicalCoefficientComponent] using hvalues 0
  have hvb : |C.b q| ≤ 2 * A 0 := by simpa [canonicalCoefficientComponent] using hvalues 1
  have hvc : |C.c q| ≤ 2 * A 0 := by simpa [canonicalCoefficientComponent] using hvalues 2
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
  have he (plus : Bool) :
      negativeCharacteristicField plus C = negativeCharacteristicValue plus ∘ v := by
    cases plus <;> rfl
  have hnorm (plus : Bool) (n : ℕ) :
      ‖iteratedFDeriv ℝ n (negativeCharacteristicField plus C) q‖ ≤
        B n * (1 + p (n + loss) z) := by
    rw [he plus]
    cases n with
    | zero =>
      have hv0 := houter plus 0 (v q) hva hvb hvc hlow hdet
      have hb0 := hDB.trans (le_mul_of_one_le_right (hB 0).le
        (le_add_of_nonneg_right (apply_nonneg (p (0 + loss)) z)))
      simpa only [norm_iteratedFDeriv_zero, Function.comp_apply] using hv0.trans hb0
    | succ n =>
      have hout (k : ℕ) (_hk : 1 ≤ k) :
          ‖iteratedFDeriv ℝ k (negativeCharacteristicValue plus) (v q)‖ ≤
            R k * (1 : ℝ) ^ (R k) * (1 + p (k + inputLoss) z) := by
        simpa only [Real.one_rpow, mul_one] using
          (houter plus k (v q) hva hvb hvc hlow hdet).trans
            ((hDR k).trans (le_mul_of_one_le_right (zero_le_one.trans (hR k))
              (le_add_of_nonneg_right (apply_nonneg (p (k + inputLoss)) z))))
      have h := hQbound z hzlow 1 le_rfl (negativeCharacteristicValue plus) v q
        (negativeCharacteristicValue_contDiffAt plus hqV) hvq hout hinner n
      have h' : ‖iteratedFDeriv ℝ (n + 1) (negativeCharacteristicValue plus ∘ v) q‖ ≤
          Q n * (1 + p ((n + 1) + loss) z) := by
        simpa only [Real.one_rpow, mul_one] using h
      exact h'.trans (mul_le_mul_of_nonneg_right (hQB n)
        (add_nonneg zero_le_one (apply_nonneg _ _)))
  refine ⟨hnorm, ?_⟩
  intro plus a b
  let V := U ∩ v ⁻¹' negativeCharacteristicValueDomain
  have hV : IsOpen V := hv.continuousOn.isOpen_inter_preimage hU negativeCharacteristicValueDomain_isOpen
  have hfield : ContDiffOn ℝ ∞ (negativeCharacteristicField plus C) V := by
    rw [he plus]
    intro x hx
    exact (ContDiffAt.comp (f := v) (g := negativeCharacteristicValue plus) x
      (negativeCharacteristicValue_contDiffAt plus hx.2)
      (hv.contDiffAt (hU.mem_nhds hx.1))).contDiffWithinAt
  exact (abs_mixedDerivative_le_norm_iteratedFDeriv hV hfield a b ⟨hq, hqV⟩).trans
    (hnorm plus (a + b))

end ContinuousFlexibility.Analysis
