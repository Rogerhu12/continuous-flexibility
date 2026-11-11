import ContinuousFlexibility.Statements.RadialTargets
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Local bounds for the actual matching formula

The estimates below use the actual inverse, source restrictions and Poisson
columns in ActualMatchedRepresentation. The four inner/outer correction
terms are retained separately. No global kernel estimate, weight exponent,
or frequency-uniform geometric estimate is assumed.

RadialModePair has the ordinary product norm. Its manually defined pairing
therefore has norm at most two; it is not treated as a Hilbert product.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Statements
open scoped BigOperators RealInnerProductSpace

/-- A two-dimensional matrix bound with the entrywise maximum convention. -/
theorem matchedCell_matrixApply_bound (A : RadialMatrix) (x : Fin 2 → ℝ)
    {a b : ℝ} (ha : 0 ≤ a)
    (hA : ∀ i j, |A i j| ≤ a) (hx : ∀ j, |x j| ≤ b) (i : Fin 2) :
    |radialMatrixApply A x i| ≤ 2 * a * b := by
  calc
    |radialMatrixApply A x i| = |A i 0 * x 0 + A i 1 * x 1| := by
      simp only [radialMatrixApply, Fin.sum_univ_two]
    _ ≤ |A i 0| * |x 0| + |A i 1| * |x 1| := by
      simpa only [abs_mul] using
        abs_add_le (A i 0 * x 0) (A i 1 * x 1)
    _ ≤ a * b + a * b :=
      add_le_add (mul_le_mul (hA i 0) (hx 0) (abs_nonneg _) ha)
        (mul_le_mul (hA i 1) (hx 1) (abs_nonneg _) ha)
    _ = 2 * a * b := by ring

/-- The corresponding estimate for a two-column Poisson map. -/
theorem matchedCell_sum_smul_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x : Fin 2 → ℝ) (v : Fin 2 → E)
    {a b : ℝ} (ha : 0 ≤ a)
    (hx : ∀ i, |x i| ≤ a) (hv : ∀ i, ‖v i‖ ≤ b) :
    ‖∑ i, x i • v i‖ ≤ 2 * a * b := by
  rw [Fin.sum_univ_two]
  calc
    ‖x 0 • v 0 + x 1 • v 1‖ ≤ ‖x 0 • v 0‖ + ‖x 1 • v 1‖ :=
      norm_add_le _ _
    _ = |x 0| * ‖v 0‖ + |x 1| * ‖v 1‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ a * b + a * b :=
      add_le_add (mul_le_mul (hx 0) (hv 0) (norm_nonneg _) ha)
        (mul_le_mul (hx 1) (hv 1) (norm_nonneg _) ha)
    _ = 2 * a * b := by ring

/-- All normalized matrices in the frozen representation have bounded
entries. The bound on Db follows from its diagonal approximation and the
upper bound on the return margin. -/
theorem actualMatchedRepresentation_matrixBounds {D : ReferenceData}
    {G : RadialModePair D →L[ℝ] RadialModePair D} {M : RadialMatchingData D}
    (hM : ActualMatchedRepresentation D G M) :
    0 < M.margin ∧
      (∀ i j, |M.A i j| ≤ 1) ∧
      (∀ i j, |M.B i j| ≤ 1) ∧
      (∀ i j, |M.Db i j| ≤ 1) ∧
      (∀ i j, |M.Kinv i j| ≤ 4 / M.margin) := by
  rcases hM with
    ⟨_, _, _, _, hmargin, hD0, herror, hK, _, _, hoff, hnorm, _, _, _⟩
  have hA : ∀ i j, |M.A i j| ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [abs_le]
      constructor <;>
        nlinarith only [hnorm i, sq_nonneg (M.B i i),
          sq_nonneg (M.A i i - 1), sq_nonneg (M.A i i + 1)]
    · rw [(hoff i j hij).1, abs_zero]
      norm_num
  have hB : ∀ i j, |M.B i j| ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [abs_le]
      constructor <;>
        nlinarith only [hnorm i, sq_nonneg (M.A i i),
          sq_nonneg (M.B i i - 1), sq_nonneg (M.B i i + 1)]
    · rw [(hoff i j hij).2, abs_zero]
      norm_num
  have hprod : |M.A 0 0 * M.D0 0| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (hD0 0).2.1]
    calc
      |M.A 0 0| * M.D0 0 ≤ 1 * M.D0 0 :=
        mul_le_mul_of_nonneg_right (hA 0 0) (hD0 0).2.1.le
      _ ≤ 1 / 2 := by simpa only [one_mul] using (hD0 0).2.2.1
  have htriangle :
      |M.A 0 0 * M.D0 0 - M.B 0 0| ≤
        |M.A 0 0 * M.D0 0| + |M.B 0 0| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (M.A 0 0 * M.D0 0) (-M.B 0 0)
  have hsmall : M.margin ≤ 3 / 2 := by
    linarith [(hD0 0).2.2.2, hB 0 0]
  refine ⟨hmargin, hA, hB, ?_, hK⟩
  intro i j
  have hdiag : |if i = j then M.D0 i else 0| ≤ 1 / 2 := by
    split_ifs
    · rw [abs_of_pos (hD0 i).2.1]
      exact (hD0 i).2.2.1
    · norm_num
  have hsplit : |M.Db i j| ≤
      |M.Db i j - (if i = j then M.D0 i else 0)| +
        |if i = j then M.D0 i else 0| := by
    simpa only [sub_add_cancel] using
      abs_add_le (M.Db i j - (if i = j then M.D0 i else 0))
        (if i = j then M.D0 i else 0)
  linarith [herror i j]

/-- Cauchy--Schwarz for the actual mode pairing and the product maximum norm. -/
theorem matchedCell_modePairing_bound (D : ReferenceData) (U F : RadialModePair D) :
    |modePairing D U F| ≤ 2 * ‖U‖ * ‖F‖ := by
  have hU₁ : ‖U.1‖ ≤ ‖U‖ := by
    rw [Prod.norm_def]
    exact le_max_left _ _
  have hU₂ : |U.2| ≤ ‖U‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact le_max_right _ _
  have hF₁ : ‖F.1‖ ≤ ‖F‖ := by
    rw [Prod.norm_def]
    exact le_max_left _ _
  have hF₂ : |F.2| ≤ ‖F‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact le_max_right _ _
  calc
    |modePairing D U F| ≤ |⟪U.1, F.1⟫_ℝ| + |U.2 * F.2| :=
      abs_add_le _ _
    _ ≤ ‖U.1‖ * ‖F.1‖ + |U.2| * |F.2| := by
      rw [abs_mul]
      exact add_le_add (abs_real_inner_le_norm _ _) le_rfl
    _ ≤ ‖U‖ * ‖F‖ + ‖U‖ * ‖F‖ :=
      add_le_add (mul_le_mul hU₁ hF₁ (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul hU₂ hF₂ (abs_nonneg _) (norm_nonneg _))
    _ = 2 * ‖U‖ * ‖F‖ := by ring

/-- Localize the exact matching formula and retain its four correction
channels. The row bounds concern the actual source restrictions. -/
theorem matchedCell_formula_bound {D : ReferenceData}
    {G : RadialModePair D →L[ℝ] RadialModePair D} {M : RadialMatchingData D}
    (hM : ActualMatchedRepresentation D G M)
    (P : RadialModePair D →L[ℝ] RadialModePair D) (F : RadialModePair D)
    {I O p v h o : ℝ} (hp : 0 ≤ p) (hv : 0 ≤ v) (hh : 0 ≤ h) (ho : 0 ≤ o)
    (hI : ‖P (M.innerInverse (M.sourceInner F))‖ ≤ I)
    (hO : ‖P (M.outerInverse (M.sourceOuter F))‖ ≤ O)
    (hP : ∀ i, ‖P (M.innerPoisson i)‖ ≤ p)
    (hV : ∀ i, ‖P (M.outerPoisson i)‖ ≤ v)
    (hrow : ∀ i, |modePairing D (M.innerPoisson i) (M.sourceInner F)| ≤ h)
    (horow : ∀ i, |modePairing D (M.outerPoisson i) (M.sourceOuter F)| ≤ o) :
    ‖P (G F)‖ ≤ I + O +
      (8 * (4 / M.margin) * (p * h) + 4 * (4 / M.margin) * (p * o) +
        (48 * (4 / M.margin) + 4) * (v * h) +
        24 * (4 / M.margin) * (v * o)) := by
  rcases actualMatchedRepresentation_matrixBounds hM with
    ⟨hmargin, hA, hB, hDb, hK⟩
  rcases hM with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hformula⟩
  let κ : ℝ := 4 / M.margin
  have hκ : 0 ≤ κ := div_nonneg (by norm_num) hmargin.le
  let a : Fin 2 → ℝ := fun i => modePairing D (M.innerPoisson i) (M.sourceInner F)
  let b : Fin 2 → ℝ := fun i => modePairing D (M.outerPoisson i) (M.sourceOuter F)
  let x := radialMatrixApply M.Kinv (fun i => b i + radialMatrixApply M.A a i)
  let y := fun i => radialMatrixApply
    (fun i j => M.A i j + radialMatrixProduct M.B M.Db i j) x i -
      radialMatrixApply M.B a i
  let X : ℝ := 2 * κ * (o + 2 * h)
  let Y : ℝ := 6 * X + 2 * h
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have ha : ∀ i, |a i| ≤ h := hrow
  have hb : ∀ i, |b i| ≤ o := horow
  have hAa : ∀ i, |radialMatrixApply M.A a i| ≤ 2 * h := by
    intro i
    simpa only [mul_one] using
      matchedCell_matrixApply_bound M.A a (by norm_num : (0 : ℝ) ≤ 1) hA ha i
  have hBa : ∀ i, |radialMatrixApply M.B a i| ≤ 2 * h := by
    intro i
    simpa only [mul_one] using
      matchedCell_matrixApply_bound M.B a (by norm_num : (0 : ℝ) ≤ 1) hB ha i
  have hx : ∀ i, |x i| ≤ X := by
    intro i
    exact matchedCell_matrixApply_bound M.Kinv
      (fun j => b j + radialMatrixApply M.A a j) hκ hK
      (fun j => (abs_add_le _ _).trans (add_le_add (hb j) (hAa j))) i
  have hT : ∀ i j,
      |M.A i j + radialMatrixProduct M.B M.Db i j| ≤ 3 := by
    intro i j
    have hprod := matchedCell_matrixApply_bound M.B (fun k => M.Db k j)
      (by norm_num : (0 : ℝ) ≤ 1) hB (fun k => hDb k j) i
    change |radialMatrixProduct M.B M.Db i j| ≤ 2 * 1 * 1 at hprod
    calc
      |M.A i j + radialMatrixProduct M.B M.Db i j| ≤
          |M.A i j| + |radialMatrixProduct M.B M.Db i j| := abs_add_le _ _
      _ ≤ 1 + 2 * 1 * 1 := add_le_add (hA i j) hprod
      _ = 3 := by norm_num
  have hy : ∀ i, |y i| ≤ Y := by
    intro i
    have hTx := matchedCell_matrixApply_bound
      (fun i j => M.A i j + radialMatrixProduct M.B M.Db i j) x
      (by norm_num : (0 : ℝ) ≤ 3) hT hx i
    calc
      |y i| ≤
          |radialMatrixApply
            (fun i j => M.A i j + radialMatrixProduct M.B M.Db i j) x i| +
          |radialMatrixApply M.B a i| := by
        simpa only [y, sub_eq_add_neg, abs_neg] using
          abs_add_le
            (radialMatrixApply
              (fun i j => M.A i j + radialMatrixProduct M.B M.Db i j) x i)
            (-radialMatrixApply M.B a i)
      _ ≤ 2 * 3 * X + 2 * h := add_le_add hTx (hBa i)
      _ = Y := by dsimp only [Y]; ring
  have hinner :
      ‖∑ i, x i • P (M.innerPoisson i)‖ ≤ 2 * X * p :=
    matchedCell_sum_smul_bound x (fun i => P (M.innerPoisson i)) hX hx hP
  have houter :
      ‖∑ i, y i • P (M.outerPoisson i)‖ ≤ 2 * Y * v :=
    matchedCell_sum_smul_bound y (fun i => P (M.outerPoisson i)) hY hy hV
  have hrepresentation : G F =
      M.innerInverse (M.sourceInner F) + M.outerInverse (M.sourceOuter F) +
        (∑ i, x i • M.innerPoisson i) + (∑ i, y i • M.outerPoisson i) :=
    hformula F
  have hlocalized : P (G F) =
      P (M.innerInverse (M.sourceInner F)) + P (M.outerInverse (M.sourceOuter F)) +
        (∑ i, x i • P (M.innerPoisson i)) +
        (∑ i, y i • P (M.outerPoisson i)) := by
    rw [hrepresentation]
    simp only [map_add, map_sum, map_smul]
  calc
    ‖P (G F)‖ ≤ I + O + 2 * X * p + 2 * Y * v := by
      rw [hlocalized]
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add hI hO)) hinner)) houter)
    _ = I + O +
        (8 * (4 / M.margin) * (p * h) + 4 * (4 / M.margin) * (p * o) +
          (48 * (4 / M.margin) + 4) * (v * h) +
          24 * (4 / M.margin) * (v * o)) := by
      dsimp only [X, Y, κ]
      ring

/-- A coarser form useful when both kinds of Poisson columns share a
common geometric envelope. The preceding theorem retains the four terms. -/
theorem matchedCell_bound {D : ReferenceData}
    {G : RadialModePair D →L[ℝ] RadialModePair D} {M : RadialMatchingData D}
    (hM : ActualMatchedRepresentation D G M)
    (P : RadialModePair D →L[ℝ] RadialModePair D) (F : RadialModePair D)
    {I O p v h o : ℝ} (hp : 0 ≤ p) (hv : 0 ≤ v) (hh : 0 ≤ h) (ho : 0 ≤ o)
    (hI : ‖P (M.innerInverse (M.sourceInner F))‖ ≤ I)
    (hO : ‖P (M.outerInverse (M.sourceOuter F))‖ ≤ O)
    (hP : ∀ i, ‖P (M.innerPoisson i)‖ ≤ p)
    (hV : ∀ i, ‖P (M.outerPoisson i)‖ ≤ v)
    (hrow : ∀ i, |modePairing D (M.innerPoisson i) (M.sourceInner F)| ≤ h)
    (horow : ∀ i, |modePairing D (M.outerPoisson i) (M.sourceOuter F)| ≤ o) :
    ‖P (G F)‖ ≤ I + O + (4 + 48 * (4 / M.margin)) * (p + v) * (h + o) := by
  have hκ : 0 ≤ 4 / M.margin :=
    div_nonneg (by norm_num) (actualMatchedRepresentation_matrixBounds hM).1.le
  have h₁ : 8 * (4 / M.margin) * (p * h) ≤
      (4 + 48 * (4 / M.margin)) * (p * h) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hp hh)
  have h₂ : 4 * (4 / M.margin) * (p * o) ≤
      (4 + 48 * (4 / M.margin)) * (p * o) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hp ho)
  have h₃ : (48 * (4 / M.margin) + 4) * (v * h) =
      (4 + 48 * (4 / M.margin)) * (v * h) := by ring
  have h₄ : 24 * (4 / M.margin) * (v * o) ≤
      (4 + 48 * (4 / M.margin)) * (v * o) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hv ho)
  have hcorrection :=
    add_le_add (add_le_add (add_le_add h₁ h₂) h₃.le) h₄
  calc
    ‖P (G F)‖ ≤ I + O +
        (8 * (4 / M.margin) * (p * h) + 4 * (4 / M.margin) * (p * o) +
          (48 * (4 / M.margin) + 4) * (v * h) +
          24 * (4 / M.margin) * (v * o)) :=
      matchedCell_formula_bound hM P F hp hv hh ho hI hO hP hV hrow horow
    _ ≤ I + O +
        ((4 + 48 * (4 / M.margin)) * (p * h) +
          (4 + 48 * (4 / M.margin)) * (p * o) +
          (4 + 48 * (4 / M.margin)) * (v * h) +
          (4 + 48 * (4 / M.margin)) * (v * o)) :=
      add_le_add le_rfl hcorrection
    _ = I + O + (4 + 48 * (4 / M.margin)) * (p + v) * (h + o) := by ring

/-- Actual local inverse and Poisson cell norms control the actual matched
operator. The source restriction maps are identified by exact equalities;
the row identities express their Green symmetry with the source cell.
This statement keeps inner--inner, inner--outer, outer--inner and
outer--outer correction bounds separate. -/
theorem matchedCell_opNorm_bound {D : ReferenceData}
    {G : RadialModePair D →L[ℝ] RadialModePair D} {M : RadialMatchingData D}
    (hM : ActualMatchedRepresentation D G M)
    (P Q Si So : RadialModePair D →L[ℝ] RadialModePair D)
    (hSi : ∀ F, Si F = M.sourceInner F)
    (hSo : ∀ F, So F = M.sourceOuter F)
    {I O p v h o : ℝ}
    (hI₀ : 0 ≤ I) (hO₀ : 0 ≤ O) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hh : 0 ≤ h) (ho : 0 ≤ o)
    (hI : ‖P ∘L M.innerInverse ∘L Si ∘L Q‖ ≤ I)
    (hO : ‖P ∘L M.outerInverse ∘L So ∘L Q‖ ≤ O)
    (hP : ∀ i, ‖P (M.innerPoisson i)‖ ≤ p)
    (hV : ∀ i, ‖P (M.outerPoisson i)‖ ≤ v)
    (hH : ∀ i, ‖Q (M.innerPoisson i)‖ ≤ h)
    (hW : ∀ i, ‖Q (M.outerPoisson i)‖ ≤ o)
    (hrow : ∀ i F,
      modePairing D (M.innerPoisson i) (M.sourceInner (Q F)) =
        modePairing D (Q (M.innerPoisson i)) F)
    (horow : ∀ i F,
      modePairing D (M.outerPoisson i) (M.sourceOuter (Q F)) =
        modePairing D (Q (M.outerPoisson i)) F) :
    ‖P ∘L G ∘L Q‖ ≤ I + O +
      (16 * (4 / M.margin) * (p * h) + 8 * (4 / M.margin) * (p * o) +
        (96 * (4 / M.margin) + 8) * (v * h) +
        48 * (4 / M.margin) * (v * o)) := by
  have hκ : 0 ≤ 4 / M.margin :=
    div_nonneg (by norm_num) (actualMatchedRepresentation_matrixBounds hM).1.le
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro F
  have hIF : ‖P (M.innerInverse (M.sourceInner (Q F)))‖ ≤ I * ‖F‖ := by
    have hb := (P ∘L M.innerInverse ∘L Si ∘L Q).le_of_opNorm_le hI F
    simpa only [ContinuousLinearMap.comp_apply, hSi] using hb
  have hOF : ‖P (M.outerInverse (M.sourceOuter (Q F)))‖ ≤ O * ‖F‖ := by
    have hb := (P ∘L M.outerInverse ∘L So ∘L Q).le_of_opNorm_le hO F
    simpa only [ContinuousLinearMap.comp_apply, hSo] using hb
  have hhF : 0 ≤ 2 * h * ‖F‖ := by positivity
  have hoF : 0 ≤ 2 * o * ‖F‖ := by positivity
  have hrowF : ∀ i,
      |modePairing D (M.innerPoisson i) (M.sourceInner (Q F))| ≤
        2 * h * ‖F‖ := by
    intro i
    rw [hrow]
    exact (matchedCell_modePairing_bound D (Q (M.innerPoisson i)) F).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hH i) (by norm_num)) (norm_nonneg F))
  have horowF : ∀ i,
      |modePairing D (M.outerPoisson i) (M.sourceOuter (Q F))| ≤
        2 * o * ‖F‖ := by
    intro i
    rw [horow]
    exact (matchedCell_modePairing_bound D (Q (M.outerPoisson i)) F).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hW i) (by norm_num)) (norm_nonneg F))
  have hb := matchedCell_formula_bound hM P (Q F) hp hv hhF hoF
    hIF hOF hP hV hrowF horowF
  change ‖P (G (Q F))‖ ≤ _
  calc
    ‖P (G (Q F))‖ ≤ I * ‖F‖ + O * ‖F‖ +
        (8 * (4 / M.margin) * (p * (2 * h * ‖F‖)) +
          4 * (4 / M.margin) * (p * (2 * o * ‖F‖)) +
          (48 * (4 / M.margin) + 4) * (v * (2 * h * ‖F‖)) +
          24 * (4 / M.margin) * (v * (2 * o * ‖F‖))) := hb
    _ = (I + O +
        (16 * (4 / M.margin) * (p * h) + 8 * (4 / M.margin) * (p * o) +
          (96 * (4 / M.margin) + 8) * (v * h) +
          48 * (4 / M.margin) * (v * o))) * ‖F‖ := by ring

end ContinuousFlexibility.Radial
