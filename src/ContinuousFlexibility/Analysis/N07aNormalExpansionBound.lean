module

public import ContinuousFlexibility.Analysis.N07aOpenClassicalNormal
public import ContinuousFlexibility.Analysis.SpacesInterpolationProducts
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-!
# L² control of the exact finite normal expansion

Every coefficient derivative is charged in its actual finite product, and
only the terminal solution/source jet is measured in L². This estimate
never invokes an unknown full mixed Sobolev norm on its right hand side.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal
open ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

def n07aNormalTermAmplitude (C : N07aNormalAtom → ℝ) (t : N07aNormalTerm) : ℝ :=
  |t.scalar| * (t.atoms.map C).prod

theorem n07aNormalTermAmplitude_nonneg (C : N07aNormalAtom → ℝ)
    (hC : ∀ j, 0 ≤ C j) (t : N07aNormalTerm) : 0 ≤ n07aNormalTermAmplitude C t := by
  apply mul_nonneg (abs_nonneg _)
  apply List.prod_nonneg
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact hC j

private theorem n07aNormalAtoms_abs_bound (A : Fin 6 → PolarPoint → ℝ)
    (C : N07aNormalAtom → ℝ) (J : List N07aNormalAtom) (p : PolarPoint)
    (hC : ∀ j ∈ J, |j.value A p| ≤ C j) :
    |(J.map (fun j => j.value A p)).prod| ≤ (J.map C).prod := by
  induction J with
  | nil => simp
  | cons j J ih =>
    simp only [List.map_cons, List.prod_cons, abs_mul]
    exact mul_le_mul (hC j (List.mem_cons_self))
      (ih (fun k hk => hC k (List.mem_cons_of_mem j hk))) (abs_nonneg _)
      ((abs_nonneg _).trans (hC j (List.mem_cons_self)))

private theorem n07aNormalAtoms_smooth {U : Set PolarPoint} (hU : IsOpen U)
    {A : Fin 6 → PolarPoint → ℝ} (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (J : List N07aNormalAtom) :
    ContDiffOn ℝ ∞ (fun p => (J.map (fun j => j.value A p)).prod) U := by
  induction J with
  | nil => simpa only [List.map_nil, List.prod_nil] using contDiffOn_const
  | cons j J ih =>
    simpa only [List.map_cons, List.prod_cons, N07aNormalAtom.value] using
      (contDiffOn_mixedDerivative hU (hA j.coefficient) j.radial j.angular).mul ih

theorem n07aNormalTerm_value_smooth {U : Set PolarPoint} (hU : IsOpen U)
    {A : Fin 6 → PolarPoint → ℝ} {u f : PolarPoint → ℝ}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hu : ContDiffOn ℝ ∞ u U) (hf : ContDiffOn ℝ ∞ f U) (t : N07aNormalTerm) :
    ContDiffOn ℝ ∞ (t.value A u f) U := by
  have hleaf : ContDiffOn ℝ ∞ (if t.source then f else u) U := by
    split <;> assumption
  exact (contDiffOn_const.mul (n07aNormalAtoms_smooth hU hA t.atoms)).mul
    (contDiffOn_mixedDerivative hU hleaf t.radial t.angular)

theorem n07aNormalTerm_eLpNorm_bound
    {A : Fin 6 → PolarPoint → ℝ} {u f : PolarPoint → ℝ}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) (canonicalOpen S K m))
    (hu : ContDiffOn ℝ ∞ u (canonicalOpen S K m))
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (C : N07aNormalAtom → ℝ) (t : N07aNormalTerm)
    (hC : ∀ j ∈ t.atoms, ∀ p ∈ canonicalOpen S K m, |j.value A p| ≤ C j) :
    eLpNorm (t.value A u f) 2 (canonicalMeasure S K m) ≤
      ENNReal.ofReal (n07aNormalTermAmplitude C t) *
        eLpNorm (mixedDerivative t.radial t.angular (if t.source then f else u))
          2 (canonicalMeasure S K m) := by
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (n07a_canonicalOpen_aestronglyMeasurable
      (n07aNormalTerm_value_smooth (isOpen_Ioo.prod isOpen_univ) hA hu hf t).continuousOn)
  filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
  simp only [Real.norm_eq_abs, N07aNormalTerm.value, abs_mul, n07aNormalTermAmplitude]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (n07aNormalAtoms_abs_bound A C t.atoms p (fun j hj => hC j hj p hp))
      (abs_nonneg _)) (abs_nonneg _)

private theorem n07aNormalTerms_eLpNorm_bound
    (A : Fin 6 → PolarPoint → ℝ) (u f : PolarPoint → ℝ)
    (L : List N07aNormalTerm) (B : N07aNormalTerm → ℝ)
    (hB : ∀ t ∈ L, 0 ≤ B t)
    (hterm : ∀ t ∈ L, eLpNorm (t.value A u f) 2 (canonicalMeasure S K m) ≤
      ENNReal.ofReal (B t)) :
    eLpNorm (n07aNormalTermsValue A u f L) 2 (canonicalMeasure S K m) ≤
      ENNReal.ofReal ((L.map B).sum) := by
  induction L with
  | nil =>
    change eLpNorm (0 : PolarPoint → ℝ) 2 (canonicalMeasure S K m) ≤ ENNReal.ofReal 0
    simp
  | cons t L ih =>
    have he : n07aNormalTermsValue A u f (t :: L) =
        t.value A u f + n07aNormalTermsValue A u f L := by
      funext p
      simp only [n07aNormalTermsValue, List.map_cons, List.sum_cons, Pi.add_apply]
    rw [he, List.map_cons, List.sum_cons]
    calc
      _ ≤ eLpNorm (t.value A u f) 2 (canonicalMeasure S K m) +
          eLpNorm (n07aNormalTermsValue A u f L) 2 (canonicalMeasure S K m) :=
        eLpNorm_add_le (by norm_num)
      _ ≤ ENNReal.ofReal (B t) + ENNReal.ofReal ((L.map B).sum) :=
        add_le_add (hterm t List.mem_cons_self)
          (ih (fun v hv => hB v (List.mem_cons_of_mem t hv))
            (fun v hv => hterm v (List.mem_cons_of_mem t hv)))
      _ = _ := (ENNReal.ofReal_add (hB t List.mem_cons_self)
        (List.sum_nonneg fun x hx => by
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
          exact hB v (List.mem_cons_of_mem t hv))).symm

/-- The exact expansion gives a quantitative bound involving only actual
coefficient jets and its terminal jets. The proved safety property of the
expansion says that solution terminals have at most one normal derivative. -/
theorem n07a_normalExpansion_eLpNorm_bound
    {A : Fin 6 → PolarPoint → ℝ} {u f : PolarPoint → ℝ}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) (canonicalOpen S K m))
    (hu : ContDiffOn ℝ ∞ u (canonicalOpen S K m))
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (heq : EqOn (mixedDerivative 2 0 u) (n07aNormalRhs A u f) (canonicalOpen S K m))
    (C : N07aNormalAtom → ℝ) (hC0 : ∀ j, 0 ≤ C j)
    (hC : ∀ j p, p ∈ canonicalOpen S K m → |j.value A p| ≤ C j)
    (T : Bool → ℕ → ℕ → ℝ) (hT0 : ∀ source a b, 0 ≤ T source a b)
    (a b : ℕ)
    (hT : ∀ t ∈ n07aNormalExpansion a b,
      eLpNorm (mixedDerivative t.radial t.angular (if t.source then f else u))
        2 (canonicalMeasure S K m) ≤ ENNReal.ofReal (T t.source t.radial t.angular)) :
    eLpNorm (mixedDerivative a b u) 2 (canonicalMeasure S K m) ≤
      ENNReal.ofReal (((n07aNormalExpansion a b).map fun t =>
        n07aNormalTermAmplitude C t * T t.source t.radial t.angular).sum) := by
  have he : mixedDerivative a b u =ᵐ[canonicalMeasure S K m]
      n07aNormalTermsValue A u f (n07aNormalExpansion a b) := by
    filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
    exact n07a_normalExpansion_exact (isOpen_Ioo.prod isOpen_univ) hA hu hf heq a b hp
  rw [eLpNorm_congr_ae he]
  apply n07aNormalTerms_eLpNorm_bound A u f
  · intro t _
    exact mul_nonneg (n07aNormalTermAmplitude_nonneg C hC0 t) (hT0 _ _ _)
  · intro t ht
    calc
      _ ≤ ENNReal.ofReal (n07aNormalTermAmplitude C t) *
          eLpNorm (mixedDerivative t.radial t.angular (if t.source then f else u))
            2 (canonicalMeasure S K m) :=
        n07aNormalTerm_eLpNorm_bound hA hu hf C t (fun j _ p hp => hC j p hp)
      _ ≤ ENNReal.ofReal (n07aNormalTermAmplitude C t) *
          ENNReal.ofReal (T t.source t.radial t.angular) :=
        mul_le_mul le_rfl (hT t ht) zero_le zero_le
      _ = _ := (ENNReal.ofReal_mul (n07aNormalTermAmplitude_nonneg C hC0 t)).symm

end ContinuousFlexibility.Analysis
