module

public import ContinuousFlexibility.Scalar.WeightedMonomialL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Actual finite Leibniz expansions for mixed cylinder jets

The finite term data are constructed before the input functions.  Repeated
terms retain coefficient one: each differentiation records the factor hit.
Every term has exactly the prescribed total radial and angular orders.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped BigOperators ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

/-- Universal finite Leibniz data, including the identity for actual smooth
functions.  The index set records repeated terms rather than numerical
multinomial coefficients. -/
structure MixedProductLeibniz (n a b : ℕ) where
  Index : Type
  [fintype : Fintype Index]
  radial : Index → Fin n → ℕ
  angular : Index → Fin n → ℕ
  radial_order : ∀ t, (∑ i, radial t i) = a
  angular_order : ∀ t, (∑ i, angular t i) = b
  formula : ∀ f : Fin n → PolarPoint → ℝ, (∀ i, ContDiff ℝ ∞ (f i)) → ∀ p,
    mixedDerivative a b (fun q => ∏ i, f i q) p =
      ∑ t, ∏ i, mixedDerivative (radial t i) (angular t i) (f i) p

attribute [instance] MixedProductLeibniz.fintype

theorem mixedProduct_fderiv_prod
    {n : ℕ} (f : Fin n → PolarPoint → ℝ) {p v : PolarPoint}
    (hf : ∀ i, DifferentiableAt ℝ (f i) p) :
    fderiv ℝ (fun q => ∏ i, f i q) p v =
      ∑ i, fderiv ℝ (f i) p v * ∏ j ∈ Finset.univ.erase i, f j p := by
  rw [fderiv_finsetProd (fun i _ => hf i)]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem mixedProduct_axis_jet
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (a b : ℕ) (radial : Bool)
    (p : PolarPoint) :
    fderiv ℝ (mixedDerivative a b f) p (if radial then (1, 0) else (0, 1)) =
      mixedDerivative (a + if radial then 1 else 0) (b + if radial then 0 else 1) f p := by
  cases radial with
  | false => simpa [angularPartial] using congrFun (angularPartial_mixedDerivative hf a b) p
  | true => simpa [radialPartial] using congrFun (radialPartial_mixedDerivative hf a b) p

private def mixedProductLeibniz_zero (n : ℕ) : MixedProductLeibniz n 0 0 where
  Index := Unit
  fintype := inferInstance
  radial := fun _ _ => 0
  angular := fun _ _ => 0
  radial_order := by intro t; simp
  angular_order := by intro t; simp
  formula := by
    intro f _ p
    simp only [mixedDerivative, iteratedDeriv_zero, Fintype.sum_unique]

/-- One coordinate differentiation distributes over every actual factor.
The same construction covers the radial and angular directions. -/
def MixedProductLeibniz.step {n a b : ℕ} (e : MixedProductLeibniz n a b)
    (radial : Bool) :
    MixedProductLeibniz n (a + if radial then 1 else 0) (b + if radial then 0 else 1) where
  Index := e.Index × Fin n
  fintype := inferInstance
  radial := fun t j => e.radial t.1 j + if j = t.2 then (if radial then 1 else 0) else 0
  angular := fun t j => e.angular t.1 j + if j = t.2 then (if radial then 0 else 1) else 0
  radial_order := by
    intro t
    simp [Finset.sum_add_distrib, e.radial_order]
  angular_order := by
    intro t
    simp [Finset.sum_add_distrib, e.angular_order]
  formula := by
    classical
    intro f hf p
    let g : e.Index → Fin n → PolarPoint → ℝ := fun t i =>
      mixedDerivative (e.radial t i) (e.angular t i) (f i)
    have hgs (t : e.Index) (i : Fin n) : ContDiff ℝ ∞ (g t i) :=
      contDiff_mixedDerivative (hf i) (e.radial t i) (e.angular t i)
    have hterm (t : e.Index) : ContDiff ℝ ∞ (fun q => ∏ i, g t i q) :=
      contDiff_prod (fun i _ => hgs t i)
    have hprod : ContDiff ℝ ∞ (fun q => ∏ i, f i q) := contDiff_prod (fun i _ => hf i)
    have heq : mixedDerivative a b (fun q => ∏ i, f i q) =
        fun q => ∑ t : e.Index, ∏ i, g t i q := funext (e.formula f hf)
    calc
      mixedDerivative (a + if radial then 1 else 0) (b + if radial then 0 else 1)
          (fun q => ∏ i, f i q) p =
          fderiv ℝ (mixedDerivative a b (fun q => ∏ i, f i q)) p
            (if radial then (1, 0) else (0, 1)) :=
        (mixedProduct_axis_jet hprod a b radial p).symm
      _ = fderiv ℝ (fun q => ∑ t : e.Index, ∏ i, g t i q) p
          (if radial then (1, 0) else (0, 1)) := by rw [heq]
      _ = ∑ t : e.Index, fderiv ℝ (fun q => ∏ i, g t i q) p
          (if radial then (1, 0) else (0, 1)) := by
        rw [fderiv_fun_sum (fun t _ => (hterm t).differentiable (by simp) p)]
        simp only [sum_apply]
      _ = ∑ t : e.Index × Fin n, ∏ j,
          mixedDerivative
            (e.radial t.1 j + if j = t.2 then (if radial then 1 else 0) else 0)
            (e.angular t.1 j + if j = t.2 then (if radial then 0 else 1) else 0) (f j) p := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro t _
        rw [mixedProduct_fderiv_prod (g t)
          (fun i => (hgs t i).differentiable (by simp) p)]
        apply Finset.sum_congr rfl
        intro i _
        change fderiv ℝ (mixedDerivative (e.radial t i) (e.angular t i) (f i)) p
            (if radial then (1, 0) else (0, 1)) *
            (∏ j ∈ Finset.univ.erase i, g t j p) = _
        rw [mixedProduct_axis_jet (hf i) (e.radial t i) (e.angular t i) radial p]
        rw [← Finset.mul_prod_erase Finset.univ
          (fun j => mixedDerivative
            (e.radial t j + if j = i then (if radial then 1 else 0) else 0)
            (e.angular t j + if j = i then (if radial then 0 else 1) else 0) (f j) p)
          (Finset.mem_univ i)]
        apply congrArg₂ (fun x y : ℝ => x * y)
        · simp
        · apply Finset.prod_congr rfl
          intro j hj
          have hji : j ≠ i := (Finset.mem_erase.mp hj).1
          simp only [if_neg hji, Nat.add_zero, g]

/-- A finite expansion exists for every arity and every pair of mixed orders,
and is independent of the smooth input functions. -/
def mixedProductLeibniz (n a b : ℕ) : MixedProductLeibniz n a b := by
  induction a with
  | zero =>
      induction b with
      | zero => exact mixedProductLeibniz_zero n
      | succ b ih => exact ih.step false
  | succ a ih => exact ih.step true

/-- The actual mixed derivative of a finite product of material pullbacks has
one-high-factor L² control at one common base and loss for all arities. -/
theorem materialPullback_product_mixedDerivative_oneHigh
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ k s a b c : ℕ, a + b + c ≤ s →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Fin (k + 1) → A.Space,
        MemLp
          (fun p => T.M (T.radius p.1) ^ c *
            mixedDerivative a b
              (fun q => ∏ i, materialPullback T γ (A.decode (u i)) q) p)
          2 materialCylinderMeasure ∧
        (eLpNorm
          (fun p => T.M (T.radius p.1) ^ c *
            mixedDerivative a b
              (fun q => ∏ i, materialPullback T γ (A.decode (u i)) q) p)
          2 materialCylinderMeasure).toReal ≤
          C * ∑ i, A.grading (s + loss) (u i) *
            ∏ j ∈ Finset.univ.erase i, A.grading base (u j) := by
  classical
  obtain ⟨base, loss, hbase, hmono⟩ := materialJetMonomial_oneHigh hT hA hinterp
  refine ⟨base, loss, hbase, ?_⟩
  intro k s a b c horder
  let e := mixedProductLeibniz (k + 1) a b
  have htorder (t : e.Index) :
      (∑ i, (e.radial t i + e.angular t i)) + c ≤ s := by
    rw [Finset.sum_add_distrib, e.radial_order, e.angular_order]
    exact horder
  have hterm (t : e.Index) := hmono k s (e.radial t) (e.angular t) c (htorder t)
  choose C hC hCt using hterm
  refine ⟨∑ t, C t, Finset.sum_nonneg (fun t _ => hC t), ?_⟩
  intro u
  let f : Fin (k + 1) → PolarPoint → ℝ := fun i => materialPullback T γ (A.decode (u i))
  have hf (i : Fin (k + 1)) : ContDiff ℝ ∞ (f i) :=
    contDiff_materialPullback hT (hA.2.2.2.1 (u i)).1
  let g : e.Index → PolarPoint → ℝ := fun t =>
    materialJetMonomial T γ A (fun _ => 1) (e.radial t) (e.angular t) c u
  have hcoeff : ∀ p : PolarPoint, |(1 : ℝ)| ≤ (1 : ℝ) * T.M (T.radius p.1) := by
    intro p
    rw [abs_one, one_mul]
    obtain ⟨_, hpos, _, _, _, _, _, hInv, _⟩ := hT
    exact (hpos (T.radius p.1) (hInv p.1).1).2.2.2
  have ht (t : e.Index) := hCt t (fun _ => 1) 1 zero_le_one
    aestronglyMeasurable_const hcoeff u
  have htmem (t : e.Index) : MemLp (g t) 2 materialCylinderMeasure := (ht t).1
  have htnorm (t : e.Index) : (eLpNorm (g t) 2 materialCylinderMeasure).toReal ≤
      C t * ∑ i, A.grading (s + loss) (u i) *
        ∏ j ∈ Finset.univ.erase i, A.grading base (u j) := by
    simpa only [one_mul] using (ht t).2
  have heq :
      (fun p => T.M (T.radius p.1) ^ c * mixedDerivative a b (fun q => ∏ i, f i q) p) =
        ∑ t : e.Index, g t := by
    funext p
    rw [e.formula f hf p, Finset.mul_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro t _
    simp only [g, materialJetMonomial, one_mul, f]
  rw [heq]
  refine ⟨memLp_finsetSum' Finset.univ (fun t _ => htmem t), ?_⟩
  have hfinite : (∑ t : e.Index, eLpNorm (g t) 2 materialCylinderMeasure) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun t _ => (htmem t).eLpNorm_ne_top)
  have htri := ENNReal.toReal_mono hfinite
    (eLpNorm_sum_le (f := g) (s := Finset.univ) (p := 2) (μ := materialCylinderMeasure)
      (by norm_num))
  rw [ENNReal.toReal_sum (fun t _ => (htmem t).eLpNorm_ne_top)] at htri
  apply htri.trans
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun t _ => htnorm t)

end ContinuousFlexibility.Statements
