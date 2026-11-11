import ContinuousFlexibility.Analysis.ProjectiveJets

/-!
# Variable multilinear curve product rules in the actual topology

An exact finite telescoping identity changes the inputs one at a time.
After division by the step size, multilinearity moves each input quotient
into its own slot. Joint evaluation continuity then handles the varying
multilinear coefficient and the other varying inputs simultaneously.

All source slots are topological real modules, and the target may be a
projective Fréchet space. No norm is imposed on these spaces. The result
is a product rule for actual quotient derivatives, not a general
higher-order Faà di Bruno theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

section Shift

variable {W : Type*} [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]

/-- An actual quotient derivative gives continuity along the punctured
parameter shift in every topological real module. -/
theorem HasProjectiveCurveDerivAt.tendsto_shift {c : ℝ → W} {dc : W} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) :
    Tendsto (fun h : ℝ => c (t + h)) (𝓝[≠] (0 : ℝ)) (𝓝 (c t)) := by
  have hzero : Tendsto (fun h : ℝ => h) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun h : ℝ => c t + h • (h⁻¹ • (c (t + h) - c t)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (c t)) := by
    simpa only [zero_smul, add_zero, id_eq] using
      (tendsto_const_nhds (x := c t)).add (hzero.smul hc)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := by simpa using hh
  change c t + h • (h⁻¹ • (c (t + h) - c t)) = c (t + h)
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  abel

end Shift

section Replacements

variable {n : ℕ} {V : Fin n → Type*}

/-- The first `j` inputs have been changed from `x` to `y`. -/
def multilinearReplaceBefore (x y : ∀ i, V i) (j : ℕ) : ∀ i, V i :=
  fun i => if i.1 < j then y i else x i

private theorem multilinearReplaceBefore_zero (x y : ∀ i, V i) :
    multilinearReplaceBefore x y 0 = x := by
  funext i
  simp [multilinearReplaceBefore]

private theorem multilinearReplaceBefore_top (x y : ∀ i, V i) :
    multilinearReplaceBefore x y n = y := by
  funext i
  simp [multilinearReplaceBefore, i.isLt]

private theorem multilinearReplaceBefore_step (x y : ∀ i, V i) (i : Fin n) :
    multilinearReplaceBefore x y (i.1 + 1) =
      Function.update (multilinearReplaceBefore x y i.1) i (y i) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [multilinearReplaceBefore]
  · have hval : j.1 ≠ i.1 := fun h => hji (Fin.val_injective h)
    have hlt : j.1 < i.1 + 1 ↔ j.1 < i.1 := by
      simpa only [Nat.lt_succ_iff] using hval.le_iff_lt
    simp only [multilinearReplaceBefore, Function.update_of_ne hji, hlt]

private theorem multilinearReplaceBefore_base (x y : ∀ i, V i) (i : Fin n) :
    Function.update (multilinearReplaceBefore x y i.1) i (x i) =
      multilinearReplaceBefore x y i.1 := by
  have hi : multilinearReplaceBefore x y i.1 i = x i := by simp [multilinearReplaceBefore]
  rw [← hi, Function.update_eq_self]

end Replacements

section Telescoping

variable {n : ℕ} {V : Fin n → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  [∀ i, TopologicalSpace (V i)]
variable {W : Type*} [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]

omit [TopologicalSpace W] [Module ℝ W] in
private theorem finite_telescope (f : ℕ → W) (k : ℕ) :
    (∑ i : Fin k, (f (i.1 + 1) - f i.1)) = f k - f 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    abel

/-- Exact finite telescoping for a genuine multilinear map, including
arity zero. -/
theorem multilinear_sub_eq_sum_updates
    (B : ContinuousMultilinearMap ℝ V W) (x y : ∀ i, V i) :
    B y - B x = ∑ i : Fin n,
      B (Function.update (multilinearReplaceBefore x y i.1) i (y i - x i)) := by
  calc
    B y - B x = B (multilinearReplaceBefore x y n) - B (multilinearReplaceBefore x y 0) := by
      rw [multilinearReplaceBefore_top, multilinearReplaceBefore_zero]
    _ = ∑ i : Fin n, (B (multilinearReplaceBefore x y (i.1 + 1)) -
        B (multilinearReplaceBefore x y i.1)) :=
      (finite_telescope (fun j => B (multilinearReplaceBefore x y j)) n).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [B.map_update_sub, multilinearReplaceBefore_step, multilinearReplaceBefore_base]

/-- Normalization moves the scalar into exactly one input slot. -/
theorem multilinear_smul_sub_eq_sum_updates
    (B : ContinuousMultilinearMap ℝ V W) (x y : ∀ i, V i) (a : ℝ) :
    a • (B y - B x) = ∑ i : Fin n,
      B (Function.update (multilinearReplaceBefore x y i.1) i (a • (y i - x i))) := by
  rw [multilinear_sub_eq_sum_updates, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (B.map_update_smul _ i a _).symm

theorem variable_multilinear_quotient_identity
    (B₀ B₁ : ContinuousMultilinearMap ℝ V W) (x y : ∀ i, V i) (a : ℝ) :
    a • (B₁ y - B₀ x) = a • (B₁ x - B₀ x) + ∑ i : Fin n,
      B₁ (Function.update (multilinearReplaceBefore x y i.1) i (a • (y i - x i))) := by
  have heq : B₁ y - B₀ x = (B₁ x - B₀ x) + (B₁ y - B₁ x) := by abel
  rw [heq, smul_add, multilinear_smul_sub_eq_sum_updates]

end Telescoping

section VariableCurve

variable {n : ℕ} {V : Fin n → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
  [∀ i, ContinuousSMul ℝ (V i)]
variable {W : Type*} [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]
  [IsTopologicalAddGroup W]

/-- Actual product rule with varying multilinear coefficient and varying
inputs. Only the coefficient curve at the fixed original input needs a
derivative; joint evaluation continuity handles the varying slot vectors. -/
theorem hasProjectiveCurveDerivAt_variableMultilinear
    (B : ℝ → ContinuousMultilinearMap ℝ V W) (c : ℝ → ∀ i, V i)
    (dc : ∀ i, V i) (b₀ : W) (t₀ : ℝ)
    (hB : ∀ w : ∀ i, V i, ContinuousAt (fun p : ℝ × (∀ i, V i) => B p.1 p.2) (t₀, w))
    (hc : ∀ i, HasProjectiveCurveDerivAt (fun t => c t i) (dc i) t₀)
    (hB₀ : HasProjectiveCurveDerivAt (fun t => B t (c t₀)) b₀ t₀) :
    HasProjectiveCurveDerivAt (fun t => B t (c t))
      (b₀ + ∑ i : Fin n, B t₀ (Function.update (c t₀) i (dc i))) t₀ := by
  have hshift : Tendsto (fun h : ℝ => t₀ + h) (𝓝[≠] (0 : ℝ)) (𝓝 t₀) := by
    simpa only [add_zero, id_eq] using (tendsto_const_nhds (x := t₀)).add
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun h : ℝ => h) (𝓝[≠] (0 : ℝ)) (𝓝 0))
  have hterm : ∀ i : Fin n, Tendsto
      (fun h : ℝ => B (t₀ + h) (Function.update
        (multilinearReplaceBefore (c t₀) (c (t₀ + h)) i.1) i
          (h⁻¹ • (c (t₀ + h) i - c t₀ i))))
      (𝓝[≠] (0 : ℝ)) (𝓝 (B t₀ (Function.update (c t₀) i (dc i)))) := by
    intro i
    have hv : Tendsto
        (fun h : ℝ => Function.update (multilinearReplaceBefore (c t₀) (c (t₀ + h)) i.1) i
          (h⁻¹ • (c (t₀ + h) i - c t₀ i)))
        (𝓝[≠] (0 : ℝ)) (𝓝 (Function.update (c t₀) i (dc i))) := by
      apply tendsto_pi_nhds.mpr
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [HasProjectiveCurveDerivAt, Function.update_self] using hc i
      · simp only [Function.update_of_ne hji]
        by_cases hlt : j.1 < i.1
        · simpa only [multilinearReplaceBefore, ite_eq_left hlt] using (hc j).tendsto_shift
        · simpa only [multilinearReplaceBefore, ite_eq_right hlt] using
            (tendsto_const_nhds (x := c t₀ j) :
              Tendsto (fun _ : ℝ => c t₀ j) (𝓝[≠] (0 : ℝ)) (𝓝 (c t₀ j)))
    simpa only [Function.comp_def] using
      (hB (Function.update (c t₀) i (dc i))).tendsto.comp (hshift.prodMk_nhds hv)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hterm i)
  unfold HasProjectiveCurveDerivAt at hB₀ ⊢
  apply (hB₀.add hsum).congr'
  exact Eventually.of_forall (fun h =>
    (variable_multilinear_quotient_identity (B t₀) (B (t₀ + h)) (c t₀) (c (t₀ + h)) h⁻¹).symm)

/-- The fixed multilinear coefficient version is a consequence of the
same actual quotient product rule. -/
theorem hasProjectiveCurveDerivAt_multilinear
    (B : ContinuousMultilinearMap ℝ V W) (c : ℝ → ∀ i, V i)
    (dc : ∀ i, V i) (t₀ : ℝ)
    (hc : ∀ i, HasProjectiveCurveDerivAt (fun t => c t i) (dc i) t₀) :
    HasProjectiveCurveDerivAt (fun t => B (c t))
      (∑ i : Fin n, B (Function.update (c t₀) i (dc i))) t₀ := by
  have hB : ∀ w : ∀ i, V i,
      ContinuousAt (fun p : ℝ × (∀ i, V i) => (fun _ : ℝ => B) p.1 p.2) (t₀, w) := by
    intro w
    have heval : Continuous (fun p : ℝ × (∀ i, V i) => B p.2) := by
      convert B.cont.comp continuous_snd using 1
      funext p
      rfl
    exact heval.continuousAt
  have h := hasProjectiveCurveDerivAt_variableMultilinear (fun _ => B) c dc 0 t₀ hB hc
    (hasProjectiveCurveDerivAt_const (B (c t₀)) t₀)
  simpa only [zero_add] using h

end VariableCurve

section BoundaryArities

variable {W : Type*} [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]

/-- Arity zero has no input contribution, even for a varying coefficient. -/
theorem hasProjectiveCurveDerivAt_multilinear_zero
    {V : Fin 0 → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, TopologicalSpace (V i)]
    (B : ℝ → ContinuousMultilinearMap ℝ V W) (c : ℝ → ∀ i, V i) (b₀ : W) (t₀ : ℝ)
    (hB₀ : HasProjectiveCurveDerivAt (fun t => B t (c t₀)) b₀ t₀) :
    HasProjectiveCurveDerivAt (fun t => B t (c t)) b₀ t₀ := by
  have heq : (fun t => B t (c t)) = (fun t => B t (c t₀)) := by
    funext t
    exact congrArg (B t) (Subsingleton.elim _ _)
  rw [heq]
  exact hB₀

variable [IsTopologicalAddGroup W]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Arity one is the exact variable-linear-map product rule. -/
theorem hasProjectiveCurveDerivAt_multilinear_one
    (B : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) W)
    (c : ℝ → E) (dc : E) (b₀ : W) (t₀ : ℝ)
    (hB : ∀ w : Fin 1 → E, ContinuousAt (fun p : ℝ × (Fin 1 → E) => B p.1 p.2) (t₀, w))
    (hc : HasProjectiveCurveDerivAt c dc t₀)
    (hB₀ : HasProjectiveCurveDerivAt (fun t => B t (fun _ => c t₀)) b₀ t₀) :
    HasProjectiveCurveDerivAt (fun t => B t (fun _ => c t))
      (b₀ + B t₀ (fun _ => dc)) t₀ := by
  have h := hasProjectiveCurveDerivAt_variableMultilinear B (fun t _ => c t) (fun _ => dc)
    b₀ t₀ hB (fun _ => hc) hB₀
  have hs : (∑ i : Fin 1, B t₀ (Function.update (fun _ => c t₀) i dc)) = B t₀ (fun _ => dc) := by
    rw [Fin.sum_univ_one]
    congr 1
    funext i
    fin_cases i
    simp
  rw [hs] at h
  exact h

end BoundaryArities

end ContinuousFlexibility.Analysis
