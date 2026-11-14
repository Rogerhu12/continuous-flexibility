module

public import ContinuousFlexibility.Analysis.OneHighConvolutionYoung
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Nonempty convolution and its frequency integrand

An iterated fiber integral represents a convolution of any positive number of
frequency factors. Keeping the full integrand visible permits a pointwise
one-high-factor inequality before any frequency variables are integrated out.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal MeasureTheory BigOperators

universe u v

variable {G : Type u} [MeasurableSpace G] [AddCommGroup G]

/-- Integrate a nonempty frequency tuple over the fiber where its sum is `x`. -/
def convolutionKernel (μ : Measure G) : (k : ℕ) →
    ((Fin (k + 1) → G) → ℝ≥0∞) → G → ℝ≥0∞
  | 0, F, x => F (fun _ => x)
  | k + 1, F, x => ∫⁻ y, convolutionKernel μ k
      (fun ζ => F (Fin.cons (α := fun _ => G) y ζ)) (-y + x) ∂μ

/-- The convolution of `k + 1` positive frequency functions. -/
def positiveConvolution (μ : Measure G) (k : ℕ) (f : Fin (k + 1) → G → ℝ≥0∞) : G → ℝ≥0∞ :=
  convolutionKernel μ k (fun ζ => ∏ i, f i (ζ i))

@[simp]
theorem convolutionKernel_zero (μ : Measure G) (F : (Fin 1 → G) → ℝ≥0∞) (x : G) :
    convolutionKernel μ 0 F x = F (fun _ => x) := rfl

theorem convolutionKernel_succ (μ : Measure G) (k : ℕ)
    (F : (Fin (k + 2) → G) → ℝ≥0∞) (x : G) :
    convolutionKernel μ (k + 1) F x =
      ∫⁻ y, convolutionKernel μ k
        (fun ζ => F (Fin.cons (α := fun _ => G) y ζ)) (-y + x) ∂μ := rfl

theorem convolutionKernel_mono (μ : Measure G) (k : ℕ)
    {F H : (Fin (k + 1) → G) → ℝ≥0∞} (h : ∀ ζ, F ζ ≤ H ζ) (x : G) :
    convolutionKernel μ k F x ≤ convolutionKernel μ k H x := by
  induction k generalizing x with
  | zero => exact h _
  | succ k ih =>
    rw [convolutionKernel_succ, convolutionKernel_succ]
    exact lintegral_mono fun y => ih
      (fun ζ => h (Fin.cons (α := fun _ => G) y ζ)) (-y + x)

variable [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [SFinite μ]

private theorem measurable_fin_cons {A : Type*} [MeasurableSpace A] {k : ℕ}
    {a : A → G} {v : A → Fin k → G} (ha : Measurable a) (hv : Measurable v) :
    Measurable (fun z => Fin.cons (α := fun _ => G) (a z) (v z)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using ha
  · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp hv

private theorem measurable_convolutionKernel_param_aux (k : ℕ) :
    ∀ {A : Type (max u v)} [MeasurableSpace A] (F : A → (Fin (k + 1) → G) → ℝ≥0∞),
      Measurable (Function.uncurry F) →
      Measurable (fun p : A × G => convolutionKernel μ k (F p.1) p.2) := by
  induction k with
  | zero =>
    intro A _ F hF
    exact hF.comp (measurable_fst.prodMk (Measurable.of_eval (fun _ => measurable_snd)))
  | succ k ih =>
    intro A _ F hF
    have hF' : Measurable (Function.uncurry
        (fun (p : A × G) (ζ : Fin (k + 1) → G) =>
          F p.1 (Fin.cons (α := fun _ => G) p.2 ζ))) :=
      hF.comp (measurable_fst.fst.prodMk
        (measurable_fin_cons measurable_fst.snd measurable_snd))
    have hinner := ih (fun (p : A × G) (ζ : Fin (k + 1) → G) =>
      F p.1 (Fin.cons (α := fun _ => G) p.2 ζ)) hF'
    have hfull : Measurable (fun p : (A × G) × G =>
        convolutionKernel μ k
          (fun ζ => F p.1.1 (Fin.cons (α := fun _ => G) p.2 ζ)) (-p.2 + p.1.2)) :=
      hinner.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk
        (measurable_snd.neg.add measurable_fst.snd))
    exact hfull.lintegral_prod_right'

/-- Joint measurability includes external parameters of any universe. -/
theorem measurable_convolutionKernel_param (k : ℕ) {A : Type v} [MeasurableSpace A]
    (F : A → (Fin (k + 1) → G) → ℝ≥0∞) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun p : A × G => convolutionKernel μ k (F p.1) p.2) := by
  have hFlift : Measurable (Function.uncurry
      (fun (a : ULift.{u} A) ζ => F a.down ζ)) :=
    hF.comp ((measurable_down.comp measurable_fst).prodMk measurable_snd)
  have h := measurable_convolutionKernel_param_aux (μ := μ) k
    (fun (a : ULift.{u} A) ζ => F a.down ζ) hFlift
  exact h.comp ((measurable_up.comp measurable_fst).prodMk measurable_snd)

theorem measurable_convolutionKernel (k : ℕ) {F : (Fin (k + 1) → G) → ℝ≥0∞}
    (hF : Measurable F) : Measurable (convolutionKernel μ k F) :=
  (measurable_convolutionKernel_param k (fun (_ : G) ζ => F ζ)
    (hF.comp measurable_snd)).comp (measurable_id.prodMk measurable_id)

theorem measurable_convolutionKernel_slice (k : ℕ) {F : (Fin (k + 2) → G) → ℝ≥0∞}
    (hF : Measurable F) (x : G) :
    Measurable (fun y => convolutionKernel μ k
      (fun ζ => F (Fin.cons (α := fun _ => G) y ζ)) (-y + x)) :=
  (measurable_convolutionKernel_param k
    (fun y ζ => F (Fin.cons (α := fun _ => G) y ζ))
    (hF.comp (measurable_fin_cons measurable_fst measurable_snd))).comp
      (measurable_id.prodMk (measurable_id.neg.add_const x))

theorem convolutionKernel_const_mul (k : ℕ) {F : (Fin (k + 1) → G) → ℝ≥0∞}
    (hF : Measurable F) (c : ℝ≥0∞) (x : G) :
    convolutionKernel μ k (fun ζ => c * F ζ) x = c * convolutionKernel μ k F x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [convolutionKernel_succ, convolutionKernel_succ]
    have hslice (y : G) :
        convolutionKernel μ k
          (fun ζ => c * F (Fin.cons (α := fun _ => G) y ζ)) (-y + x) =
          c * convolutionKernel μ k
            (fun ζ => F (Fin.cons (α := fun _ => G) y ζ)) (-y + x) :=
      ih (hF.comp (measurable_fin_cons measurable_const measurable_id)) (-y + x)
    simp_rw [hslice]
    exact lintegral_const_mul c (measurable_convolutionKernel_slice k hF x)

theorem convolutionKernel_finset_sum (k : ℕ) {ι : Type*} (S : Finset ι)
    (F : ι → (Fin (k + 1) → G) → ℝ≥0∞) (hF : ∀ i ∈ S, Measurable (F i)) (x : G) :
    convolutionKernel μ k (fun ζ => ∑ i ∈ S, F i ζ) x =
      ∑ i ∈ S, convolutionKernel μ k (F i) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [convolutionKernel_succ]
    have hslice (y : G) :
        convolutionKernel μ k
          (fun ζ => ∑ i ∈ S, F i (Fin.cons (α := fun _ => G) y ζ)) (-y + x) =
          ∑ i ∈ S, convolutionKernel μ k
            (fun ζ => F i (Fin.cons (α := fun _ => G) y ζ)) (-y + x) :=
      ih (fun i ζ => F i (Fin.cons (α := fun _ => G) y ζ))
        (fun i hi => (hF i hi).comp (measurable_fin_cons measurable_const measurable_id))
        (-y + x)
    simp_rw [hslice]
    rw [lintegral_finsetSum S (fun i hi => measurable_convolutionKernel_slice k (hF i hi) x)]
    rfl

theorem measurable_positiveConvolution (k : ℕ) {f : Fin (k + 1) → G → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) : Measurable (positiveConvolution μ k f) :=
  measurable_convolutionKernel k
    (Finset.univ.measurable_fun_prod (fun i _ => (hf i).comp (measurable_pi_apply i)))

@[simp]
theorem positiveConvolution_zero (μ : Measure G) (f : Fin 1 → G → ℝ≥0∞) :
    positiveConvolution μ 0 f = f 0 := by
  ext x
  change (∏ i : Fin 1, f i x) = f 0 x
  exact Fin.prod_univ_one _

/-- The full-tuple representation is the usual iterated convolution. -/
theorem positiveConvolution_succ (k : ℕ) {f : Fin (k + 2) → G → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) :
    positiveConvolution μ (k + 1) f =
      f 0 ⋆ₗ[μ] positiveConvolution μ k (fun i => f i.succ) := by
  ext x
  rw [positiveConvolution, convolutionKernel_succ, lconvolution_def]
  apply lintegral_congr
  intro y
  have heq : (fun ζ : Fin (k + 1) → G =>
      ∏ i : Fin (k + 2), f i (Fin.cons (α := fun _ => G) y ζ i)) =
      (fun ζ => f 0 y * ∏ i : Fin (k + 1), f i.succ (ζ i)) := by
    funext ζ
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  rw [heq, convolutionKernel_const_mul k
    (Finset.univ.measurable_fun_prod (fun i _ => (hf i.succ).comp (measurable_pi_apply i)))]
  rfl

end ContinuousFlexibility.Analysis
