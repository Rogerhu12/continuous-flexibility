module

public import ContinuousFlexibility.Analysis.CoupledCircleCompositionMultilinear
public import ContinuousFlexibility.Analysis.TameJetLocalBounds

/-!
# Local affine growth of circle composition kernels

A bounded low-seminorm box controls all low factors. Each kernel then
has affine growth in one high seminorm, with the original fixed loss.
The final homogeneous jet estimates follow from multilinear normalization.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators

private theorem coupled_bounded_factor_size {n : ℕ} (a b : Fin n → ℝ)
    {A R Q : ℝ} (hR : 1 ≤ R) (hQ : 0 ≤ Q)
    (ha : ∀ i, 0 ≤ a i) (haR : ∀ i, a i ≤ R)
    (hb : ∀ i, 0 ≤ b i) (hbQ : ∀ i, b i ≤ Q)
    (hA : 0 ≤ A) (hAQ : A ≤ 1 + Q) :
    A * ∏ i, a i + ∑ i, b i * ∏ j ∈ Finset.univ.erase i, a j ≤
      ((n : ℝ) + 1) * R ^ n * (1 + Q) := by
  have hprod (I : Finset (Fin n)) : (∏ i ∈ I, a i) ≤ R ^ n := by
    calc
      _ ≤ ∏ _i ∈ I, R := Finset.prod_le_prod₀ (fun i _ => ha i) (fun i _ => haR i)
      _ = R ^ I.card := by rw [Finset.prod_const]
      _ ≤ R ^ n := pow_le_pow_right₀ hR (by simpa using Finset.card_le_univ I)
  have hmain : A * (∏ i, a i) ≤ (1 + Q) * R ^ n :=
    mul_le_mul hAQ (hprod Finset.univ)
      (Finset.prod_nonneg (fun i _ => ha i)) (add_nonneg zero_le_one hQ)
  have hsum : (∑ i, b i * ∏ j ∈ Finset.univ.erase i, a j) ≤
      (n : ℝ) * (Q * R ^ n) := by
    calc
      _ ≤ ∑ _i : Fin n, Q * R ^ n := Finset.sum_le_sum (fun i _ =>
        mul_le_mul (hbQ i) (hprod (Finset.univ.erase i))
          (Finset.prod_nonneg (fun j _ => ha j)) hQ)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hscalar : (1 + Q) + (n : ℝ) * Q ≤ ((n : ℝ) + 1) * (1 + Q) := by
    nlinarith only [Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ (1 + Q) * R ^ n + (n : ℝ) * (Q * R ^ n) := add_le_add hmain hsum
    _ = ((1 + Q) + (n : ℝ) * Q) * R ^ n := by ring
    _ ≤ (((n : ℝ) + 1) * (1 + Q)) * R ^ n :=
      mul_le_mul_of_nonneg_right hscalar (pow_nonneg (zero_le_one.trans hR) n)
    _ = _ := by ring

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

theorem coupled_circle_kernel_locallyTame
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : ∀ s, Continuous (p s)) (r k : ℕ)
    (ψ v : E → M.Space) (w : E → Fin k → M.Space)
    (hψ : Continuous ψ) (hv : Continuous v) (hw : ∀ i, Continuous (fun x => w x i))
    (hψp : ∀ s x, M.grading s (ψ x) ≤ p s x)
    (hvp : ∀ s x, M.grading s (v x) ≤ p s x)
    (hwp : ∀ s x i, M.grading s (w x i) ≤ p s x) :
    LocallyTameOn p M.grading univ
      (fun x => coupledCircleKernel hD hT hγ hM hI r k (ψ x) (v x) (w x)) := by
  classical
  have hc : Continuous
      (fun x => coupledCircleKernel hD hT hγ hM hI r k (ψ x) (v x) (w x)) := by
    have hm : Continuous (fun x =>
        (ψ x, (Fin.cons (v x) (w x) : Fin (k + 1) → M.Space))) :=
      hψ.prodMk (continuous_pi (fun i => Fin.cases hv hw i))
    simpa only [Function.comp_def, coupledCircleKernelMultilinear_apply,
      Fin.cons_zero, Fin.tail_cons] using
      (coupledCircleKernelMultilinear_continuous hD hT hγ hM hI r k).comp hm
  refine ⟨hc.continuousOn, fun x₀ _ => ?_⟩
  have hexists := coupled_circle_kernel_grading_bounds hD hT hγ hM hI
  let base : ℕ := hexists.choose
  let loss : ℕ := hexists.choose_spec.choose
  have hbound : ∀ (r k s : ℕ) (R : ℝ), 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ ψ : M.Space, M.grading base ψ ≤ R → ∀ v : M.Space, ∀ w : Fin k → M.Space,
        M.grading s (coupledCircleKernel hD hT hγ hM hI r k ψ v w) ≤
          C * coupledCircleKernelMajorant M base (r + s + loss) ψ (Fin.cons v w) :=
    hexists.choose_spec.choose_spec
  let R : ℝ := 1 + p base x₀
  have hR : 1 ≤ R := le_add_of_nonneg_right (apply_nonneg _ _)
  let W : Set E := {x | p base x < R}
  have hW : W ∈ 𝓝[univ] x₀ := nhdsWithin_le_nhds
    ((hp base).continuousAt.preimage_mem_nhds
      (Iio_mem_nhds (lt_add_of_pos_left (p base x₀) zero_lt_one)))
  refine ⟨r + loss, base, W, hW, fun s _ => ?_⟩
  have hCexists := hbound r k s R hR
  let C : ℝ := hCexists.choose
  have hC : 0 ≤ C := hCexists.choose_spec.1
  have hCb : ∀ ψ : M.Space, M.grading base ψ ≤ R →
      ∀ v : M.Space, ∀ w : Fin k → M.Space,
        M.grading s (coupledCircleKernel hD hT hγ hM hI r k ψ v w) ≤
          C * coupledCircleKernelMajorant M base (r + s + loss) ψ (Fin.cons v w) :=
    hCexists.choose_spec.2
  refine ⟨C * (((k + 1 : ℕ) : ℝ) + 1) * R ^ (k + 1),
    mul_nonneg (mul_nonneg hC (by positivity)) (pow_nonneg (zero_le_one.trans hR) _), ?_⟩
  intro x hx
  have hlow : ∀ i : Fin (k + 1),
      M.grading base ((Fin.cons (v x) (w x) : Fin (k + 1) → M.Space) i) ≤ R :=
    fun i => Fin.cases ((hvp base x).trans hx.le)
      (fun j => (hwp base x j).trans hx.le) i
  have hhigh : ∀ i : Fin (k + 1),
      M.grading (r + s + loss) ((Fin.cons (v x) (w x) : Fin (k + 1) → M.Space) i) ≤
      p (r + s + loss) x :=
    fun i => Fin.cases (hvp _ x) (fun j => hwp _ x j) i
  have hb : coupledCircleKernelMajorant M base (r + s + loss) (ψ x)
      (Fin.cons (v x) (w x)) ≤
      (((k + 1 : ℕ) : ℝ) + 1) * R ^ (k + 1) * (1 + p (r + s + loss) x) :=
    coupled_bounded_factor_size _ _ hR (apply_nonneg _ _)
      (fun _ => apply_nonneg _ _) hlow (fun _ => apply_nonneg _ _) hhigh
      (add_nonneg zero_le_one (apply_nonneg _ _)) (add_le_add le_rfl (hψp _ x))
  exact (hCb (ψ x) ((hψp base x).trans hx.le) (v x) (w x)).trans
    ((mul_le_mul_of_nonneg_left hb hC).trans_eq
      (by simp only [Nat.add_assoc, Nat.add_comm r s]; ac_rfl))

end ContinuousFlexibility.Statements
