module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Tactic.Ring

/-!
# Actual product-space L² synthesis

A radial L² vector and an angular L² vector define their pointwise product
in the actual product measure. An orthonormal angular family therefore
induces an isometric, convergent synthesis of square-summable radial vectors.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

theorem referenceL2Tensor_memLp (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    MemLp (fun z : α × β => f z.1 * g z.2) 2 (μ.prod ν) := by
  have hf : AEStronglyMeasurable (fun z : α × β => f z.1) (μ.prod ν) :=
    (Lp.aestronglyMeasurable f).comp_fst
  have hg : AEStronglyMeasurable (fun z : α × β => g z.2) (μ.prod ν) :=
    (Lp.aestronglyMeasurable g).comp_snd
  apply (memLp_two_iff_integrable_sq (hf.mul hg)).2
  change Integrable (fun z : α × β => (f z.1 * g z.2) ^ 2) (μ.prod ν)
  simpa only [mul_pow] using
    (Lp.memLp f).integrable_sq.mul_prod (Lp.memLp g).integrable_sq

/-- The actual radial-angular product, as a vector in the product L² space. -/
def referenceL2Tensor (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    Lp ℝ 2 (μ.prod ν) :=
  (referenceL2Tensor_memLp f g).toLp (fun z : α × β => f z.1 * g z.2)

theorem referenceL2Tensor_ae (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    referenceL2Tensor f g =ᵐ[μ.prod ν] fun z : α × β => f z.1 * g z.2 :=
  (referenceL2Tensor_memLp f g).coeFn_toLp

theorem referenceL2Tensor_add_left (f₁ f₂ : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    referenceL2Tensor (f₁ + f₂) g = referenceL2Tensor f₁ g + referenceL2Tensor f₂ g := by
  apply Lp.ext
  have hf : ∀ᵐ z : α × β ∂μ.prod ν, (f₁ + f₂) z.1 = f₁ z.1 + f₂ z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae (Lp.coeFn_add f₁ f₂)
  filter_upwards [referenceL2Tensor_ae (f₁ + f₂) g,
    referenceL2Tensor_ae f₁ g, referenceL2Tensor_ae f₂ g,
    Lp.coeFn_add (referenceL2Tensor f₁ g) (referenceL2Tensor f₂ g), hf]
    with z hsum h₁ h₂ hout hrad
  simp only [Pi.add_apply] at hout
  rw [hsum, hout, h₁, h₂, hrad]
  ring

theorem referenceL2Tensor_smul_left (c : ℝ) (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    referenceL2Tensor (c • f) g = c • referenceL2Tensor f g := by
  apply Lp.ext
  have hf : ∀ᵐ z : α × β ∂μ.prod ν, (c • f) z.1 = c * f z.1 := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae (Lp.coeFn_smul c f)
  filter_upwards [referenceL2Tensor_ae (c • f) g,
    referenceL2Tensor_ae f g, Lp.coeFn_smul c (referenceL2Tensor f g), hf]
    with z hsmul hprod hout hrad
  simp only [Pi.smul_apply, smul_eq_mul] at hout
  rw [hsmul, hout, hprod, hrad]
  ring

/-- Product-space inner products separate into the two actual L² factors. -/
theorem referenceL2Tensor_inner (f₁ f₂ : Lp ℝ 2 μ) (g₁ g₂ : Lp ℝ 2 ν) :
    ⟪referenceL2Tensor f₁ g₁, referenceL2Tensor f₂ g₂⟫_ℝ =
      ⟪f₁, f₂⟫_ℝ * ⟪g₁, g₂⟫_ℝ := by
  calc
    _ = ∫ z : α × β, (f₁ z.1 * g₁ z.2) * (f₂ z.1 * g₂ z.2) ∂μ.prod ν := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [referenceL2Tensor_ae f₁ g₁, referenceL2Tensor_ae f₂ g₂]
        with z h₁ h₂
      simp only [Real.inner_apply, h₁, h₂]
    _ = ∫ z : α × β, (f₁ z.1 * f₂ z.1) * (g₁ z.2 * g₂ z.2) ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards with z
      ring
    _ = (∫ r, f₁ r * f₂ r ∂μ) * (∫ θ, g₁ θ * g₂ θ ∂ν) :=
      integral_prod_mul (fun r => f₁ r * f₂ r) (fun θ => g₁ θ * g₂ θ)
    _ = _ := by simp only [L2.inner_def, Real.inner_apply]

theorem referenceL2Tensor_norm_sq (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    ‖referenceL2Tensor f g‖ ^ 2 = ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using referenceL2Tensor_inner f f g g

/-- Multiplication by a unit angular L² vector is an actual product-space isometry. -/
def referenceL2TensorIsometry (g : Lp ℝ 2 ν) (hg : ‖g‖ = 1) :
    Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (μ.prod ν) where
  toFun f := referenceL2Tensor f g
  map_add' f₁ f₂ := referenceL2Tensor_add_left f₁ f₂ g
  map_smul' c f := referenceL2Tensor_smul_left c f g
  norm_map' f := by
    change ‖referenceL2Tensor f g‖ = ‖f‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [hg, one_pow, mul_one] using referenceL2Tensor_norm_sq f g

variable {ι : Type*}

/-- Angular orthonormality gives an orthogonal family of full radial subspaces. -/
theorem referenceL2Tensor_orthogonalFamily
    (φ : ι → Lp ℝ 2 ν) (hφ : Orthonormal ℝ φ) :
    OrthogonalFamily ℝ (fun _ : ι => Lp ℝ 2 μ)
      (fun i => referenceL2TensorIsometry (μ := μ) (φ i) (hφ.norm_eq_one i)) := by
  intro i j hij f g
  change ⟪referenceL2Tensor f (φ i), referenceL2Tensor g (φ j)⟫_ℝ = 0
  rw [referenceL2Tensor_inner, hφ.inner_eq_zero hij, mul_zero]

/-- Isometric synthesis in the actual radial-angular L² space. -/
def referenceL2TensorSynthesis
    (φ : ι → Lp ℝ 2 ν) (hφ : Orthonormal ℝ φ) :
    lp (fun _ : ι => Lp ℝ 2 μ) 2 →ₗᵢ[ℝ] Lp ℝ 2 (μ.prod ν) :=
  (referenceL2Tensor_orthogonalFamily (μ := μ) φ hφ).linearIsometry

theorem referenceL2TensorSynthesis_hasSum
    (φ : ι → Lp ℝ 2 ν) (hφ : Orthonormal ℝ φ)
    (f : lp (fun _ : ι => Lp ℝ 2 μ) 2) :
    HasSum (fun i => referenceL2Tensor (f i) (φ i))
      (referenceL2TensorSynthesis φ hφ f) :=
  (referenceL2Tensor_orthogonalFamily (μ := μ) φ hφ).hasSum_linearIsometry f

theorem referenceL2TensorSynthesis_norm
    (φ : ι → Lp ℝ 2 ν) (hφ : Orthonormal ℝ φ)
    (f : lp (fun _ : ι => Lp ℝ 2 μ) 2) :
    ‖referenceL2TensorSynthesis φ hφ f‖ = ‖f‖ :=
  (referenceL2TensorSynthesis φ hφ).norm_map f

/-- The physical product-space square norm is the sum of the modal square norms. -/
theorem referenceL2TensorSynthesis_norm_sq
    (φ : ι → Lp ℝ 2 ν) (hφ : Orthonormal ℝ φ)
    (f : lp (fun _ : ι => Lp ℝ 2 μ) 2) :
    ‖referenceL2TensorSynthesis φ hφ f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  rw [referenceL2TensorSynthesis_norm]
  have hs := lp.hasSum_norm (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by norm_num) f
  simpa using hs.tsum_eq.symm

end ContinuousFlexibility.Statements
