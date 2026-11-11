import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

/-!
# Complexification of a real Hilbert space

The complexification is the real Hilbert product of two copies of the
original space.  Its complex scalar multiplication is explicit; in
particular no separability or finite-dimensionality assumption is used.
The norm is the existing product `L²` norm, not the product max norm.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- The two real components of a complexified Hilbert vector, with the
Hilbert product norm. -/
def AngularComplexification (H : Type*) : Type _ := WithLp 2 (H × H)

namespace AngularComplexification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

instance instNormedAddCommGroup : NormedAddCommGroup (AngularComplexification H) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (H × H)))

instance instRealInnerProductSpace : InnerProductSpace ℝ (AngularComplexification H) :=
  inferInstanceAs (InnerProductSpace ℝ (WithLp 2 (H × H)))

instance instCompleteSpace [CompleteSpace H] : CompleteSpace (AngularComplexification H) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (H × H)))

/-- Real component. -/
def re (u : AngularComplexification H) : H := WithLp.fst u

/-- Imaginary component. -/
def im (u : AngularComplexification H) : H := WithLp.snd u

/-- Form a complexified vector from its two real components. -/
def mk (x y : H) : AngularComplexification H := WithLp.toLp 2 (x, y)

@[simp] theorem re_mk (x y : H) : (mk x y).re = x := WithLp.toLp_fst (x, y)
@[simp] theorem im_mk (x y : H) : (mk x y).im = y := WithLp.toLp_snd (x, y)

@[ext] theorem ext {u v : AngularComplexification H}
    (hre : u.re = v.re) (him : u.im = v.im) : u = v :=
  WithLp.ofLp_injective 2 (Prod.ext hre him)

@[simp] theorem mk_re_im (u : AngularComplexification H) : mk u.re u.im = u := by
  ext <;> simp only [re_mk, im_mk]

@[simp] theorem re_zero : (0 : AngularComplexification H).re = 0 := WithLp.zero_fst
@[simp] theorem im_zero : (0 : AngularComplexification H).im = 0 := WithLp.zero_snd
@[simp] theorem re_add (u v : AngularComplexification H) : (u + v).re = u.re + v.re :=
  WithLp.add_fst u v
@[simp] theorem im_add (u v : AngularComplexification H) : (u + v).im = u.im + v.im :=
  WithLp.add_snd u v
@[simp] theorem re_sub (u v : AngularComplexification H) : (u - v).re = u.re - v.re :=
  WithLp.sub_fst u v
@[simp] theorem im_sub (u v : AngularComplexification H) : (u - v).im = u.im - v.im :=
  WithLp.sub_snd u v
@[simp] theorem re_real_smul (r : ℝ) (u : AngularComplexification H) :
    (r • u).re = r • u.re := WithLp.smul_fst u r
@[simp] theorem im_real_smul (r : ℝ) (u : AngularComplexification H) :
    (r • u).im = r • u.im := WithLp.smul_snd u r

instance instComplexSMul : SMul ℂ (AngularComplexification H) where
  smul z u := mk (z.re • u.re - z.im • u.im) (z.im • u.re + z.re • u.im)

@[simp] theorem re_smul (z : ℂ) (u : AngularComplexification H) :
    (z • u).re = z.re • u.re - z.im • u.im :=
  re_mk _ _

@[simp] theorem im_smul (z : ℂ) (u : AngularComplexification H) :
    (z • u).im = z.im • u.re + z.re • u.im :=
  im_mk _ _

instance instComplexModule : Module ℂ (AngularComplexification H) where
  one_smul u := by
    ext <;> simp only [re_smul, im_smul, Complex.one_re, Complex.one_im,
      one_smul, zero_smul, sub_zero, zero_add]
  mul_smul z w u := by
    ext <;> simp only [re_smul, im_smul, Complex.mul_re, Complex.mul_im] <;> module
  smul_add z u v := by
    ext <;> simp only [re_smul, im_smul, re_add, im_add] <;> module
  smul_zero z := by
    ext <;> simp only [re_smul, im_smul, re_zero, im_zero, smul_zero,
      sub_zero, add_zero]
  add_smul z w u := by
    ext <;> simp only [re_smul, im_smul, re_add, im_add,
      Complex.add_re, Complex.add_im] <;> module
  zero_smul u := by
    ext <;> simp only [re_smul, im_smul, re_zero, im_zero,
      Complex.zero_re, Complex.zero_im, zero_smul, sub_zero, add_zero]

@[simp] theorem ofReal_smul (r : ℝ) (u : AngularComplexification H) :
    (r : ℂ) • u = r • u := by
  ext <;> simp only [re_smul, im_smul, re_real_smul, im_real_smul,
    Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero, zero_add]

instance instScalarTower : IsScalarTower ℝ ℂ (AngularComplexification H) where
  smul_assoc r z u := by
    ext <;> simp only [re_smul, im_smul, re_real_smul, im_real_smul,
      Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> module

/-- The squared norm is the sum of the squared component norms. -/
theorem norm_sq (u : AngularComplexification H) :
    ‖u‖ ^ 2 = ‖u.re‖ ^ 2 + ‖u.im‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 u

theorem norm_re_le (u : AngularComplexification H) : ‖u.re‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem norm_im_le (u : AngularComplexification H) : ‖u.im‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- The explicit complex action scales the Hilbert product norm exactly. -/
theorem norm_complex_smul (z : ℂ) (u : AngularComplexification H) :
    ‖z • u‖ = ‖z‖ * ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [norm_sq, re_smul, im_smul, norm_sub_sq_real, norm_add_sq_real, mul_pow,
    Complex.sq_norm, Complex.normSq_apply, norm_sq]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right]
  ring

instance instComplexNormedSpace : NormedSpace ℂ (AngularComplexification H) where
  norm_smul_le z u := (norm_complex_smul z u).le

/-- The Hermitian extension of the original real scalar product. -/
def complexInner (u v : AngularComplexification H) : ℂ :=
  ⟨inner ℝ u.re v.re + inner ℝ u.im v.im,
    inner ℝ u.re v.im - inner ℝ u.im v.re⟩

instance instComplexInnerProductSpace : InnerProductSpace ℂ (AngularComplexification H) where
  inner := complexInner
  norm_sq_eq_re_inner u := by
    simpa only [complexInner, RCLike.re_to_complex,
      real_inner_self_eq_norm_sq] using norm_sq u
  conj_inner_symm u v := by
    apply Complex.ext
    · simp only [complexInner, Complex.conj_re]
      rw [real_inner_comm v.re u.re, real_inner_comm v.im u.im]
    · simp only [complexInner, Complex.conj_im]
      rw [real_inner_comm v.re u.im, real_inner_comm v.im u.re]
      ring
  add_left u v w := by
    apply Complex.ext <;>
      simp only [complexInner, re_add, im_add, inner_add_left,
        Complex.add_re, Complex.add_im] <;> ring
  smul_left u v z := by
    apply Complex.ext <;>
      simp only [complexInner, re_smul, im_smul, inner_sub_left, inner_add_left,
        real_inner_smul_left, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im] <;> ring

/-- The original real Hilbert space embeds isometrically as the real axis. -/
def ofReal : H →ₗᵢ[ℝ] AngularComplexification H where
  toFun x := mk x 0
  map_add' x y := by ext <;> simp only [re_mk, im_mk, re_add, im_add, add_zero]
  map_smul' r x := by
    ext <;> simp only [re_mk, im_mk, re_real_smul, im_real_smul, smul_zero]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq, re_mk, im_mk, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

@[simp] theorem ofReal_apply (x : H) : ofReal x = mk x 0 := rfl
@[simp] theorem re_ofReal (x : H) : (ofReal x).re = x := re_mk x 0
@[simp] theorem im_ofReal (x : H) : (ofReal x).im = 0 := im_mk x 0

end AngularComplexification

end ContinuousFlexibility.Analysis
