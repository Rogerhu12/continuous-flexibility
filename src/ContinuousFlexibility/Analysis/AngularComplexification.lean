module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith

/-!
# Complexification of a real Hilbert space

The complexification is the real Hilbert product of two copies of the
original space.  Its complex scalar multiplication is explicit; in
particular no separability or finite-dimensionality assumption is used.
The norm is the existing product `L²` norm, not the product max norm.
-/

@[expose] public section

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
    ext <;> simp only [re_mk, im_mk, re_real_smul, im_real_smul, smul_zero, RingHom.id_apply]
  norm_map' x := by
    change ‖mk x 0‖ = ‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq, re_mk, im_mk, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

@[simp] theorem ofReal_apply (x : H) : ofReal x = mk x 0 := rfl
@[simp] theorem re_ofReal (x : H) : (ofReal x).re = x := re_mk x 0
@[simp] theorem im_ofReal (x : H) : (ofReal x).im = 0 := im_mk x 0

@[simp] theorem norm_ofReal (x : H) : ‖ofReal x‖ = ‖x‖ := ofReal.norm_map x

/-- Replacing the two components by their norms preserves the product norm. -/
theorem norm_mk_norm (x y : H) :
    ‖(mk ‖x‖ ‖y‖ : AngularComplexification ℝ)‖ = ‖mk x y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [norm_sq, re_mk, im_mk, Real.norm_of_nonneg (norm_nonneg _)]

/-- Coordinatewise norm bounds imply the corresponding Hilbert product bound. -/
theorem norm_mk_le_of_bounds {x y : H} {X Y : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hx : ‖x‖ ≤ X) (hy : ‖y‖ ≤ Y) :
    ‖mk x y‖ ≤ ‖(mk X Y : AngularComplexification ℝ)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [norm_sq, re_mk, im_mk, Real.norm_of_nonneg hX,
    Real.norm_of_nonneg hY] using
    add_le_add ((sq_le_sq₀ (norm_nonneg _) hX).mpr hx)
      ((sq_le_sq₀ (norm_nonneg _) hY).mpr hy)

section Operators

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- Componentwise extension of a real linear map, as a complex linear map. -/
def extendLinear (T : H →ₗ[ℝ] F) :
    AngularComplexification H →ₗ[ℂ] AngularComplexification F where
  toFun u := mk (T u.re) (T u.im)
  map_add' u v := by
    ext <;> simp only [re_mk, im_mk, re_add, im_add, map_add]
  map_smul' z u := by
    ext <;> simp only [re_mk, im_mk, re_smul, im_smul, map_sub, map_add, map_smul,
      RingHom.id_apply]

@[simp] theorem extendLinear_apply (T : H →ₗ[ℝ] F) (u : AngularComplexification H) :
    extendLinear T u = mk (T u.re) (T u.im) := rfl

theorem norm_extendLinear_le (T : H →ₗ[ℝ] F) {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ x, ‖T x‖ ≤ M * ‖x‖) (u : AngularComplexification H) :
    ‖extendLinear T u‖ ≤ M * ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp
  have hx := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mpr (hT u.re)
  have hy := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mpr (hT u.im)
  simp only [extendLinear_apply, norm_sq, re_mk, im_mk, mul_pow] at hx hy ⊢
  nlinarith

/-- A bounded real operator extends to a bounded complex operator. -/
def extend (T : H →L[ℝ] F) :
    AngularComplexification H →L[ℂ] AngularComplexification F :=
  (extendLinear T.toLinearMap).mkContinuous ‖T‖
    (norm_extendLinear_le T.toLinearMap (norm_nonneg T) T.le_opNorm)

@[simp] theorem extend_apply (T : H →L[ℝ] F) (u : AngularComplexification H) :
    extend T u = mk (T u.re) (T u.im) := by
  unfold extend
  simp only [LinearMap.mkContinuous_apply, extendLinear_apply, ContinuousLinearMap.coe_coe]

@[simp] theorem re_extend (T : H →L[ℝ] F) (u : AngularComplexification H) :
    (extend T u).re = T u.re := by rw [extend_apply, re_mk]

@[simp] theorem im_extend (T : H →L[ℝ] F) (u : AngularComplexification H) :
    (extend T u).im = T u.im := by rw [extend_apply, im_mk]

@[simp] theorem extend_ofReal (T : H →L[ℝ] F) (x : H) :
    extend T (ofReal x) = ofReal (T x) := by
  ext <;> simp only [re_extend, im_extend, re_ofReal, im_ofReal, map_zero]

/-- Complexification preserves the operator norm exactly. -/
@[simp] theorem norm_extend (T : H →L[ℝ] F) : ‖extend T‖ = ‖T‖ := by
  apply le_antisymm
  · apply (extend T).opNorm_le_bound (norm_nonneg T)
    intro u
    simpa only [extend_apply, extendLinear_apply, ContinuousLinearMap.coe_coe] using
      norm_extendLinear_le T.toLinearMap (norm_nonneg T) T.le_opNorm u
  · apply T.opNorm_le_bound (norm_nonneg (extend T))
    intro x
    simpa only [extend_ofReal, norm_ofReal] using (extend T).le_opNorm (ofReal x)

@[simp] theorem extend_id :
    extend (ContinuousLinearMap.id ℝ H) = ContinuousLinearMap.id ℂ (AngularComplexification H) := by
  apply ContinuousLinearMap.ext
  intro u
  ext <;> simp only [re_extend, im_extend, ContinuousLinearMap.id_apply]

@[simp] theorem extend_comp (S : F →L[ℝ] G) (T : H →L[ℝ] F) :
    extend (S.comp T) = (extend S).comp (extend T) := by
  apply ContinuousLinearMap.ext
  intro u
  ext <;> simp only [re_extend, im_extend, ContinuousLinearMap.comp_apply]

@[simp] theorem extend_add (S T : H →L[ℝ] F) : extend (S + T) = extend S + extend T := by
  apply ContinuousLinearMap.ext
  intro u
  ext <;> simp only [re_extend, im_extend, re_add, im_add, ContinuousLinearMap.add_apply]

@[simp] theorem extend_sub (S T : H →L[ℝ] F) : extend (S - T) = extend S - extend T := by
  apply ContinuousLinearMap.ext
  intro u
  ext <;> simp only [re_extend, im_extend, re_sub, im_sub, ContinuousLinearMap.sub_apply]

@[simp] theorem extend_zero : extend (0 : H →L[ℝ] F) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  ext <;> simp only [re_extend, im_extend, re_zero, im_zero, ContinuousLinearMap.zero_apply]

/-- A real two-term estimate transfers with exactly the same coefficients.
The comparison components may belong to different Hilbert spaces. -/
theorem norm_mk_le_two_term {x y : H} {x₁ y₁ : F} {x₂ y₂ : G} {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hx : ‖x‖ ≤ a * ‖x₁‖ + c * ‖x₂‖)
    (hy : ‖y‖ ≤ a * ‖y₁‖ + c * ‖y₂‖) :
    ‖mk x y‖ ≤ a * ‖mk x₁ y₁‖ + c * ‖mk x₂ y₂‖ := by
  have hpair :
      (mk (a * ‖x₁‖ + c * ‖x₂‖) (a * ‖y₁‖ + c * ‖y₂‖) : AngularComplexification ℝ) =
        a • mk ‖x₁‖ ‖y₁‖ + c • mk ‖x₂‖ ‖y₂‖ := by
    ext <;> simp only [re_mk, im_mk, re_add, im_add,
      re_real_smul, im_real_smul, smul_eq_mul]
  calc
    ‖mk x y‖ ≤ ‖(mk (a * ‖x₁‖ + c * ‖x₂‖) (a * ‖y₁‖ + c * ‖y₂‖) :
        AngularComplexification ℝ)‖ :=
      norm_mk_le_of_bounds
        (add_nonneg (mul_nonneg ha (norm_nonneg _)) (mul_nonneg hc (norm_nonneg _)))
        (add_nonneg (mul_nonneg ha (norm_nonneg _)) (mul_nonneg hc (norm_nonneg _))) hx hy
    _ = ‖a • (mk ‖x₁‖ ‖y₁‖ : AngularComplexification ℝ) + c • mk ‖x₂‖ ‖y₂‖‖ := by
      rw [hpair]
    _ ≤ ‖a • (mk ‖x₁‖ ‖y₁‖ : AngularComplexification ℝ)‖ +
        ‖c • (mk ‖x₂‖ ‖y₂‖ : AngularComplexification ℝ)‖ := norm_add_le _ _
    _ = a * ‖mk x₁ y₁‖ + c * ‖mk x₂ y₂‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hc,
        norm_mk_norm, norm_mk_norm]

end Operators

end AngularComplexification

end ContinuousFlexibility.Analysis
