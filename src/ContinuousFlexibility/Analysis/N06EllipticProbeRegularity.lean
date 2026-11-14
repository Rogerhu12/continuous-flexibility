module

public import ContinuousFlexibility.Analysis.N05PolynomialProbes

/-!
# Recovering coefficient differentiability from genuine elliptic probes

The totalized Frechet derivative is zero at a nondifferentiable flux.
An affine family of quadratic probes with a nonzero leading coefficient
rules that possibility out. A probe factor is one at the point, so its
product is differentiable exactly when the original coefficient is.
The same directional lemma handles both coordinate axes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- A smooth nonvanishing factor cannot conceal nondifferentiability. -/
theorem n06_differentiableAt_of_mul_nonzero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {p : E} (hg : DifferentiableAt ℝ g p) (hne : g p ≠ 0)
    (hprod : DifferentiableAt ℝ (fun q => f q * g q) p) :
    DifferentiableAt ℝ f p := by
  have hinv : DifferentiableAt ℝ (fun q => (g q)⁻¹) p :=
    ((hasDerivAt_inv hne).hasFDerivAt.comp p hg.hasFDerivAt).differentiableAt
  have hd := hprod.mul hinv
  apply hd.congr_of_eventuallyEq
  filter_upwards [hg.continuousAt.eventually_ne hne] with q hq
  change f q = (f q * g q) * (g q)⁻¹
  rw [mul_assoc, mul_inv_cancel₀ hq, mul_one]

/-- If the secondary direction kills the affine factor, its flux cannot
account for a nonconstant leading response. The primary coefficient is
therefore actually differentiable. No regularity of either input field
is assumed. -/
theorem n06_directional_flux_leading_differentiable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E →L[ℝ] ℝ) (p v w : E) {f g : E → ℝ} {A B : ℝ}
    (hw : ℓ w = 0) (hA : A ≠ 0)
    (hprobe : ∀ s : ℝ,
      fderiv ℝ (fun q => f q * (1 + s * (ℓ q - ℓ p))) p v +
        fderiv ℝ (fun q => g q * (1 + s * (ℓ q - ℓ p))) p w = B + s * A) :
    DifferentiableAt ℝ f p := by
  let P (s : ℝ) (q : E) : ℝ := 1 + s * (ℓ q - ℓ p)
  have hP (s : ℝ) : HasFDerivAt (P s) (s • ℓ) p := by
    exact ((ℓ.hasFDerivAt.sub_const (ℓ p)).const_mul s).const_add 1
  have hp (s : ℝ) : P s p = 1 := by simp only [P, sub_self, mul_zero, add_zero]
  have hdw (s : ℝ) : fderiv ℝ (P s) p w = 0 := by
    rw [(hP s).fderiv, ContinuousLinearMap.smul_apply, hw, smul_zero]
  by_contra hf
  have hnot (s : ℝ) : ¬DifferentiableAt ℝ (fun q => f q * P s q) p := by
    intro h
    exact hf (n06_differentiableAt_of_mul_nonzero (hP s).differentiableAt
      (by rw [hp s]; norm_num) h)
  have hzero (s : ℝ) : fderiv ℝ (fun q => f q * P s q) p v = 0 := by
    rw [fderiv_zero_of_not_differentiableAt (hnot s), ContinuousLinearMap.zero_apply]
  by_cases hg : DifferentiableAt ℝ g p
  · have hvalue (s : ℝ) : fderiv ℝ (fun q => g q * P s q) p w = fderiv ℝ g p w := by
      rw [fderiv_fun_mul hg (hP s).differentiableAt,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply, hdw, hp]
      simp only [smul_eq_mul, mul_zero, one_mul, zero_add]
    have h0 := hprobe 0
    have h1 := hprobe 1
    change fderiv ℝ (fun q => f q * P 0 q) p v +
      fderiv ℝ (fun q => g q * P 0 q) p w = B + 0 * A at h0
    change fderiv ℝ (fun q => f q * P 1 q) p v +
      fderiv ℝ (fun q => g q * P 1 q) p w = B + 1 * A at h1
    rw [hzero, hvalue] at h0 h1
    exact hA (by linarith only [h0, h1])
  · have hgnot (s : ℝ) : ¬DifferentiableAt ℝ (fun q => g q * P s q) p := by
      intro h
      exact hg (n06_differentiableAt_of_mul_nonzero (hP s).differentiableAt
        (by rw [hp s]; norm_num) h)
    have hvalue (s : ℝ) : fderiv ℝ (fun q => g q * P s q) p w = 0 := by
      rw [fderiv_zero_of_not_differentiableAt (hgnot s), ContinuousLinearMap.zero_apply]
    have h0 := hprobe 0
    have h1 := hprobe 1
    change fderiv ℝ (fun q => f q * P 0 q) p v +
      fderiv ℝ (fun q => g q * P 0 q) p w = B + 0 * A at h0
    change fderiv ℝ (fun q => f q * P 1 q) p v +
      fderiv ℝ (fun q => g q * P 1 q) p w = B + 1 * A at h1
    rw [hzero, hvalue] at h0 h1
    exact hA (by linarith only [h0, h1])

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- One coordinate-independent polynomial probe supplies both pure axes. -/
def n06PureQuadraticProbe (ℓ : PolarPoint →L[ℝ] ℝ) (x : PolarPoint) (s : ℝ)
    (y : PolarPoint) : ℝ :=
  (ℓ y - ℓ x) + s * (ℓ y - ℓ x) ^ 2

theorem n06PureQuadraticProbe_contDiff (ℓ : PolarPoint →L[ℝ] ℝ)
    (x : PolarPoint) (s : ℝ) : ContDiff ℝ ∞ (n06PureQuadraticProbe ℓ x s) :=
  (ℓ.contDiff.sub contDiff_const).add
    (contDiff_const.mul ((ℓ.contDiff.sub contDiff_const).pow 2))

theorem n06PureQuadraticProbe_fderiv (ℓ : PolarPoint →L[ℝ] ℝ)
    (x : PolarPoint) (s : ℝ) (y v : PolarPoint) :
    fderiv ℝ (n06PureQuadraticProbe ℓ x s) y v =
      (1 + 2 * s * (ℓ y - ℓ x)) * ℓ v := by
  have h : HasFDerivAt (fun q => ℓ q - ℓ x) ℓ y := ℓ.hasFDerivAt.sub_const (ℓ x)
  have hd := h.add ((h.pow 2).const_mul s)
  change HasFDerivAt (n06PureQuadraticProbe ℓ x s) _ y at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Nat.cast_ofNat, pow_one]
  ring

theorem n06PureQuadraticProbe_partials (x : PolarPoint) (s : ℝ) :
    (radialPartial (n06PureQuadraticProbe (ContinuousLinearMap.fst ℝ ℝ ℝ) x s) =
      fun y => 1 + 2 * s * (y.1 - x.1)) ∧
    (angularPartial (n06PureQuadraticProbe (ContinuousLinearMap.fst ℝ ℝ ℝ) x s) =
      fun _ => 0) ∧
    (radialPartial (n06PureQuadraticProbe (ContinuousLinearMap.snd ℝ ℝ ℝ) x s) =
      fun _ => 0) ∧
    (angularPartial (n06PureQuadraticProbe (ContinuousLinearMap.snd ℝ ℝ ℝ) x s) =
      fun y => 1 + 2 * s * (y.2 - x.2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext y <;>
    simp only [radialPartial, angularPartial, n06PureQuadraticProbe_fderiv,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', mul_one, mul_zero]

/-- The two nonzero pure principal responses force both diagonal fields
to be differentiable. The same abstract directional proof handles each. -/
theorem n06_diagonal_differentiable_of_pure_probes
    {L : SymmetricCoefficients} {x : PolarPoint} {α γ dr dt : ℝ}
    (hα : α ≠ 0) (hγ : γ ≠ 0)
    (hr : ∀ s, divergenceOperator L
      (n06PureQuadraticProbe (ContinuousLinearMap.fst ℝ ℝ ℝ) x s) x = dr + 2 * s * α)
    (ht : ∀ s, divergenceOperator L
      (n06PureQuadraticProbe (ContinuousLinearMap.snd ℝ ℝ ℝ) x s) x = dt + 2 * s * γ) :
    DifferentiableAt ℝ L.a x ∧ DifferentiableAt ℝ L.c x := by
  constructor
  · apply n06_directional_flux_leading_differentiable
      (ContinuousLinearMap.fst ℝ ℝ ℝ) x (1, 0) (0, 1) (g := L.b) (A := α)
        (B := dr) rfl hα
    intro s
    have h := hr (s / 2)
    rw [divergenceOperator, (n06PureQuadraticProbe_partials x (s / 2)).1,
      (n06PureQuadraticProbe_partials x (s / 2)).2.1] at h
    simp only [mul_zero, add_zero] at h
    have hs : 2 * (s / 2) = s := by ring
    simpa only [radialPartial, angularPartial, hs, ContinuousLinearMap.coe_fst',
      mul_assoc] using h
  · apply n06_directional_flux_leading_differentiable
      (ContinuousLinearMap.snd ℝ ℝ ℝ) x (0, 1) (1, 0) (g := L.b) (A := γ)
        (B := dt) rfl hγ
    intro s
    have h := ht (s / 2)
    rw [divergenceOperator, (n06PureQuadraticProbe_partials x (s / 2)).2.2.1,
      (n06PureQuadraticProbe_partials x (s / 2)).2.2.2] at h
    simp only [mul_zero, zero_add] at h
    have hs : 2 * (s / 2) = s := by ring
    simpa only [radialPartial, angularPartial, hs, ContinuousLinearMap.coe_snd',
      mul_assoc, add_comm] using h

/-- Adding the other coordinate makes both mixed-coefficient factors
nonzero. With the diagonal fields now differentiable, a nonzero leading
response forces the mixed coefficient to be differentiable as well. -/
theorem n06_mixed_differentiable_of_biased_probes
    {L : SymmetricCoefficients} {x : PolarPoint} {α d : ℝ}
    (ha : DifferentiableAt ℝ L.a x) (hc : DifferentiableAt ℝ L.c x) (hα : α ≠ 0)
    (hprobe : ∀ s, divergenceOperator L
      (fun y => n06PureQuadraticProbe (ContinuousLinearMap.fst ℝ ℝ ℝ) x s y +
        n05AngularLinear x y) x = d + 2 * s * α) :
    DifferentiableAt ℝ L.b x := by
  by_contra hb
  let P (s : ℝ) (y : PolarPoint) : ℝ := 1 + 2 * s * (y.1 - x.1)
  have hP (s : ℝ) : DifferentiableAt ℝ (P s) x :=
    ((differentiableAt_const (1 : ℝ)).add
      ((differentiableAt_const (2 * s)).mul
        (differentiableAt_fst.sub_const x.1)))
  have hp (s : ℝ) : P s x ≠ 0 := by norm_num [P]
  have hNnot (s : ℝ) : ¬DifferentiableAt ℝ (fun y => L.a y * P s y + L.b y) x := by
    intro h
    have hd := h.sub (ha.mul (hP s))
    apply hb
    convert hd using 1
    funext y
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have hTnot (s : ℝ) : ¬DifferentiableAt ℝ (fun y => L.b y * P s y + L.c y) x := by
    intro h
    have hd : DifferentiableAt ℝ (fun y => L.b y * P s y) x := by
      convert h.sub hc using 1
      funext y
      simp only [Pi.sub_apply]
      ring
    exact hb (n06_differentiableAt_of_mul_nonzero (hP s) (hp s) hd)
  have hzero (s : ℝ) : d + 2 * s * α = 0 := by
    have h := hprobe s
    have hR := (n06PureQuadraticProbe_contDiff
      (ContinuousLinearMap.fst ℝ ℝ ℝ) x s).differentiable (by simp)
    have hT := (n05AngularLinear_contDiff x).differentiable (by simp)
    have hr : radialPartial (fun y =>
        n06PureQuadraticProbe (ContinuousLinearMap.fst ℝ ℝ ℝ) x s y +
          n05AngularLinear x y) = P s := by
      funext y
      rw [radialPartial_add (hR y) (hT y),
        (n06PureQuadraticProbe_partials x s).1, n05AngularLinear_radial]
      simp only [P, add_zero]
    have ht : angularPartial (fun y =>
        n06PureQuadraticProbe (ContinuousLinearMap.fst ℝ ℝ ℝ) x s y +
          n05AngularLinear x y) = fun _ => 1 := by
      funext y
      rw [angularPartial_add (hR y) (hT y),
        (n06PureQuadraticProbe_partials x s).2.1, n05AngularLinear_angular]
      norm_num
    rw [divergenceOperator, hr, ht] at h
    simp only [mul_one] at h
    rw [radialPartial, angularPartial,
      fderiv_zero_of_not_differentiableAt (hNnot s),
      fderiv_zero_of_not_differentiableAt (hTnot s),
      ContinuousLinearMap.zero_apply, zero_add] at h
    exact h.symm
  exact hα (by linarith only [hzero 0, hzero 1])

end ContinuousFlexibility.Statements
