import ContinuousFlexibility.Analysis.PhysicalTransmissionOperator

/-!
# Cubic coefficient differences act on the degenerate graph norm

This is the pointwise multiplication step in the positive-cylinder relative estimate.
The coefficients are genuine cubic multiples and all derivatives are the actual partial
derivatives. A local equality of coefficient differences is sufficient for the final
two-operator estimate; no equality outside the canonical piece is required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

private theorem n06_five_squares (x₁ x₂ x₃ x₄ x₅ : ℝ) :
    (x₁ + x₂ + x₃ + x₄ + x₅) ^ 2 ≤
      5 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 + x₅ ^ 2) := by
  nlinarith only [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ - x₃),
    sq_nonneg (x₁ - x₄), sq_nonneg (x₁ - x₅), sq_nonneg (x₂ - x₃),
    sq_nonneg (x₂ - x₄), sq_nonneg (x₂ - x₅), sq_nonneg (x₃ - x₄),
    sq_nonneg (x₃ - x₅), sq_nonneg (x₄ - x₅)]

private theorem n06_weighted_product_square {a w v x δ : ℝ}
    (hδ : 0 ≤ δ) (ha : |a| ≤ 5 * δ) (hw : w ^ 2 ≤ v) :
    (w * a * x) ^ 2 ≤ 25 * δ ^ 2 * v * x ^ 2 := by
  have ha₂ := (sq_le_sq₀ (abs_nonneg a) (mul_nonneg (by norm_num) hδ)).2 ha
  rw [sq_abs] at ha₂
  norm_num [mul_pow] at ha₂
  calc
    (w * a * x) ^ 2 = a ^ 2 * w ^ 2 * x ^ 2 := by ring
    _ ≤ 25 * δ ^ 2 * w ^ 2 * x ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ha₂ (sq_nonneg w)) (sq_nonneg x)
    _ ≤ 25 * δ ^ 2 * v * x ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hw (by positivity)) (sq_nonneg x)

theorem n06_cubic_firstOrder_abs {d e A Ar At δ : ℝ}
    (hd : 0 ≤ d) (hd₁ : d ≤ 1) (he : |e| ≤ 1)
    (hA : |A| ≤ δ) (hAr : |Ar| ≤ δ) (hAt : |At| ≤ δ) :
    |3 * e * A + d * Ar + d * At| ≤ 5 * δ := by
  have h₁ : |3 * e * A| ≤ 3 * δ := by
    calc
      |3 * e * A| = 3 * |e| * |A| := by rw [abs_mul, abs_mul]; norm_num
      _ ≤ (3 * 1) * δ :=
        mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) hA
          (abs_nonneg A) (by norm_num)
      _ = 3 * δ := by ring
  have h₂ : |d * Ar| ≤ δ := by
    rw [abs_mul, abs_of_nonneg hd]
    simpa only [one_mul] using mul_le_mul hd₁ hAr (abs_nonneg Ar) zero_le_one
  have h₃ : |d * At| ≤ δ := by
    rw [abs_mul, abs_of_nonneg hd]
    simpa only [one_mul] using mul_le_mul hd₁ hAt (abs_nonneg At) zero_le_one
  calc
    |3 * e * A + d * Ar + d * At| ≤ |3 * e * A + d * Ar| + |d * At| :=
      abs_add_le _ _
    _ ≤ (|3 * e * A| + |d * Ar|) + |d * At| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (3 * δ + δ) + δ := add_le_add (add_le_add h₁ h₂) h₃
    _ = 5 * δ := by ring

/-- The expansion of the cubic-coefficient divergence operator, with derivative values as inputs. -/
def n06CubicExpression (d e A B C Ar Bt Br Ct urr urt utt ur ut : ℝ) : ℝ :=
  d ^ 3 * A * urr + d ^ 3 * (2 * B) * urt + d ^ 3 * C * utt +
    d ^ 2 * (3 * e * A + d * Ar + d * Bt) * ur +
    d ^ 2 * (3 * e * B + d * Br + d * Ct) * ut

/-- The cubic zero absorbs exactly the five weighted graph derivatives. -/
theorem n06CubicExpression_sq_le
    {d e A B C Ar Bt Br Ct δ : ℝ} (urr urt utt ur ut : ℝ)
    (hd : 0 ≤ d) (hd₁ : d ≤ 1) (he : |e| ≤ 1) (hδ : 0 ≤ δ)
    (hA : |A| ≤ δ) (hB : |B| ≤ δ) (hC : |C| ≤ δ)
    (hAr : |Ar| ≤ δ) (hBt : |Bt| ≤ δ)
    (hBr : |Br| ≤ δ) (hCt : |Ct| ≤ δ) :
    (n06CubicExpression d e A B C Ar Bt Br Ct urr urt utt ur ut) ^ 2 ≤
      125 * δ ^ 2 * (d ^ 4 * urr ^ 2 + d ^ 5 * urt ^ 2 + d ^ 6 * utt ^ 2 +
        d ^ 2 * ur ^ 2 + d ^ 3 * ut ^ 2) := by
  have hstep (n : ℕ) : d ^ (n + 1) ≤ d ^ n := by
    calc
      d ^ (n + 1) = d ^ n * d := pow_succ d n
      _ ≤ d ^ n * 1 := mul_le_mul_of_nonneg_left hd₁ (pow_nonneg hd n)
      _ = d ^ n := mul_one _
  have h₆₄ : (d ^ 3) ^ 2 ≤ d ^ 4 := by
    calc (d ^ 3) ^ 2 = d ^ 6 := by ring
         _ ≤ d ^ 5 := hstep 5
         _ ≤ d ^ 4 := hstep 4
  have h₆₅ : (d ^ 3) ^ 2 ≤ d ^ 5 := by
    calc (d ^ 3) ^ 2 = d ^ 6 := by ring
         _ ≤ d ^ 5 := hstep 5
  have h₆₆ : (d ^ 3) ^ 2 ≤ d ^ 6 := le_of_eq (by ring)
  have h₄₂ : (d ^ 2) ^ 2 ≤ d ^ 2 := by
    calc (d ^ 2) ^ 2 = d ^ 4 := by ring
         _ ≤ d ^ 3 := hstep 3
         _ ≤ d ^ 2 := hstep 2
  have h₄₃ : (d ^ 2) ^ 2 ≤ d ^ 3 := by
    calc (d ^ 2) ^ 2 = d ^ 4 := by ring
         _ ≤ d ^ 3 := hstep 3
  have hA₅ : |A| ≤ 5 * δ := hA.trans (by linarith only [hδ])
  have hB₅ : |2 * B| ≤ 5 * δ := by
    rw [abs_mul]
    norm_num
    linarith only [hB, hδ]
  have hC₅ : |C| ≤ 5 * δ := hC.trans (by linarith only [hδ])
  have hAr₅ := n06_cubic_firstOrder_abs hd hd₁ he hA hAr hBt
  have hBr₅ := n06_cubic_firstOrder_abs hd hd₁ he hB hBr hCt
  let x₁ := d ^ 3 * A * urr
  let x₂ := d ^ 3 * (2 * B) * urt
  let x₃ := d ^ 3 * C * utt
  let x₄ := d ^ 2 * (3 * e * A + d * Ar + d * Bt) * ur
  let x₅ := d ^ 2 * (3 * e * B + d * Br + d * Ct) * ut
  have hx₁ : x₁ ^ 2 ≤ 25 * δ ^ 2 * d ^ 4 * urr ^ 2 :=
    n06_weighted_product_square hδ hA₅ h₆₄
  have hx₂ : x₂ ^ 2 ≤ 25 * δ ^ 2 * d ^ 5 * urt ^ 2 :=
    n06_weighted_product_square hδ hB₅ h₆₅
  have hx₃ : x₃ ^ 2 ≤ 25 * δ ^ 2 * d ^ 6 * utt ^ 2 :=
    n06_weighted_product_square hδ hC₅ h₆₆
  have hx₄ : x₄ ^ 2 ≤ 25 * δ ^ 2 * d ^ 2 * ur ^ 2 :=
    n06_weighted_product_square hδ hAr₅ h₄₂
  have hx₅ : x₅ ^ 2 ≤ 25 * δ ^ 2 * d ^ 3 * ut ^ 2 :=
    n06_weighted_product_square hδ hBr₅ h₄₃
  change (x₁ + x₂ + x₃ + x₄ + x₅) ^ 2 ≤ _
  calc
    (x₁ + x₂ + x₃ + x₄ + x₅) ^ 2 ≤
        5 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 + x₅ ^ 2) :=
      n06_five_squares x₁ x₂ x₃ x₄ x₅
    _ ≤ 5 * (25 * δ ^ 2 * d ^ 4 * urr ^ 2 + 25 * δ ^ 2 * d ^ 5 * urt ^ 2 +
        25 * δ ^ 2 * d ^ 6 * utt ^ 2 + 25 * δ ^ 2 * d ^ 2 * ur ^ 2 +
        25 * δ ^ 2 * d ^ 3 * ut ^ 2) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (add_le_add (add_le_add hx₁ hx₂) hx₃) hx₄) hx₅)
        (by norm_num)
    _ = _ := by ring

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis Filter
open scoped ContDiff Topology

/-- The actual coefficient field obtained by multiplying each divided coefficient by d³. -/
def n06CubicCoefficients (d A B C : PolarPoint → ℝ) : SymmetricCoefficients where
  a := fun p => d p ^ 3 * A p
  b := fun p => d p ^ 3 * B p
  c := fun p => d p ^ 3 * C p

private theorem n06_fderiv_cube_apply {d : PolarPoint → ℝ} {p : PolarPoint}
    (hd : DifferentiableAt ℝ d p) (v : PolarPoint) :
    fderiv ℝ (fun q => d q ^ 3) p v = 3 * d p ^ 2 * fderiv ℝ d p v := by
  rw [(hd.hasFDerivAt.pow 3).fderiv]
  simp only [smul_apply, smul_eq_mul]
  norm_num

/-- Product-rule expansion of the genuine operator, using only local differentiability. -/
theorem n06CubicCoefficients_divergence
    {d A B C u : PolarPoint → ℝ} {p : PolarPoint}
    (hd : DifferentiableAt ℝ d p) (hA : DifferentiableAt ℝ A p)
    (hB : DifferentiableAt ℝ B p) (hC : DifferentiableAt ℝ C p)
    (hu : ContDiffAt ℝ 2 u p) (hdθ : angularPartial d p = 0) :
    divergenceOperator (n06CubicCoefficients d A B C) u p =
      n06CubicExpression (d p) (radialPartial d p) (A p) (B p) (C p)
        (radialPartial A p) (angularPartial B p) (radialPartial B p) (angularPartial C p)
        (radialPartial (radialPartial u) p) (angularPartial (radialPartial u) p)
        (angularPartial (angularPartial u) p) (radialPartial u p) (angularPartial u p) := by
  have hr : radialPartial (fun q => d q ^ 3) p =
      3 * d p ^ 2 * radialPartial d p := n06_fderiv_cube_apply hd (1, 0)
  have ht : angularPartial (fun q => d q ^ 3) p =
      3 * d p ^ 2 * angularPartial d p := n06_fderiv_cube_apply hd (0, 1)
  have hd₃ : DifferentiableAt ℝ (fun q => d q ^ 3) p := hd.pow 3
  have hca : DifferentiableAt ℝ (fun q => d q ^ 3 * A q) p := hd₃.mul hA
  have hcb : DifferentiableAt ℝ (fun q => d q ^ 3 * B q) p := hd₃.mul hB
  have hcc : DifferentiableAt ℝ (fun q => d q ^ 3 * C q) p := hd₃.mul hC
  change
    radialPartial (fun q => d q ^ 3 * A q * radialPartial u q +
      d q ^ 3 * B q * angularPartial u q) p +
    angularPartial (fun q => d q ^ 3 * B q * radialPartial u q +
      d q ^ 3 * C q * angularPartial u q) p = _
  rw [divergence_expansion_of_coefficients hca hcb hcc hu]
  rw [radialPartial_mul hd₃ hA, angularPartial_mul hd₃ hB,
    radialPartial_mul hd₃ hB, angularPartial_mul hd₃ hC]
  simp only [hr, ht, hdθ, zero_mul, mul_zero, zero_add]
  unfold n06CubicExpression
  ring

/-- The actual differential operator is controlled by the weighted degenerate graph density. -/
theorem n06CubicCoefficients_divergence_sq_le
    {d A B C u : PolarPoint → ℝ} {p : PolarPoint} {δ : ℝ}
    (hd : DifferentiableAt ℝ d p) (hA : DifferentiableAt ℝ A p)
    (hB : DifferentiableAt ℝ B p) (hC : DifferentiableAt ℝ C p)
    (hu : ContDiffAt ℝ 2 u p) (hdθ : angularPartial d p = 0)
    (hd₀ : 0 ≤ d p) (hd₁ : d p ≤ 1) (hdr : |radialPartial d p| ≤ 1) (hδ : 0 ≤ δ)
    (hA₀ : |A p| ≤ δ) (hB₀ : |B p| ≤ δ) (hC₀ : |C p| ≤ δ)
    (hAr : |radialPartial A p| ≤ δ) (hBt : |angularPartial B p| ≤ δ)
    (hBr : |radialPartial B p| ≤ δ) (hCt : |angularPartial C p| ≤ δ) :
    (divergenceOperator (n06CubicCoefficients d A B C) u p) ^ 2 ≤
      125 * δ ^ 2 *
        (d p ^ 4 * (radialPartial (radialPartial u) p) ^ 2 +
         d p ^ 5 * (angularPartial (radialPartial u) p) ^ 2 +
         d p ^ 6 * (angularPartial (angularPartial u) p) ^ 2 +
         d p ^ 2 * (radialPartial u p) ^ 2 + d p ^ 3 * (angularPartial u p) ^ 2) := by
  rw [n06CubicCoefficients_divergence hd hA hB hC hu hdθ]
  exact n06CubicExpression_sq_le _ _ _ _ _ hd₀ hd₁ hdr hδ hA₀ hB₀ hC₀ hAr hBt hBr hCt

/-- Subtraction of the true coefficient fields commutes with the differential operator. -/
theorem n06_divergenceOperator_sub {L L₀ : SymmetricCoefficients}
    {u : PolarPoint → ℝ} {p : PolarPoint}
    (ha : DifferentiableAt ℝ L.a p) (hb : DifferentiableAt ℝ L.b p)
    (hc : DifferentiableAt ℝ L.c p) (ha₀ : DifferentiableAt ℝ L₀.a p)
    (hb₀ : DifferentiableAt ℝ L₀.b p) (hc₀ : DifferentiableAt ℝ L₀.c p)
    (hu : ContDiffAt ℝ 2 u p) :
    divergenceOperator L u p - divergenceOperator L₀ u p =
      divergenceOperator
        { a := fun q => L.a q - L₀.a q
          b := fun q => L.b q - L₀.b q
          c := fun q => L.c q - L₀.c q } u p := by
  have hda : DifferentiableAt ℝ (fun q => L.a q - L₀.a q) p := ha.sub ha₀
  have hdb : DifferentiableAt ℝ (fun q => L.b q - L₀.b q) p := hb.sub hb₀
  have hdc : DifferentiableAt ℝ (fun q => L.c q - L₀.c q) p := hc.sub hc₀
  simp only [divergenceOperator]
  rw [divergence_expansion_of_coefficients ha hb hc hu,
    divergence_expansion_of_coefficients ha₀ hb₀ hc₀ hu,
    divergence_expansion_of_coefficients hda hdb hdc hu]
  rw [radialPartial_sub ha ha₀, angularPartial_sub hb hb₀,
    radialPartial_sub hb hb₀, angularPartial_sub hc hc₀]
  ring

/-- The value of a differential operator depends only on the germs of its coefficients. -/
theorem n06_divergenceOperator_congr_germ {L L' : SymmetricCoefficients}
    (u : PolarPoint → ℝ) {p : PolarPoint}
    (ha : L.a =ᶠ[𝓝 p] L'.a) (hb : L.b =ᶠ[𝓝 p] L'.b) (hc : L.c =ᶠ[𝓝 p] L'.c) :
    divergenceOperator L u p = divergenceOperator L' u p := by
  have hr : (fun q => L.a q * radialPartial u q + L.b q * angularPartial u q)
      =ᶠ[𝓝 p] (fun q => L'.a q * radialPartial u q + L'.b q * angularPartial u q) := by
    filter_upwards [ha, hb] with q hqa hqb
    rw [hqa, hqb]
  have ht : (fun q => L.b q * radialPartial u q + L.c q * angularPartial u q)
      =ᶠ[𝓝 p] (fun q => L'.b q * radialPartial u q + L'.c q * angularPartial u q) := by
    filter_upwards [hb, hc] with q hqb hqc
    rw [hqb, hqc]
  exact congrArg₂ (fun a b : ℝ => a + b)
    (congrArg (fun T : PolarPoint →L[ℝ] ℝ => T (1, 0)) (hr.fderiv_eq (𝕜 := ℝ)))
    (congrArg (fun T : PolarPoint →L[ℝ] ℝ => T (0, 1)) (ht.fderiv_eq (𝕜 := ℝ)))

/-- A cubic coefficient difference on a neighborhood gives the required graph-density bound
for the difference of the actual operators. -/
theorem n06_divergenceDifference_sq_le
    {L L₀ : SymmetricCoefficients} {d A B C u : PolarPoint → ℝ}
    {p : PolarPoint} {δ : ℝ}
    (ha : DifferentiableAt ℝ L.a p) (hb : DifferentiableAt ℝ L.b p)
    (hc : DifferentiableAt ℝ L.c p) (ha₀ : DifferentiableAt ℝ L₀.a p)
    (hb₀ : DifferentiableAt ℝ L₀.b p) (hc₀ : DifferentiableAt ℝ L₀.c p)
    (hd : DifferentiableAt ℝ d p) (hA : DifferentiableAt ℝ A p)
    (hB : DifferentiableAt ℝ B p) (hC : DifferentiableAt ℝ C p)
    (hu : ContDiffAt ℝ 2 u p)
    (heqa : (fun q => L.a q - L₀.a q) =ᶠ[𝓝 p] (fun q => d q ^ 3 * A q))
    (heqb : (fun q => L.b q - L₀.b q) =ᶠ[𝓝 p] (fun q => d q ^ 3 * B q))
    (heqc : (fun q => L.c q - L₀.c q) =ᶠ[𝓝 p] (fun q => d q ^ 3 * C q))
    (hdθ : angularPartial d p = 0) (hd₀ : 0 ≤ d p) (hd₁ : d p ≤ 1)
    (hdr : |radialPartial d p| ≤ 1) (hδ : 0 ≤ δ)
    (hA₀ : |A p| ≤ δ) (hB₀ : |B p| ≤ δ) (hC₀ : |C p| ≤ δ)
    (hAr : |radialPartial A p| ≤ δ) (hBt : |angularPartial B p| ≤ δ)
    (hBr : |radialPartial B p| ≤ δ) (hCt : |angularPartial C p| ≤ δ) :
    (divergenceOperator L u p - divergenceOperator L₀ u p) ^ 2 ≤
      125 * δ ^ 2 *
        (d p ^ 4 * (radialPartial (radialPartial u) p) ^ 2 +
         d p ^ 5 * (angularPartial (radialPartial u) p) ^ 2 +
         d p ^ 6 * (angularPartial (angularPartial u) p) ^ 2 +
         d p ^ 2 * (radialPartial u p) ^ 2 + d p ^ 3 * (angularPartial u p) ^ 2) := by
  rw [n06_divergenceOperator_sub ha hb hc ha₀ hb₀ hc₀ hu,
    n06_divergenceOperator_congr_germ u
      (L := { a := fun q => L.a q - L₀.a q
              b := fun q => L.b q - L₀.b q
              c := fun q => L.c q - L₀.c q })
      (L' := n06CubicCoefficients d A B C) heqa heqb heqc]
  exact n06CubicCoefficients_divergence_sq_le hd hA hB hC hu hdθ hd₀ hd₁ hdr hδ
    hA₀ hB₀ hC₀ hAr hBt hBr hCt

end ContinuousFlexibility.Statements
