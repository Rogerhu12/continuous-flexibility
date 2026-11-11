import ContinuousFlexibility.Radial.MorseChainParameters
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Morse travel integral between the actual turning points

The angle change of variables uses the positive quantity c + h cos θ.
The reciprocal integral is evaluated on two half intervals, so the
tangent substitution never meets its pole.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open scoped Interval

set_option backward.isDefEq.respectTransparency false

private theorem cos_affine_pos {c h : ℝ} (ha : 0 < c + h) (hb : 0 < c - h)
    (θ : ℝ) : 0 < c + h * cos θ := by
  by_cases hh : 0 ≤ h
  · have hm := mul_le_mul_of_nonneg_left (neg_one_le_cos θ) hh
    linarith only [hm, hb]
  · have hm := mul_le_mul_of_nonpos_left (cos_le_one θ) (le_of_not_ge hh)
    linarith only [hm, ha]

private theorem continuous_one_div_cos_affine {c h : ℝ}
    (ha : 0 < c + h) (hb : 0 < c - h) :
    Continuous (fun θ => 1 / (c + h * cos θ)) :=
  continuous_const.div₀ (continuous_const.add (continuous_const.mul Real.continuous_cos))
    (fun θ => (cos_affine_pos ha hb θ).ne')

private theorem half_angle_denominator (c h θ : ℝ) (hc : cos (θ / 2) ≠ 0) :
    (c + h + (c - h) * tan (θ / 2) ^ 2) * cos (θ / 2) ^ 2 = c + h * cos θ := by
  have hcos : cos θ = cos (θ / 2) ^ 2 - sin (θ / 2) ^ 2 := by
    have ht : 2 * (θ / 2) = θ := by ring
    have hh := Real.cos_two_mul (θ / 2)
    rw [ht] at hh
    linarith only [hh, Real.sin_sq_add_cos_sq (θ / 2)]
  rw [Real.tan_eq_sin_div_cos, div_pow]
  calc
    _ = (c + h) * cos (θ / 2) ^ 2 + (c - h) * sin (θ / 2) ^ 2 := by
      rw [add_mul, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hc)]
    _ = c * (sin (θ / 2) ^ 2 + cos (θ / 2) ^ 2) +
        h * (cos (θ / 2) ^ 2 - sin (θ / 2) ^ 2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one, ← hcos]

private theorem integral_cos_affine_half_angle {c h : ℝ}
    (ha : 0 < c + h) (hb : 0 < c - h) :
    (∫ θ in (0 : ℝ)..π / 2, 1 / (c + h * cos θ)) =
      ∫ t in (0 : ℝ)..1, 2 / (c + h + (c - h) * t ^ 2) := by
  let f : ℝ → ℝ := fun θ => tan (θ / 2)
  let f' : ℝ → ℝ := fun θ => 1 / cos (θ / 2) ^ 2 * (1 / 2)
  let g : ℝ → ℝ := fun t => 2 / (c + h + (c - h) * t ^ 2)
  have hhalf : 0 ≤ π / 2 := by positivity
  have hcos (θ : ℝ) (hθ : θ ∈ uIcc (0 : ℝ) (π / 2)) : 0 < cos (θ / 2) := by
    rw [uIcc_of_le hhalf] at hθ
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hd (θ : ℝ) (hθ : θ ∈ uIcc (0 : ℝ) (π / 2)) : HasDerivAt f (f' θ) θ := by
    have htan : HasDerivAt Real.tan (1 / cos (θ / 2) ^ 2) (θ / 2) :=
      Real.hasDerivAt_tan (hcos θ hθ).ne'
    have hlinear : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) θ := (hasDerivAt_id' θ).div_const 2
    simpa only [f, f', Function.comp_def] using htan.comp θ hlinear
  have hc : Continuous (fun θ : ℝ => cos (θ / 2) ^ 2) :=
    (Real.continuous_cos.comp (continuous_id.div_const 2)).pow 2
  have hd' : ContinuousOn f' (uIcc (0 : ℝ) (π / 2)) :=
    (continuousOn_const.div₀ hc.continuousOn
      (fun θ hθ => (pow_pos (hcos θ hθ) _).ne')).mul continuousOn_const
  have hgpos (t : ℝ) : 0 < c + h + (c - h) * t ^ 2 :=
    add_pos_of_pos_of_nonneg ha (mul_nonneg hb.le (sq_nonneg _))
  have hg : Continuous g :=
    continuous_const.div₀ (continuous_const.add (continuous_const.mul (continuous_id.pow 2)))
      (fun t => (hgpos t).ne')
  have hsub := intervalIntegral.integral_comp_mul_deriv (f := f) (f' := f') (g := g) hd hd' hg
  have hzero : f 0 = 0 := by simp [f]
  have hone : f (π / 2) = 1 := by
    change tan (π / 2 / 2) = 1
    rw [show π / 2 / 2 = π / 4 by ring, Real.tan_pi_div_four]
  change (∫ θ in (0 : ℝ)..π / 2, 1 / (c + h * cos θ)) =
    ∫ t in (0 : ℝ)..1, g t
  rw [hzero, hone] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro θ hθ
  have he := half_angle_denominator c h θ (hcos θ hθ).ne'
  change 1 / (c + h * cos θ) =
    2 / (c + h + (c - h) * tan (θ / 2) ^ 2) * (1 / cos (θ / 2) ^ 2 * (1 / 2))
  rw [← he]
  rw [← one_div_mul_one_div_rev]
  ring

private theorem integral_quadratic_reciprocal_unit {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in (0 : ℝ)..1, 2 / (a + b * t ^ 2)) =
      (2 / sqrt (a * b)) * arctan (sqrt (b / a)) := by
  let q := sqrt (b / a)
  have hq : 0 < q := sqrt_pos.mpr (div_pos hb ha)
  have hq₂ : q ^ 2 = b / a := sq_sqrt (div_nonneg hb.le ha.le)
  have hprod : a * q = sqrt (a * b) := by
    apply (sq_eq_sq₀ (mul_nonneg ha.le hq.le) (sqrt_nonneg _)).mp
    rw [mul_pow, hq₂, sq_sqrt (mul_nonneg ha.le hb.le)]
    calc
      _ = a * (a * (b / a)) := by ring
      _ = _ := by rw [mul_div_assoc', mul_div_cancel_left₀ _ ha.ne']
  let g : ℝ → ℝ := fun t => (1 + t ^ 2)⁻¹
  have hgden : Continuous (fun t : ℝ => 1 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hg : Continuous g :=
    hgden.inv₀ (fun t => (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg t)).ne')
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := (1 : ℝ))
    (f := fun t => q * t) (f' := fun _ => q) (g := g)
    (fun t _ => by simpa only [mul_one] using (hasDerivAt_id' t).const_mul q)
    continuousOn_const hg
  change (∫ t in (0 : ℝ)..1, g (q * t) * q) = ∫ t in q * 0..q * 1, g t at hsub
  rw [mul_zero, mul_one] at hsub
  rw [← hprod]
  change (∫ t in (0 : ℝ)..1, 2 / (a + b * t ^ 2)) = (2 / (a * q)) * arctan q
  have hatan : (∫ t in (0 : ℝ)..q, g t) = arctan q := by
    unfold g
    rw [integral_inv_one_add_sq, Real.arctan_zero, sub_zero]
  have hatan' : (∫ t in (0 : ℝ)..1, g (q * t) * q) = arctan q := hsub.trans hatan
  rw [← hatan']
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  have hden : a + b * t ^ 2 = a * (1 + (q * t) ^ 2) := by
    rw [mul_pow, hq₂, mul_add, mul_one, ← mul_assoc a (b / a),
      mul_div_assoc', mul_div_cancel_left₀ _ ha.ne']
  change 2 / (a + b * t ^ 2) = (2 / (a * q)) * (g (q * t) * q)
  rw [hden]
  let w := 1 + (q * t) ^ 2
  change 2 / (a * w) = (2 / (a * q)) * (w⁻¹ * q)
  calc
    _ = 2 * a⁻¹ * w⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = (2 * a⁻¹ * w⁻¹) * (q⁻¹ * q) := by rw [inv_mul_cancel₀ hq.ne', mul_one]
    _ = _ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The reciprocal of the positive affine cosine has the actual full
half-period integral, obtained by combining the two half-angle changes. -/
theorem integral_one_div_cos_affine {c h : ℝ} (ha : 0 < c + h) (hb : 0 < c - h) :
    (∫ θ in (0 : ℝ)..π, 1 / (c + h * cos θ)) = π / sqrt (c ^ 2 - h ^ 2) := by
  let f : ℝ → ℝ := fun θ => 1 / (c + h * cos θ)
  let fNeg : ℝ → ℝ := fun θ => 1 / (c + (-h) * cos θ)
  have hf : Continuous f := continuous_one_div_cos_affine ha hb
  have hma : 0 < c + (-h) := by linarith
  have hmb : 0 < c - (-h) := by linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (0 : ℝ) (π / 2)) (hf.intervalIntegrable (π / 2) π)
  have href := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := π / 2) f π
  rw [show π - π / 2 = π / 2 by ring, sub_zero] at href
  have hneg : (fun θ => f (π - θ)) = fNeg := by
    funext θ
    change 1 / (c + h * cos (π - θ)) = 1 / (c + (-h) * cos θ)
    rw [Real.cos_pi_sub, mul_neg, neg_mul]
  rw [hneg] at href
  change (∫ θ in (0 : ℝ)..π, f θ) = _
  rw [← hsplit, ← href]
  change (∫ θ in (0 : ℝ)..π / 2, 1 / (c + h * cos θ)) +
    (∫ θ in (0 : ℝ)..π / 2, 1 / (c + (-h) * cos θ)) = _
  rw [integral_cos_affine_half_angle ha hb, integral_cos_affine_half_angle hma hmb,
    integral_quadratic_reciprocal_unit ha hb, integral_quadratic_reciprocal_unit hma hmb]
  rw [show c + (-h) = c - h by ring, show c - (-h) = c + h by ring]
  rw [show (c + h) * (c - h) = c ^ 2 - h ^ 2 by ring,
    show (c - h) * (c + h) = c ^ 2 - h ^ 2 by ring]
  have hq : 0 < sqrt ((c - h) / (c + h)) := sqrt_pos.mpr (div_pos hb ha)
  have hqInv : sqrt ((c + h) / (c - h)) = (sqrt ((c - h) / (c + h)))⁻¹ := by
    rw [← Real.sqrt_inv, inv_div]
  rw [hqInv, Real.arctan_inv_of_pos hq]
  ring

private theorem integral_sin_sq_cos_affine {c h : ℝ}
    (ha : 0 < c + h) (hb : 0 < c - h) :
    (∫ θ in (0 : ℝ)..π, h ^ 2 * sin θ ^ 2 / (c + h * cos θ)) =
      π * (c - sqrt (c ^ 2 - h ^ 2)) := by
  have hpos : 0 < c ^ 2 - h ^ 2 := by
    calc
      0 < (c + h) * (c - h) := mul_pos ha hb
      _ = c ^ 2 - h ^ 2 := by ring
  have hfrac (θ : ℝ) :
      h ^ 2 * sin θ ^ 2 / (c + h * cos θ) =
        (c - h * cos θ) - (c ^ 2 - h ^ 2) * (1 / (c + h * cos θ)) := by
    have hd := (cos_affine_pos ha hb θ).ne'
    apply (div_eq_iff hd).mpr
    have htrig : h ^ 2 * sin θ ^ 2 = h ^ 2 - (h * cos θ) ^ 2 := by
      have he := congrArg (fun x : ℝ => h ^ 2 * x) (Real.sin_sq_add_cos_sq θ)
      nlinarith only [he]
    rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hd, mul_one, htrig]
    ring
  have hlin : Continuous (fun θ => c - h * cos θ) :=
    continuous_const.sub (continuous_const.mul Real.continuous_cos)
  have hrec : Continuous (fun θ => (c ^ 2 - h ^ 2) * (1 / (c + h * cos θ))) :=
    continuous_const.mul (continuous_one_div_cos_affine ha hb)
  have hlinInt : (∫ θ in (0 : ℝ)..π, c - h * cos θ) = π * c := by
    have hc : IntervalIntegrable (fun _ : ℝ => c) volume 0 π :=
      continuous_const.intervalIntegrable _ _
    have hcos : IntervalIntegrable (fun θ : ℝ => h * cos θ) volume 0 π :=
      (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hc hcos, intervalIntegral.integral_const_mul]
    simp [integral_cos, intervalIntegral.integral_const, smul_eq_mul]
  have hrecInt : (∫ θ in (0 : ℝ)..π, (c ^ 2 - h ^ 2) * (1 / (c + h * cos θ))) =
      π * sqrt (c ^ 2 - h ^ 2) := by
    rw [intervalIntegral.integral_const_mul, integral_one_div_cos_affine ha hb]
    calc
      _ = sqrt (c ^ 2 - h ^ 2) ^ 2 * (π / sqrt (c ^ 2 - h ^ 2)) := by
        rw [sq_sqrt hpos.le]
      _ = π * (sqrt (c ^ 2 - h ^ 2) * sqrt (c ^ 2 - h ^ 2) / sqrt (c ^ 2 - h ^ 2)) := by ring
      _ = _ := by rw [mul_div_cancel_right₀ _ (sqrt_pos.mpr hpos).ne']
  calc
    _ = ∫ θ in (0 : ℝ)..π, (c - h * cos θ) -
        (c ^ 2 - h ^ 2) * (1 / (c + h * cos θ)) :=
      intervalIntegral.integral_congr (fun θ _ => hfrac θ)
    _ = _ := by
      rw [intervalIntegral.integral_sub (hlin.intervalIntegrable _ _) (hrec.intervalIntegrable _ _),
        hlinInt, hrecInt]
      ring

/-- The actual travel integral of the positive Morse well between its
two logarithmic turning points. -/
theorem morseTravel_eq_pi_sqrt {A B : ℝ} (hB : 0 < B) (hAB : 4 * B < A) :
    Statements.morseTravel A B = π * (sqrt A / 2 - sqrt B) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  let c : ℝ := 1 / 2
  let h : ℝ := sqrt (1 - 4 * B / A) / 2
  have hh : 0 ≤ h := div_nonneg (sqrt_nonneg _) (by norm_num)
  have hleft : c + h = morseLeftRootT A B := by
    unfold c h morseLeftRootT
    ring
  have hright : c - h = morseRightRootT A B := by
    unfold c h morseRightRootT
    ring
  obtain ⟨hRpos, _, hLlo, _⟩ := morseRootT_bounds hB hAB
  have ha : 0 < c + h := by rw [hleft]; linarith only [hLlo]
  have hb : 0 < c - h := by rw [hright]; exact hRpos
  let f : ℝ → ℝ := fun θ => -log (c + h * cos θ)
  let f' : ℝ → ℝ := fun θ => h * sin θ / (c + h * cos θ)
  let g : ℝ → ℝ := fun x => sqrt (morseRho A B x)
  have hf (θ : ℝ) : HasDerivAt f (f' θ) θ := by
    have hD := (((Real.hasDerivAt_cos θ).const_mul h).const_add c).log
      (cos_affine_pos ha hb θ).ne'
    have he : -(h * (-sin θ) / (c + h * cos θ)) = f' θ := by
      unfold f'
      ring
    have hd := hD.neg
    change HasDerivAt f (-(h * (-sin θ) / (c + h * cos θ))) θ at hd
    rw [he] at hd
    exact hd
  have hf' : Continuous f' :=
    (continuous_const.mul Real.continuous_sin).div₀
      (continuous_const.add (continuous_const.mul Real.continuous_cos))
      (fun θ => (cos_affine_pos ha hb θ).ne')
  have hg : Continuous g := by
    unfold g morseRho
    fun_prop
  have h0 : f 0 = morseLeftTurn A B := by
    unfold f morseLeftTurn
    rw [Real.cos_zero, mul_one, hleft]
  have hπ : f π = morseRightTurn A B := by
    unfold f morseRightTurn
    rw [Real.cos_pi, mul_neg_one, ← sub_eq_add_neg, hright]
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := π)
    (f := f) (f' := f') (g := g) (fun θ _ => hf θ) hf'.continuousOn hg
  rw [h0, hπ] at hsub
  have hsqrt (θ : ℝ) (hθ : θ ∈ uIcc (0 : ℝ) π) :
      g (f θ) = sqrt A * (h * sin θ) := by
    have hx : exp (-f θ) = c + h * cos θ := by
      unfold f
      rw [neg_neg, Real.exp_log (cos_affine_pos ha hb θ)]
    have hρ : morseRho A B (f θ) = A * (h * sin θ) ^ 2 := by
      rw [morseRho_factor hB hAB, hx, ← hleft, ← hright]
      have hsin : 1 - cos θ ^ 2 = sin θ ^ 2 := by
        linarith only [Real.sin_sq_add_cos_sq θ]
      calc
        _ = A * (h ^ 2 * (1 - cos θ ^ 2)) := by ring
        _ = _ := by rw [hsin]; ring
    rw [uIcc_of_le Real.pi_pos.le] at hθ
    unfold g
    rw [hρ, Real.sqrt_mul hA.le, Real.sqrt_sq (mul_nonneg hh (Real.sin_nonneg_of_mem_Icc hθ))]
  have heval :
      Statements.morseTravel A B = sqrt A *
        (∫ θ in (0 : ℝ)..π, h ^ 2 * sin θ ^ 2 / (c + h * cos θ)) := by
    change (∫ x in morseLeftTurn A B..morseRightTurn A B, g x) = _
    rw [← hsub, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    change g (f θ) * f' θ = _
    rw [hsqrt θ hθ]
    unfold f'
    ring
  have hprod : c ^ 2 - h ^ 2 = B / A := by
    calc
      _ = (c - h) * (c + h) := by ring
      _ = _ := by rw [hright, hleft, morseRootT_mul hB hAB]
  have hsqrtBA : sqrt A * sqrt (B / A) = sqrt B := by
    rw [← Real.sqrt_mul hA.le, mul_div_assoc', mul_div_cancel_left₀ _ hA.ne']
  rw [heval, integral_sin_sq_cos_affine ha hb, hprod]
  calc
    _ = π * (sqrt A * c - sqrt A * sqrt (B / A)) := by ring
    _ = _ := by rw [hsqrtBA]; unfold c; ring

end ContinuousFlexibility.Radial
