import ContinuousFlexibility.Radial.OuterRealizedCellEnergy

/-!
# Energy estimates at every point of a transition piece

The positive piece uses one regularized weight for the whole interval.
The negative piece keeps its full weighted energy until the last step.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory

theorem outer_abs_integral_le_whole {f : ℝ → ℝ} {l r s t : ℝ}
    (hlr : l ≤ r) (hf : ContinuousOn f (Icc l r))
    (hf₀ : ∀ x ∈ Icc l r, 0 ≤ f x) (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    |∫ x in s..t, f x| ≤ ∫ x in l..r, f x := by
  have hae : 0 ≤ᵐ[volume.restrict (Ioc l r)] f :=
    (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall (fun x hx => hf₀ x ⟨hx.1.le, hx.2⟩))
  have hi := hf.intervalIntegrable_of_Icc hlr
  rcases le_total s t with hst | hts
  · have hpos : 0 ≤ ∫ x in s..t, f x :=
      intervalIntegral.integral_nonneg hst (fun x hx => hf₀ x ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩)
    rw [abs_of_nonneg hpos]
    exact intervalIntegral.integral_mono_interval hs.1 hst ht.2 hae hi
  · have hpos : 0 ≤ ∫ x in t..s, f x :=
      intervalIntegral.integral_nonneg hts (fun x hx => hf₀ x ⟨ht.1.trans hx.1, hx.2.trans hs.2⟩)
    rw [intervalIntegral.integral_symm t s, abs_neg, abs_of_nonneg hpos]
    exact intervalIntegral.integral_mono_interval ht.1 hts hs.2 hae hi

theorem transfer_positive_piece_regularized_on {u z α β : ℝ → ℝ} {l r s t : ℝ}
    (hlr : l ≤ r) (hα : ContinuousOn α (Icc l r)) (hβ : ContinuousOn β (Icc l r))
    (hα₀ : ∀ x ∈ Icc l r, 0 ≤ α x) (hβ₀ : ∀ x ∈ Icc l r, 0 ≤ β x)
    (hd : ∀ x ∈ Icc l r,
      HasDerivAt u (α x * z x) x ∧ HasDerivAt z (β x * u x) x)
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    let a := ∫ x in l..r, α x
    let b := ∫ x in l..r, β x
    u t ^ 2 + z t ^ 2 ≤ (u s ^ 2 + z s ^ 2) *
      ((1 + a + b) ^ 4 * exp (2 * sqrt (a * b) + 2)) := by
  let a := ∫ x in l..r, α x
  let b := ∫ x in l..r, β x
  have ha : 0 ≤ a := intervalIntegral.integral_nonneg hlr hα₀
  have hb : 0 ≤ b := intervalIntegral.integral_nonneg hlr hβ₀
  have hM : 1 ≤ 1 + a + b := by linarith only [ha, hb]
  obtain ⟨μ, hμ, hμhi, hμlo, hbound⟩ := exists_regularized_positive_weight ha hb
  have hαi : IntervalIntegrable (fun x => α x / μ) volume l r :=
    (hα.div_const μ).intervalIntegrable_of_Icc hlr
  have hβi : IntervalIntegrable (fun x => μ * β x) volume l r :=
    (continuousOn_const.mul hβ).intervalIntegrable_of_Icc hlr
  have hκ : ContinuousOn (fun x => α x / μ + μ * β x) (Icc l r) :=
    (hα.div_const μ).add (continuousOn_const.mul hβ)
  have hκ₀ (x : ℝ) (hx : x ∈ Icc l r) : 0 ≤ α x / μ + μ * β x :=
    add_nonneg (div_nonneg (hα₀ x hx) hμ.le) (mul_nonneg hμ.le (hβ₀ x hx))
  have hI : (∫ x in l..r, α x / μ + μ * β x) = a / μ + μ * b := by
    rw [intervalIntegral.integral_add hαi hβi, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul]
  have hfull := outer_abs_integral_le_whole hlr hκ hκ₀ hs ht
  rw [hI] at hfull
  have htransfer := transfer_positive_piece hlr hμ hα hβ hα₀ hβ₀ hd hs ht
  have hweighted :
      u t ^ 2 + μ ^ 2 * z t ^ 2 ≤
        (u s ^ 2 + μ ^ 2 * z s ^ 2) * exp (2 * sqrt (a * b) + 2) :=
    htransfer.trans (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (hfull.trans hbound)) (by positivity))
  simpa only [mul_assoc] using
    state_energy_rescale_transfer hM hμhi hμlo (exp_pos _).le hweighted

/-- Two adjacent intervals with pointwise transfer bounds have the product
bound on their union, in either orientation and at every interior point. -/
theorem energy_transfer_join {E : ℝ → ℝ} {a b c F G : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hF : 1 ≤ F) (hG : 1 ≤ G)
    (hE : ∀ x ∈ Icc a c, 0 ≤ E x)
    (hleft : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, E t ≤ E s * F)
    (hright : ∀ s ∈ Icc b c, ∀ t ∈ Icc b c, E t ≤ E s * G)
    {s t : ℝ} (hs : s ∈ Icc a c) (ht : t ∈ Icc a c) :
    E t ≤ E s * (F * G) := by
  have hF₀ : 0 ≤ F := zero_le_one.trans hF
  have hG₀ : 0 ≤ G := zero_le_one.trans hG
  by_cases hsb : s ≤ b
  · by_cases htb : t ≤ b
    · calc
        _ ≤ E s * F := hleft s ⟨hs.1, hsb⟩ t ⟨ht.1, htb⟩
        _ ≤ (E s * F) * G := le_mul_of_one_le_right (mul_nonneg (hE s hs) hF₀) hG
        _ = _ := mul_assoc _ _ _
    · calc
        _ ≤ E b * G := hright b ⟨le_rfl, hbc⟩ t ⟨(lt_of_not_ge htb).le, ht.2⟩
        _ ≤ (E s * F) * G :=
          mul_le_mul_of_nonneg_right (hleft s ⟨hs.1, hsb⟩ b ⟨hab, le_rfl⟩) hG₀
        _ = _ := mul_assoc _ _ _
  · by_cases htb : t ≤ b
    · calc
        _ ≤ E b * F := hleft b ⟨hab, le_rfl⟩ t ⟨ht.1, htb⟩
        _ ≤ (E s * G) * F :=
          mul_le_mul_of_nonneg_right (hright s ⟨(lt_of_not_ge hsb).le, hs.2⟩ b ⟨le_rfl, hbc⟩) hF₀
        _ = _ := by ring
    · calc
        _ ≤ E s * G := hright s ⟨(lt_of_not_ge hsb).le, hs.2⟩ t ⟨(lt_of_not_ge htb).le, ht.2⟩
        _ ≤ (E s * G) * F := le_mul_of_one_le_right (mul_nonneg (hE s hs) hG₀) hF
        _ = _ := by ring

/-- Keeping the negative weighted energy gives the same exponential
factor at interior points, with one coefficient-size prefactor. -/
theorem morse_negative_energy_on {A B j s t : ℝ} (hB : 0 < B)
    (hAB : 4 * B < A) {u v : ℝ → ℝ}
    (hu : ∀ x ∈ Icc (morseLeftTurn A B) (morseRightTurn A B), HasDerivAt u (v x) x)
    (hv : ∀ x ∈ Icc (morseLeftTurn A B) (morseRightTurn A B),
      HasDerivAt v (-(j ^ 2 * morseRho A B x * u x)) x)
    (hs : s ∈ Icc (morseLeftTurn A B) (morseRightTurn A B))
    (ht : t ∈ Icc (morseLeftTurn A B) (morseRightTurn A B)) :
    u t ^ 2 + v t ^ 2 ≤ (u s ^ 2 + v s ^ 2) *
      ((1 + j ^ 2 * (A / 4 - B)) * morseNegativeEnergyFactor A B j) := by
  let l := morseLeftTurn A B
  let r := morseRightTurn A B
  let q : ℝ → ℝ := fun x => j ^ 2 * |A * (exp (-x) * (2 * exp (-x) - 1))| /
    (1 + j ^ 2 * morseRho A B x)
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hlr : l ≤ r := (morseTurn_order hB hAB).le
  have hρ₀ : ∀ x ∈ Icc l r, 0 ≤ morseRho A B x :=
    fun _ hx => morseRho_nonneg_between_turns hB hAB hx
  have hdc : Continuous (fun x : ℝ => A * (exp (-x) * (2 * exp (-x) - 1))) := by fun_prop
  have hqc : ContinuousOn q (Icc l r) :=
    continuousOn_ratio
      (continuousOn_of_hasDerivAt' (fun x _ => hasDerivAt_morseRho A B x)) hρ₀
      (continuous_abs.comp_continuousOn hdc.continuousOn)
  have hq₀ (x : ℝ) (hx : x ∈ Icc l r) : 0 ≤ q x :=
    div_nonneg (mul_nonneg (sq_nonneg j) (abs_nonneg _))
      (add_nonneg zero_le_one (mul_nonneg (sq_nonneg j) (hρ₀ x hx)))
  have hI : (∫ x in l..r, 1 + q x) ≤ r - l + 2 * log (1 + j ^ 2 * (A / 4 - B)) := by
    rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable l r)
      (hqc.intervalIntegrable_of_Icc hlr), intervalIntegral.integral_const, smul_eq_mul, mul_one]
    exact add_le_add le_rfl (morse_negative_integral_log_le hB hAB j)
  have hsub := outer_abs_integral_le_whole hlr (continuousOn_const.add hqc)
    (fun x hx => add_nonneg zero_le_one (hq₀ x hx)) hs ht
  have hweighted := negative_energy_transfer hlr hu hv
    (fun x _ => hasDerivAt_morseRho A B x) hρ₀ hdc.continuousOn hs ht
  have hlow : u t ^ 2 + v t ^ 2 ≤ v t ^ 2 + (1 + j ^ 2 * morseRho A B t) * u t ^ 2 := by
    have hp := mul_nonneg (mul_nonneg (sq_nonneg j) (hρ₀ t ht)) (sq_nonneg (u t))
    nlinarith only [hp]
  have hupp : v s ^ 2 + (1 + j ^ 2 * morseRho A B s) * u s ^ 2 ≤
      (u s ^ 2 + v s ^ 2) * (1 + j ^ 2 * (A / 4 - B)) := by
    have hp := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (morseRho_le_peak hA.le B s) (sq_nonneg j)) (sq_nonneg (u s))
    have hpeak : 0 ≤ A / 4 - B := by linarith only [hAB]
    have hvp := mul_nonneg (mul_nonneg (sq_nonneg j) hpeak) (sq_nonneg (v s))
    nlinarith only [hp, hvp]
  calc
    _ ≤ v t ^ 2 + (1 + j ^ 2 * morseRho A B t) * u t ^ 2 := hlow
    _ ≤ (v s ^ 2 + (1 + j ^ 2 * morseRho A B s) * u s ^ 2) *
        exp |∫ x in s..t, 1 + q x| := hweighted
    _ ≤ ((u s ^ 2 + v s ^ 2) * (1 + j ^ 2 * (A / 4 - B))) *
        exp (r - l + 2 * log (1 + j ^ 2 * (A / 4 - B))) :=
      mul_le_mul hupp (exp_le_exp.mpr (hsub.trans hI)) (exp_pos _).le
        (by have hp : 0 ≤ A / 4 - B := by linarith only [hAB]; positivity)
    _ = _ := by dsimp only [morseNegativeEnergyFactor, l, r]; ring

end ContinuousFlexibility.Radial
