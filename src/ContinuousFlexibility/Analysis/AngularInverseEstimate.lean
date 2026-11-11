import ContinuousFlexibility.Analysis.AngularCommutedEquation
import ContinuousFlexibility.Analysis.AngularGraphInterpolation

/-!
# Tame estimates for the angular inverse

The constant in the order-`p` estimate is an explicit function of `p`,
`a (p-1)`, `c 0`, and the norm of the inverse.  In particular, no
higher error coefficient is an argument of this constant.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ENNReal NNReal

/-- The coefficient before adjacent-order absorption. -/
def angularInversePreConstant (p : ℕ) (a czero b : ℝ) : ℝ :=
  (2 : ℝ) ^ p * (1 + b) * (1 + 2 * (p : ℝ) * (1 + a + czero))

/-- The final inverse constant, independent of all high-order errors. -/
def angularInverseTameConstant (p : ℕ) (a czero b : ℝ) : ℝ :=
  angularAbsorptionConstant (p - 1) (angularInversePreConstant p a czero b) b

theorem angularInversePreConstant_pos (p : ℕ) {a czero b : ℝ}
    (ha : 0 ≤ a) (hczero : 0 ≤ czero) (hb : 0 ≤ b) :
    0 < angularInversePreConstant p a czero b := by
  unfold angularInversePreConstant
  positivity

theorem angularInverseTameConstant_pos (p : ℕ) {a czero b : ℝ}
    (ha : 0 ≤ a) (hczero : 0 ≤ czero) (hb : 0 ≤ b) :
    0 < angularInverseTameConstant p a czero b :=
  angularAbsorptionConstant_pos _ (angularInversePreConstant_pos p ha hczero hb) hb

private theorem angularWeight_pow_le_frequency (p n : ℕ) :
    angularWeight n ^ p ≤ (2 : ℝ) ^ p * (1 + (n : ℝ) ^ p) := by
  by_cases hn : n = 0
  · subst n
    have hw : angularWeight 0 = 1 := by norm_num [angularWeight]
    have htwo : 1 ≤ (2 : ℝ) ^ p := by
      simpa only [pow_zero] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le p)
    rw [hw, one_pow]
    have hle : (1 : ℝ) ≤ 1 + (0 : ℝ) ^ p :=
      le_add_of_nonneg_right (pow_nonneg (by norm_num) p)
    have hmul : (2 : ℝ) ^ p ≤ (2 : ℝ) ^ p * (1 + (0 : ℝ) ^ p) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hle (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p)
    simpa only [Nat.cast_zero] using htwo.trans hmul
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hw : angularWeight n ≤ 2 * (n : ℝ) :=
      (angularWeight_le_one_add n).trans (by linarith)
    calc
      angularWeight n ^ p ≤ (2 * (n : ℝ)) ^ p :=
        pow_le_pow_left₀ (angularWeight_nonneg n) hw p
      _ = (2 : ℝ) ^ p * (n : ℝ) ^ p := mul_pow _ _ _
      _ ≤ (2 : ℝ) ^ p * (1 + (n : ℝ) ^ p) := by gcongr; linarith

section GeneralField

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace 𝕜 (E n)]

theorem memAngularWeight_frequencyPower {p : ℕ} {v : lp E 2}
    (hv : MemAngularSobolev (𝕜 := 𝕜) p v) :
    MemAngularWeight (𝕜 := 𝕜) (fun n => (n : ℝ) ^ p) v := by
  apply hv.mono
  intro n
  rw [abs_of_nonneg (pow_nonneg (Nat.cast_nonneg (α := ℝ) n) p),
    abs_of_nonneg (pow_nonneg (angularWeight_nonneg n) p)]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (natCast_le_angularWeight n) p

theorem angularWeightNorm_frequencyPower_eq {p : ℕ} {v : lp E 2}
    (hv : MemAngularSobolev (𝕜 := 𝕜) p v) :
    angularWeightNorm (𝕜 := 𝕜) (fun n => (n : ℝ) ^ p) v =
      ‖angularDerivativePower (𝕜 := 𝕜) p v‖ := by
  rw [← norm_angularMultiplierVector _ v (memAngularWeight_frequencyPower hv)]
  congr 1
  ext n
  rw [angularMultiplierVector_apply, angularDerivativePower_apply p v hv]

theorem angularSobolevNorm_le_base_derivativePower {p : ℕ} {v : lp E 2}
    (hv : MemAngularSobolev (𝕜 := 𝕜) p v) :
    angularSobolevNorm (𝕜 := 𝕜) p v ≤
      (2 : ℝ) ^ p * (‖v‖ + ‖angularDerivativePower (𝕜 := 𝕜) p v‖) := by
  have hfreq := memAngularWeight_frequencyPower hv
  have h := angularWeightNorm_le_add
    (memAngularWeight_const (𝕜 := 𝕜) ((2 : ℝ) ^ p) v)
    (hfreq.const_mul_weight ((2 : ℝ) ^ p))
    (w := fun n => angularWeight n ^ p) (fun n => by
      rw [abs_of_nonneg (pow_nonneg (angularWeight_nonneg n) p)]
      simpa only [mul_add, mul_one] using angularWeight_pow_le_frequency p n)
  rw [angularWeightNorm_const, angularWeightNorm_const_mul hfreq,
    abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p),
    angularWeightNorm_frequencyPower_eq hv] at h
  simpa only [angularSobolevNorm, mul_add] using h

end GeneralField

private theorem angular_inverse_preabsorb_scalar {t b h A F Y U : ℝ}
    (ht : 0 ≤ t) (hb : 0 ≤ b) (hh : 0 ≤ h) (hA : 1 ≤ A)
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hU : 0 ≤ U) :
    t * (U + b * (F + h * (2 * Y + A * U))) ≤
      t * (1 + b) * (1 + 2 * h) * (F + Y + A * U) := by
  let S : ℝ := F + Y + A * U
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hUS : U ≤ S := by
    have hAU := mul_le_mul_of_nonneg_right hA hU
    dsimp only [S]
    nlinarith only [hAU, hF, hY]
  have hFS : F ≤ S := by
    dsimp only [S]
    linarith only [hY, mul_nonneg hA0 hU]
  have htwo : 2 * Y + A * U ≤ 2 * S := by
    dsimp only [S]
    nlinarith only [hF, mul_nonneg hA0 hU]
  have hprincipal : F + h * (2 * Y + A * U) ≤ (1 + 2 * h) * S := by
    calc
      _ ≤ S + h * (2 * S) := add_le_add hFS (mul_le_mul_of_nonneg_left htwo hh)
      _ = (1 + 2 * h) * S := by ring
  have hS' : S ≤ (1 + 2 * h) * S := by nlinarith only [mul_nonneg hh hS]
  calc
    _ ≤ t * ((1 + 2 * h) * S + b * ((1 + 2 * h) * S)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hUS.trans hS')
        (mul_le_mul_of_nonneg_left hprincipal hb)) ht
    _ = t * (1 + b) * (1 + 2 * h) * (F + Y + A * U) := by dsimp only [S]; ring

section ComplexField

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)]

/-- Every summand in the order-`m+1` commuted equation has the same tame
bound. The large coefficient `c` occurs linearly after weighted Young. -/
theorem angular_commutator_term_bound (K : lp E 2 →L[ℂ] lp E 2)
    {m k : ℕ} (hk : k ≤ m) {a c czero : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hczero : 0 ≤ czero)
    (hzero : ‖K‖ ≤ a + czero)
    (hone : ∀ v : lp E 2, MemAngularSobolev (𝕜 := ℂ) m v →
      MemAngularSobolev (𝕜 := ℂ) m (K v) ∧
      angularSobolevNorm (𝕜 := ℂ) m (K v) ≤
        a * angularSobolevNorm (𝕜 := ℂ) m v + c * ‖v‖)
    (u : lp E 2) (hu : MemAngularSobolev (𝕜 := ℂ) m u) :
    ‖angularDerivativePower (𝕜 := ℂ) k
        (K (angularDerivativePower (𝕜 := ℂ) (m - k) u))‖ ≤
      (1 + a + czero) * (2 * angularSobolevNorm (𝕜 := ℂ) m u + (1 + c) * ‖u‖) := by
  have hC : 0 ≤ 1 + a + czero := by positivity
  have hA : 0 ≤ 1 + c := by positivity
  by_cases hm : m = 0
  · subst m
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    simp only [Nat.sub_zero, angularDerivativePower_zero, angularSobolevNorm_zero]
    calc
      ‖K u‖ ≤ (a + czero) * ‖u‖ := K.le_of_opNorm_le hzero u
      _ ≤ (1 + a + czero) * ‖u‖ := by gcongr; linarith
      _ ≤ (1 + a + czero) * (2 * ‖u‖ + (1 + c) * ‖u‖) := by
        apply mul_le_mul_of_nonneg_left _ hC
        nlinarith only [norm_nonneg u, mul_nonneg hA (norm_nonneg u)]
  · have hm' : 0 < m := Nat.pos_of_ne_zero hm
    have hsum : k + (m - k) = m := by omega
    have hu' : MemAngularSobolev (𝕜 := ℂ) (k + (m - k)) u := by simpa only [hsum] using hu
    have hv : MemAngularSobolev (𝕜 := ℂ) k (angularDerivativePower (𝕜 := ℂ) (m - k) u) :=
      hu'.derivative_power
    obtain ⟨hKv, hbound⟩ := angular_sobolev_interpolation K hm' ha hc hczero hzero hone hk _ hv
    have hprincipal : angularSobolevNorm (𝕜 := ℂ) k (angularDerivativePower (𝕜 := ℂ) (m - k) u) ≤
        angularSobolevNorm (𝕜 := ℂ) m u := by
      simpa only [hsum] using angularSobolevNorm_derivativePower_le k (m - k) hu'
    have hnorm : ‖angularDerivativePower (𝕜 := ℂ) (m - k) u‖ ≤
        angularSobolevNorm (𝕜 := ℂ) (m - k) u :=
      norm_angularDerivativePower_le _ (hu.of_le (Nat.sub_le _ _))
    have hmixed : (1 + c) ^ ((k : ℝ) / m) *
        ‖angularDerivativePower (𝕜 := ℂ) (m - k) u‖ ≤
        angularSobolevNorm (𝕜 := ℂ) m u + (1 + c) * ‖u‖ :=
      (mul_le_mul_of_nonneg_left hnorm (Real.rpow_nonneg hA _)).trans
        (angularWeightNorm_mixed hu hm' hk hA)
    calc
      _ ≤ angularSobolevNorm (𝕜 := ℂ) k (K (angularDerivativePower (𝕜 := ℂ) (m - k) u)) :=
        norm_angularDerivativePower_le k hKv
      _ ≤ (1 + a + czero) *
          (angularSobolevNorm (𝕜 := ℂ) k (angularDerivativePower (𝕜 := ℂ) (m - k) u) +
            (1 + c) ^ ((k : ℝ) / m) * ‖angularDerivativePower (𝕜 := ℂ) (m - k) u‖) := hbound
      _ ≤ (1 + a + czero) *
          (angularSobolevNorm (𝕜 := ℂ) m u +
            (angularSobolevNorm (𝕜 := ℂ) m u + (1 + c) * ‖u‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add hprincipal hmixed) hC
      _ = (1 + a + czero) * (2 * angularSobolevNorm (𝕜 := ℂ) m u + (1 + c) * ‖u‖) := by ring

/-- The angular commutator inverse lemma on a complex Hilbert spectral
sum.  Spectral summands may have arbitrary dimensions.  The displayed
constant depends only on the permitted low-order data. -/
theorem angular_inverse_tame_complex (R K B : lp E 2 →L[ℂ] lp E 2)
    (a c : ℕ → ℝ≥0) (ha : Monotone a) (_hc : Monotone c)
    (hR : ∀ p v, MemAngularSobolev (𝕜 := ℂ) p v →
      MemAngularSobolev (𝕜 := ℂ) p (R v))
    (hK : ∀ p v, MemAngularSobolev (𝕜 := ℂ) p v →
      MemAngularSobolev (𝕜 := ℂ) p (K v))
    (hbound : ∀ p v, MemAngularSobolev (𝕜 := ℂ) p v →
      angularSobolevNorm (𝕜 := ℂ) p (K v) ≤
        (a p : ℝ) * angularSobolevNorm (𝕜 := ℂ) p v + (c p : ℝ) * ‖v‖)
    (hcomm : ∀ v, v ∈ angularFrequencyDomain (𝕜 := ℂ) →
      angularDerivative (𝕜 := ℂ) (R v) = R (angularDerivative (𝕜 := ℂ) v) + K v)
    (hleft : ∀ v, B (v + R v) = v)
    (hright : ∀ f, B f + R (B f) = f) :
    (∀ p f, MemAngularSobolev (𝕜 := ℂ) p f →
      MemAngularSobolev (𝕜 := ℂ) p (B f)) ∧
    (∀ p, 1 ≤ p → ∀ f, MemAngularSobolev (𝕜 := ℂ) p f →
      angularSobolevNorm (𝕜 := ℂ) p (B f) ≤
        angularInverseTameConstant p (a (p - 1)) (c 0) ‖B‖ *
          (angularSobolevNorm (𝕜 := ℂ) p f + (1 + (c (p - 1) : ℝ)) * ‖f‖)) := by
  have hRdom : ∀ v, v ∈ angularFrequencyDomain (𝕜 := ℂ) →
      R v ∈ angularFrequencyDomain (𝕜 := ℂ) := by
    intro v hv
    exact (memAngularSobolev_one_iff_frequency _).mp
      (hR 1 v ((memAngularSobolev_one_iff_frequency _).mpr hv))
  have hreg := angularInverse_preserves_sobolev R K B hRdom hK hcomm hleft hright
  refine ⟨hreg, ?_⟩
  have hKzero : ‖K‖ ≤ (a 0 : ℝ) + (c 0 : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    simpa only [angularSobolevNorm_zero, add_mul] using hbound 0 v (memAngularSobolev_zero v)
  intro p hp f hf
  let m : ℕ := p - 1
  let u : lp E 2 := B f
  let C : ℝ := 1 + (a m : ℝ) + (c 0 : ℝ)
  let A : ℝ := 1 + (c m : ℝ)
  let X : ℝ := angularSobolevNorm (𝕜 := ℂ) p u
  let Y : ℝ := angularSobolevNorm (𝕜 := ℂ) m u
  let U : ℝ := ‖u‖
  let F : ℝ := angularSobolevNorm (𝕜 := ℂ) p f
  let D : ℝ := angularInversePreConstant p (a m) (c 0) ‖B‖
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hA : 1 ≤ A := le_add_of_nonneg_right (c m).coe_nonneg
  have hD : 0 < D := angularInversePreConstant_pos p (a m).coe_nonneg (c 0).coe_nonneg (norm_nonneg B)
  have hu : MemAngularSobolev (𝕜 := ℂ) p u := hreg p f hf
  have hum : MemAngularSobolev (𝕜 := ℂ) m u := hu.of_le (Nat.sub_le _ _)
  have ha0 : (a 0 : ℝ) ≤ (a m : ℝ) := by exact_mod_cast ha (Nat.zero_le m)
  have hzero : ‖K‖ ≤ (a m : ℝ) + (c 0 : ℝ) :=
    hKzero.trans (add_le_add ha0 le_rfl)
  let T : lp E 2 := ∑ k ∈ Finset.range p,
    angularDerivativePower (𝕜 := ℂ) k (K (angularDerivativePower (𝕜 := ℂ) (m - k) u))
  have hterm (k : ℕ) (hk : k ∈ Finset.range p) :
      ‖angularDerivativePower (𝕜 := ℂ) k (K (angularDerivativePower (𝕜 := ℂ) (m - k) u))‖ ≤
        C * (2 * Y + A * U) := by
    have hkm : k ≤ m := by have := Finset.mem_range.mp hk; dsimp only [m]; omega
    exact angular_commutator_term_bound K hkm (a m).coe_nonneg (c m).coe_nonneg
      (c 0).coe_nonneg hzero (fun v hv => ⟨hK m v hv, hbound m v hv⟩) u hum
  have hsum : ‖T‖ ≤ (p : ℝ) * C * (2 * Y + A * U) := by
    calc
      ‖T‖ ≤ ∑ k ∈ Finset.range p,
          ‖angularDerivativePower (𝕜 := ℂ) k (K (angularDerivativePower (𝕜 := ℂ) (m - k) u))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range p, C * (2 * Y + A * U) := Finset.sum_le_sum hterm
      _ = (p : ℝ) * C * (2 * Y + A * U) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  have heq : angularDerivativePower (𝕜 := ℂ) p u =
      B (angularDerivativePower (𝕜 := ℂ) p f - T) := by
    calc
      _ = B (angularDerivativePower (𝕜 := ℂ) p u + R (angularDerivativePower (𝕜 := ℂ) p u)) := (hleft _).symm
      _ = B (angularDerivativePower (𝕜 := ℂ) p f - T) := congrArg B
        (angularInverse_commuted_equation R K B hR hK hcomm hleft hright p f hf)
  have hpower : ‖angularDerivativePower (𝕜 := ℂ) p u‖ ≤
      ‖B‖ * (F + (p : ℝ) * C * (2 * Y + A * U)) := by
    rw [heq]
    apply (B.le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
    exact (norm_sub_le _ _).trans (add_le_add (norm_angularDerivativePower_le p hf) hsum)
  have hequation : X ≤ D * (F + Y + A * U) := by
    calc
      X ≤ (2 : ℝ) ^ p * (U + ‖angularDerivativePower (𝕜 := ℂ) p u‖) :=
        angularSobolevNorm_le_base_derivativePower hu
      _ ≤ (2 : ℝ) ^ p * (U + ‖B‖ * (F + (p : ℝ) * C * (2 * Y + A * U))) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hpower U) (by positivity)
      _ ≤ D * (F + Y + A * U) := by
        simpa only [D, angularInversePreConstant, C, mul_assoc] using
          angular_inverse_preabsorb_scalar (t := (2 : ℝ) ^ p) (b := ‖B‖)
            (h := (p : ℝ) * C) (A := A) (F := F) (Y := Y) (U := U)
            (by positivity) (norm_nonneg B) (mul_nonneg (Nat.cast_nonneg p) hC) hA
            (angularSobolevNorm_nonneg (𝕜 := ℂ) p f)
            (angularSobolevNorm_nonneg (𝕜 := ℂ) m u) (norm_nonneg u)
  have hmp : m + 1 = p := by dsimp only [m]; omega
  have hu' : MemAngularSobolev (𝕜 := ℂ) (m + 1) u := by simpa only [hmp] using hu
  have hinterpolate : Y ≤ (2 * D)⁻¹ * X + (2 * D) ^ m * U := by
    simpa only [inv_inv, hmp] using
      angularSobolevNorm_adjacent hu' (epsilon := (2 * D)⁻¹) (by positivity)
  exact angular_absorb_lower_order m hD (norm_nonneg B) hA (norm_nonneg u)
    (angularSobolevNorm_nonneg (𝕜 := ℂ) p f) (norm_nonneg f) (B.le_opNorm f) hinterpolate hequation

end ComplexField

end ContinuousFlexibility.Analysis
