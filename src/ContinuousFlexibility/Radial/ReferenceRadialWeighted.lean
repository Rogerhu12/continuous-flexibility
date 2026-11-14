module

public import ContinuousFlexibility.Radial.R11bGlobalL2

/-!
# Scalar radial weighted L² fields

These are the actual one-dimensional coefficient norms obtained by angular
projection. The coefficient exponent is written directly as A, without the
factor 2 used in the source/output conventions. No parity, boundary value,
or equation is built into this norm predicate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter Real
open ContinuousFlexibility.Statements

def ReferenceRadialWeighted (D : ReferenceData) (γ A : ℝ) (u : ℝ → ℝ) : Prop :=
  (∀ m, MemLp (fun r => D.localizer m r * u r) 2 (volume.restrict (radialCore D))) ∧
    Summable (fun m => exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
      ∫ r, (D.localizer m r * u r) ^ 2 ∂volume.restrict (radialCore D))

theorem ReferenceRadialWeighted.congr_ae {D : ReferenceData} {γ A : ℝ}
    {u v : ℝ → ℝ} (hu : ReferenceRadialWeighted D γ A u)
    (he : u =ᵐ[volume.restrict (radialCore D)] v) :
    ReferenceRadialWeighted D γ A v := by
  have hl (m : ℕ) : (fun r => D.localizer m r * u r) =ᵐ[volume.restrict (radialCore D)]
      (fun r => D.localizer m r * v r) := he.mono fun r hr => congrArg _ hr
  refine ⟨fun m => (memLp_congr_ae (hl m)).mp (hu.1 m), ?_⟩
  apply hu.2.congr
  intro m
  congr 1
  exact integral_congr_ae ((hl m).mono fun r hr => congrArg (fun x : ℝ => x ^ 2) hr)

theorem ReferenceRadialWeighted.memLp {D : ReferenceData} (hpart : RadialPartition D)
    {γ A : ℝ} (hγ : 0 < γ) {u : ℝ → ℝ}
    (hu : ReferenceRadialWeighted D γ A u) :
    MemLp u 2 (volume.restrict (radialCore D)) := by
  obtain ⟨B, hB⟩ := hpart.2.2.2.2.2
  obtain ⟨K, _, hweight⟩ := r11b_exp_weight_le 0 A 0 γ hγ
  have hweight' (m : ℕ) : (1 : ℝ) ≤ K *
      exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) := by
    simpa only [zero_mul, mul_zero, zero_add, exp_zero] using hweight (D.cellIndex m)
  obtain ⟨hs, _⟩ := r11b_weighted_tsum_le (fun _ => 1)
    (fun m => exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)))
    (fun m => ∫ r, (D.localizer m r * u r) ^ 2 ∂volume.restrict (radialCore D))
    (fun _ => zero_le_one) (fun _ => integral_nonneg fun _ => sq_nonneg _) hweight' hu.2
  simp only [one_mul] at hs
  have hsum : ∀ᵐ r ∂volume.restrict (radialCore D), (∑' m, D.localizer m r) = 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (hpart.2.2.2.2.1 r hr).2
  exact (r11b_memLp_of_localized_square_summable D.localizer u hu.1
    (Eventually.of_forall fun r => (hB r).1)
    (Eventually.of_forall fun r => (hB r).2) hsum hs).1

theorem ReferenceRadialWeighted.add {D : ReferenceData} {γ A : ℝ}
    {u v : ℝ → ℝ} (hu : ReferenceRadialWeighted D γ A u)
    (hv : ReferenceRadialWeighted D γ A v) :
    ReferenceRadialWeighted D γ A (fun r => u r + v r) := by
  have hl (m : ℕ) : MemLp (fun r => D.localizer m r * (u r + v r)) 2
      (volume.restrict (radialCore D)) := by
    have h := (hu.1 m).add (hv.1 m)
    change MemLp (fun r => D.localizer m r * u r + D.localizer m r * v r) 2
      (volume.restrict (radialCore D)) at h
    simpa only [mul_add] using h
  refine ⟨hl, ?_⟩
  apply ((hu.2.add hv.2).mul_left 2).of_nonneg_of_le
    (fun m => mul_nonneg (exp_pos _).le (integral_nonneg fun r => sq_nonneg _))
  intro m
  have hb : (∫ r, (D.localizer m r * (u r + v r)) ^ 2 ∂volume.restrict (radialCore D)) ≤
      2 * ((∫ r, (D.localizer m r * u r) ^ 2 ∂volume.restrict (radialCore D)) +
        ∫ r, (D.localizer m r * v r) ^ 2 ∂volume.restrict (radialCore D)) := by
    calc
      _ ≤ ∫ r, 2 * ((D.localizer m r * u r) ^ 2 + (D.localizer m r * v r) ^ 2)
          ∂volume.restrict (radialCore D) := by
        apply integral_mono (hl m).integrable_sq
          (((hu.1 m).integrable_sq.add (hv.1 m).integrable_sq).const_mul 2)
        intro r
        change (D.localizer m r * (u r + v r)) ^ 2 ≤
          2 * ((D.localizer m r * u r) ^ 2 + (D.localizer m r * v r) ^ 2)
        nlinarith only [sq_nonneg (D.localizer m r * u r - D.localizer m r * v r)]
      _ = _ := by rw [integral_const_mul, integral_add (hu.1 m).integrable_sq
        (hv.1 m).integrable_sq]
  have hm := mul_le_mul_of_nonneg_left hb
    (exp_pos (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m))).le
  nlinarith only [hm]

/-- Multiplication by a cellwise coefficient power costs any prescribed
strict attenuation margin. All measurability is retained explicitly. -/
theorem ReferenceRadialWeighted.mul_coefficient {D : ReferenceData}
    (hpart : RadialPartition D) {γlo γhi Ahi : ℝ} (Alo : ℝ)
    (hγ : γlo < γhi) {u k : ℝ → ℝ}
    (hu : ReferenceRadialWeighted D γhi Ahi u)
    (hk : AEStronglyMeasurable k (volume.restrict (radialCore D)))
    {C B : ℝ} (hC : 0 ≤ C)
    (hb : ∀ m r, r ∈ D.cells m → |k r| ≤ C * exp (B * radialQ (D.cellIndex m))) :
    ReferenceRadialWeighted D γlo Alo (fun r => k r * u r) := by
  let L (m : ℕ) : ℝ := C * exp (B * radialQ (D.cellIndex m))
  have hL (m : ℕ) : 0 ≤ L m := mul_nonneg hC (exp_pos _).le
  have hpoint (m : ℕ) (r : ℝ) :
      |D.localizer m r * (k r * u r)| ≤ L m * |D.localizer m r * u r| := by
    by_cases hz : D.localizer m r = 0
    · simp only [hz, zero_mul, abs_zero, mul_zero, le_refl]
    · have hkr := hb m r (hpart.2.2.1 m hz)
      calc
        _ = |k r| * |D.localizer m r * u r| := by
          rw [← abs_mul]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hkr (abs_nonneg _)
  have hl (m : ℕ) : MemLp (fun r => D.localizer m r * (k r * u r)) 2
      (volume.restrict (radialCore D)) := by
    have hm : AEStronglyMeasurable (fun r => D.localizer m r * (k r * u r))
        (volume.restrict (radialCore D)) := by
      have h := hk.mul (hu.1 m).aestronglyMeasurable
      change AEStronglyMeasurable (fun r => k r * (D.localizer m r * u r))
        (volume.restrict (radialCore D)) at h
      simpa only [mul_left_comm] using h
    apply ((hu.1 m).norm.const_mul (L m)).mono' hm
    exact Eventually.of_forall fun r => by
      simpa only [Real.norm_eq_abs] using hpoint m r
  have hsq (m : ℕ) :
      (∫ r, (D.localizer m r * (k r * u r)) ^ 2 ∂volume.restrict (radialCore D)) ≤
        (L m) ^ 2 * ∫ r, (D.localizer m r * u r) ^ 2 ∂volume.restrict (radialCore D) := by
    calc
      _ ≤ ∫ r, (L m) ^ 2 * (D.localizer m r * u r) ^ 2
          ∂volume.restrict (radialCore D) := by
        apply integral_mono (hl m).integrable_sq ((hu.1 m).integrable_sq.const_mul _)
        intro r
        have hp := pow_le_pow_left₀ (abs_nonneg _) (hpoint m r) 2
        simpa only [mul_pow, sq_abs] using hp
      _ = _ := integral_const_mul _ _
  obtain ⟨K, _, hweight⟩ := r11b_exp_weight_le (Alo + 2 * B) Ahi γlo γhi hγ
  have hw (m : ℕ) :
      exp (Alo * radialQ (D.cellIndex m) + 2 * γlo * radialS (D.cellIndex m)) *
          (L m) ^ 2 ≤
        C ^ 2 * K * exp (Ahi * radialQ (D.cellIndex m) + 2 * γhi * radialS (D.cellIndex m)) := by
    calc
      _ = C ^ 2 * exp ((Alo + 2 * B) * radialQ (D.cellIndex m) +
          2 * γlo * radialS (D.cellIndex m)) := by
        have he : exp ((Alo + 2 * B) * radialQ (D.cellIndex m) +
            2 * γlo * radialS (D.cellIndex m)) =
            exp (Alo * radialQ (D.cellIndex m) + 2 * γlo * radialS (D.cellIndex m)) *
              exp (B * radialQ (D.cellIndex m)) * exp (B * radialQ (D.cellIndex m)) := by
          rw [← exp_add, ← exp_add]
          congr 1
          ring
        rw [he]
        dsimp only [L]
        ring
      _ ≤ _ := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left (hweight (D.cellIndex m)) (sq_nonneg C)
  refine ⟨hl, ?_⟩
  apply (hu.2.mul_left (C ^ 2 * K)).of_nonneg_of_le
    (fun m => mul_nonneg (exp_pos _).le (integral_nonneg fun r => sq_nonneg _))
  intro m
  calc
    _ ≤ exp (Alo * radialQ (D.cellIndex m) + 2 * γlo * radialS (D.cellIndex m)) *
        ((L m) ^ 2 * ∫ r, (D.localizer m r * u r) ^ 2 ∂volume.restrict (radialCore D)) :=
      mul_le_mul_of_nonneg_left (hsq m) (exp_pos _).le
    _ = (exp (Alo * radialQ (D.cellIndex m) + 2 * γlo * radialS (D.cellIndex m)) *
        (L m) ^ 2) * ∫ r, (D.localizer m r * u r) ^ 2 ∂volume.restrict (radialCore D) :=
      (mul_assoc _ _ _).symm
    _ ≤ (C ^ 2 * K * exp (Ahi * radialQ (D.cellIndex m) + 2 * γhi * radialS (D.cellIndex m))) *
        ∫ r, (D.localizer m r * u r) ^ 2 ∂volume.restrict (radialCore D) :=
      mul_le_mul_of_nonneg_right (hw m) (integral_nonneg fun r => sq_nonneg _)
    _ = _ := mul_assoc _ _ _

end ContinuousFlexibility.Radial
