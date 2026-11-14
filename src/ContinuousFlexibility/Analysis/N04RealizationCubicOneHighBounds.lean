import ContinuousFlexibility.Analysis.N04RealizationUnitCubicJets
import ContinuousFlexibility.Analysis.N07aHeightFamilyTame
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Fixed-loss bounds for the actual cubic quotients

The numerator towers and their endpoint representatives are supplied on
one open parameter domain. Two cubic divisions retain that domain and
the exact height factor. Their only extra grading cost is six radial
orders. The inverse sixth power of the same fixed interval width is
absorbed at the caller's original sample, before collecting the fields.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Genuine numerator bounds give one genuine divided tower per field.
No divided-field bound, parameter endpoint tower, or smaller neighborhood
is a premise. The supplied sample and height factor are unchanged. -/
theorem n04Realization_unitCubic_oneHigh_bounds
    {U : Set X} (hU : IsOpen U)
    (p : ℕ → Seminorm ℝ X) (hp : WithSeminorms p) (hmono : Monotone p)
    (base : ℕ) (E H width : I → ℝ)
    (hE : ∀ m, 1 ≤ E m) (hH : ∀ m, 0 ≤ H m)
    (hwidth : ∀ m, 0 < width m) {bw : ℝ} (hbw : 0 < bw)
    (hwidthBound : ∀ m, (width m)⁻¹ ≤ bw * E m ^ bw)
    (N e : I → X → PolarPoint → ℝ)
    (RN : ∀ m, MixedJetRegularity U (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) (N m))
    (hrep : ∀ m, ∀ x ∈ U, ∃ F : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧
      EqOn F (N m x) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) ∧
      ∀ c : Bool, ∀ θ i, i ≤ 2 →
        iteratedDeriv i (fun t : ℝ => F (t, θ)) (if c then 1 else 0) = 0)
    (hfactor : ∀ m, ∀ x ∈ U, ∀ q ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ),
      N m x q = width m ^ 6 * (q.1 * (1 - q.1)) ^ 3 * e m x q)
    (hnum : ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m a b, a + b ≤ s →
        ∀ q (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)),
        ∀ x ∈ U, ∀ v : Fin k → X,
          |((RN m).parameter a b q hq).D k x v| ≤
            B * E m ^ B * H m * oneHighVariationWeight p base (s + loss) x v) :
    ∃ RE : ∀ m, MixedJetRegularity U
        (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) (e m),
      ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
        ∀ m a b, a + b ≤ s →
          ∀ q (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)),
          ∀ x ∈ U, ∀ v : Fin k → X,
            |((RE m).parameter a b q hq).D k x v| ≤
              B * E m ^ B * H m * oneHighVariationWeight p base (s + loss) x v := by
  classical
  choose loss horder using hnum
  choose B hB hb using horder
  let G : ∀ m : I, ∀ k : ℕ, ℕ → ℕ → X × (Fin k → X) → ℝ :=
    fun m k a b y => B k (a + b) * E m ^ B k (a + b) * H m *
      oneHighVariationWeight p base (a + b + loss k) y.1 y.2
  have hG (m : I) (k a b : ℕ) : Continuous (G m k a b) := by
    apply continuous_const.mul
    simpa only [sub_zero] using
      n07a_oneHighVariationWeight_continuous hp base (a + b + loss k) k (0 : X)
  have hGb (m : I) (k a b : ℕ) (q : PolarPoint)
      (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ))
      (x : X) (hx : x ∈ U) (v : Fin k → X) :
      |((RN m).parameter a b q hq).D k x v| ≤ G m k a b (x, v) :=
    hb k (a + b) m a b le_rfl q hq x hx v
  choose RE hRE using fun m => n04Realization_unitCubic_parameterJets
    hU (hwidth m) (RN m) (hrep m) (hfactor m) (G m) (hG m) (hGb m)
  refine ⟨RE, fun k => ⟨loss k + 6, fun s => ?_⟩⟩
  let A : ℝ := 1 + ∑ i : Fin (s + 7), B k i.val
  have hA : 0 < A := by
    have hsum : 0 ≤ ∑ i : Fin (s + 7), B k i.val :=
      Finset.sum_nonneg (fun i _ => (hB k i.val).le)
    dsimp only [A]
    linarith
  have hBA (r : ℕ) (hr : r ≤ s + 6) : B k r ≤ A := by
    have hsum : B k r ≤ ∑ i : Fin (s + 7), B k i.val :=
      Finset.single_le_sum (fun (i : Fin (s + 7)) _ => (hB k i.val).le)
        (Finset.mem_univ (⟨r, by omega⟩ : Fin (s + 7)))
    exact hsum.trans (le_add_of_nonneg_left zero_le_one)
  obtain ⟨Q, hQ, hpack⟩ := coefficientEnvelope_pack (bw ^ 6 * A) (bw * 6 + A)
  refine ⟨Q, hQ, ?_⟩
  intro m a b hab q hq x hx v
  let r : ℕ := (a + 6) + b
  let V : ℝ := oneHighVariationWeight p base (s + (loss k + 6)) x v
  have hr : r ≤ s + 6 := by dsimp only [r]; omega
  have hV : 0 ≤ V := oneHighVariationWeight_nonneg p base _ x v
  have hEpos : 0 < E m := zero_lt_one.trans_le (hE m)
  have hcost : B k r * E m ^ B k r ≤ A * E m ^ A :=
    mul_le_mul (hBA r hr)
      (Real.rpow_le_rpow_of_exponent_le (hE m) (hBA r hr))
      (Real.rpow_nonneg hEpos.le _) hA.le
  have hweight : oneHighVariationWeight p base (r + loss k) x v ≤ V :=
    n07a_oneHighVariationWeight_mono hmono base (by dsimp only [r]; omega) x v
  have hGnonneg : 0 ≤ G m k (a + 6) b (x, v) :=
    mul_nonneg (mul_nonneg (mul_nonneg (hB k r).le
      (Real.rpow_nonneg hEpos.le _)) (hH m))
      (oneHighVariationWeight_nonneg p base _ x v)
  have hmajorant : G m k (a + 6) b (x, v) ≤ A * E m ^ A * H m * V :=
    mul_le_mul (mul_le_mul_of_nonneg_right hcost (hH m)) hweight
      (oneHighVariationWeight_nonneg p base _ x v)
      (mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg hEpos.le _)) (hH m))
  have hinv : 0 ≤ (width m ^ 6)⁻¹ := inv_nonneg.mpr (pow_pos (hwidth m) 6).le
  have hinvBound : (width m ^ 6)⁻¹ ≤ bw ^ 6 * E m ^ (bw * 6) := by
    rw [← inv_pow]
    calc
      (width m)⁻¹ ^ 6 ≤ (bw * E m ^ bw) ^ 6 :=
        pow_le_pow_left₀ (inv_nonneg.mpr (hwidth m).le) (hwidthBound m) 6
      _ = bw ^ 6 * E m ^ (bw * 6) := by
        rw [mul_pow]
        simpa only [Nat.cast_ofNat] using
          congrArg (fun u : ℝ => bw ^ 6 * u)
            (Real.rpow_mul_natCast hEpos.le bw 6).symm
  calc
    |((RE m).parameter a b q hq).D k x v| ≤
        (width m ^ 6)⁻¹ * G m k (a + 6) b (x, v) / 4 := hRE m k a b q hq x hx v
    _ ≤ (width m ^ 6)⁻¹ * G m k (a + 6) b (x, v) :=
      div_le_self (mul_nonneg hinv hGnonneg) (by norm_num)
    _ ≤ (bw ^ 6 * E m ^ (bw * 6)) * (A * E m ^ A * H m * V) :=
      mul_le_mul hinvBound hmajorant hGnonneg
        (mul_nonneg (pow_nonneg hbw.le 6) (Real.rpow_nonneg hEpos.le _))
    _ = (bw ^ 6 * A * E m ^ (bw * 6 + A)) * H m * V := by
      rw [Real.rpow_add hEpos (bw * 6) A]
      ring
    _ ≤ Q * E m ^ Q * H m * V :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hpack (E m) (hE m)) (hH m)) hV

end ContinuousFlexibility.Analysis
