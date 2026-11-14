module

public import ContinuousFlexibility.Analysis.MaterialScalarPowerJets
public import ContinuousFlexibility.Analysis.MaterialEndpointWeightTransport

/-!
# Actual envelope ratios on bounded endpoint-coordinate displacements

The original E0 is only positive. Its proved fixed scaled lower bound
raises possibly negative exponents before the actual endpoint comparison.
All constants precede both physical points and the sample denominator.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

private theorem rpow_raise_of_scaled_floor {x K a b : ℝ}
    (hx : 0 < x) (hK : 0 < K) (hfloor : 1 ≤ K * x) (hab : a ≤ b) :
    x ^ a ≤ K ^ (b - a) * x ^ b := by
  have hpower : 1 ≤ K ^ (b - a) * x ^ (b - a) := by
    rw [← Real.mul_rpow hK.le hx.le]
    exact Real.one_le_rpow hfloor (sub_nonneg.mpr hab)
  calc
    x ^ a ≤ x ^ a * (K ^ (b - a) * x ^ (b - a)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower
        (Real.rpow_nonneg hx.le a)
    _ = K ^ (b - a) * (x ^ a * x ^ (b - a)) := by ring
    _ = K ^ (b - a) * x ^ b := by
      rw [← Real.rpow_add hx, show a + (b - a) = b by ring]

/-- Taking gamma equal to 1 or -1 gives the two genuine envelope ratios. -/
def materialE0NormalizedPower (T : MaterialData) (γ sample : ℝ) : ℝ → ℝ :=
  fun r => T.E0 r ^ γ * T.E0 sample ^ (-γ)

/-- Every actual physical derivative is controlled at the same denominator
point. No unscaled E0 floor, sample replacement, or cell hypothesis is used. -/
theorem materialE0_normalized_physical_jets_of_bounded_X_shift
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (γ : ℝ) (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ r s : ℝ,
      r ∈ Ioo D.a D.b → s ∈ Ioo D.a D.b →
      |endpointX 1 (endpointDistance D r) -
        endpointX 1 (endpointDistance D s)| ≤ L →
      |iteratedDeriv n (materialE0NormalizedPower T γ s) r| ≤ B * T.E0 s ^ A := by
  obtain ⟨B, A, hB, hA, hphysical⟩ := materialE0_rpow_physical_jet_bound hT γ n
  obtain ⟨K, hK, hfloor⟩ := material_E0_uniform_scaled_lower hT hD
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  let R := A + |γ|
  have hR : 0 ≤ R := add_nonneg hA (abs_nonneg _)
  obtain ⟨J, P, hJ, hP, htransfer⟩ :=
    material_global_H_M_E0_rpow_bounded_X_shift hT hD (0 : ℝ) (0 : ℝ) hR hL
  let Kp := K ^ (|γ| - γ)
  let Ks := K ^ (|γ| + γ)
  have hKp : 0 ≤ Kp := Real.rpow_nonneg hKpos.le _
  have hKs : 0 ≤ Ks := Real.rpow_nonneg hKpos.le _
  let C := B * Kp * J
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hB hKp) hJ.le
  refine ⟨C * Ks, P + |γ|, mul_nonneg hC hKs, add_nonneg hP (abs_nonneg _), ?_⟩
  intro r s hr hs hdist
  have hEr : 0 < T.E0 r := (hT.2.1 r hr).2.2.1
  have hEs : 0 < T.E0 s := (hT.2.1 s hs).2.2.1
  have hp : T.E0 r ^ γ * T.E0 r ^ A ≤ Kp * T.E0 r ^ R := by
    rw [← Real.rpow_add hEr]
    have h := rpow_raise_of_scaled_floor hEr hKpos (hfloor r hr)
      (show γ + A ≤ A + |γ| by linarith only [le_abs_self γ])
    simpa only [Kp, R, show A + |γ| - (γ + A) = |γ| - γ by ring] using h
  have hdenom : T.E0 s ^ (-γ) ≤ Ks * T.E0 s ^ |γ| := by
    simpa only [Ks, sub_neg_eq_add] using
      rpow_raise_of_scaled_floor hEs hKpos (hfloor s hs) (neg_le_abs γ)
  have hshift : T.E0 r ^ R ≤ J * T.E0 s ^ P := by
    simpa only [Real.rpow_zero, one_mul] using htransfer r s hr hs hdist
  have hnum : |iteratedDeriv n (fun t => T.E0 t ^ γ) r| ≤ C * T.E0 s ^ P := by
    calc
      _ ≤ B * T.E0 r ^ γ * T.E0 r ^ A := hphysical r hr
      _ = B * (T.E0 r ^ γ * T.E0 r ^ A) := by ring
      _ ≤ B * (Kp * T.E0 r ^ R) := mul_le_mul_of_nonneg_left hp hB
      _ ≤ B * (Kp * (J * T.E0 s ^ P)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hshift hKp) hB
      _ = C * T.E0 s ^ P := by dsimp only [C]; ring
  change |iteratedDeriv n (fun t => T.E0 t ^ γ * T.E0 s ^ (-γ)) r| ≤ _
  rw [iteratedDeriv_mul_const_field, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hEs.le (-γ))]
  calc
    _ ≤ (C * T.E0 s ^ P) * (Ks * T.E0 s ^ |γ|) :=
      mul_le_mul hnum hdenom (Real.rpow_nonneg hEs.le _)
        (mul_nonneg hC (Real.rpow_nonneg hEs.le _))
    _ = (C * Ks) * T.E0 s ^ (P + |γ|) := by
      rw [Real.rpow_add hEs]
      ring

end ContinuousFlexibility.Statements
