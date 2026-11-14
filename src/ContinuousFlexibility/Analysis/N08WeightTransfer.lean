module

public import ContinuousFlexibility.Scalar.WeightedReferenceBounds

/-!
# Transferring control-label losses to a physical height weight

A comparison between positive height powers suffices. It is unnecessary
to invert the endpoint formula or compare numerical cell indices. Raising
the comparison to a positive power pays for a prescribed negative label
weight; the remaining positive label power absorbs every envelope loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

section Numeric

variable {I : Type*} {P H E : I → ℝ} {a b θ t C : ℝ}

theorem n08_weight_transfer
    (hP : ∀ i, 0 < P i) (hH : ∀ i, 0 < H i) (hE : ∀ i, 0 ≤ E i)
    (hC : 0 < C) (hθ : 0 < θ) (hgap : t < b * θ)
    (hcompare : ∀ i, P i ^ a ≤ C * H i ^ b)
    (henvelope : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 ≤ K ∧ ∀ i, H i ^ η * E i ≤ K)
    (δ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i,
      P i ^ (a * θ + δ) * H i ^ (-t) * E i ≤ K * P i ^ δ := by
  obtain ⟨K, hK, hKb⟩ := henvelope (b * θ - t) (sub_pos.mpr hgap)
  refine ⟨C ^ θ * K, mul_nonneg (Real.rpow_nonneg hC.le _) hK, fun i => ?_⟩
  have hpower : P i ^ (a * θ) ≤ C ^ θ * H i ^ (b * θ) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (hP i).le a) (hcompare i) hθ.le
    simpa only [Real.mul_rpow hC.le (Real.rpow_nonneg (hH i).le b),
      ← Real.rpow_mul (hP i).le, ← Real.rpow_mul (hH i).le] using h
  have hlow : 0 ≤ P i ^ δ := Real.rpow_nonneg (hP i).le _
  have hlabel : 0 ≤ H i ^ (-t) := Real.rpow_nonneg (hH i).le _
  calc
    _ = P i ^ δ * (P i ^ (a * θ) * H i ^ (-t) * E i) := by
      rw [Real.rpow_add (hP i)]
      ring
    _ ≤ P i ^ δ * ((C ^ θ * H i ^ (b * θ)) * H i ^ (-t) * E i) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpower hlabel) (hE i)) hlow
    _ = P i ^ δ * C ^ θ * (H i ^ (b * θ - t) * E i) := by
      rw [sub_eq_add_neg, Real.rpow_add (hH i)]
      ring
    _ ≤ P i ^ δ * C ^ θ * K :=
      mul_le_mul_of_nonneg_left (hKb i) (mul_nonneg hlow (Real.rpow_nonneg hC.le _))
    _ = _ := by ring

end Numeric

variable {D : ReferenceData} {T : MaterialData} {I : Type*}

/-- At actual material points, every fixed label-envelope loss is absorbed
by the positive exponent remaining after the explicit height comparison. -/
theorem n08_material_weight_transfer
    (hT : IsMaterialData D T) (physical label : I → ℝ)
    (hphysical : ∀ i, physical i ∈ Set.Ioo D.a D.b)
    (hlabel : ∀ i, label i ∈ Set.Ioo D.a D.b)
    {a b θ t C : ℝ} (hC : 0 < C) (hθ : 0 < θ) (hgap : t < b * θ)
    (hcompare : ∀ i, T.H (physical i) ^ a ≤ C * T.H (label i) ^ b)
    (A δ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i,
      T.H (physical i) ^ (a * θ + δ) * T.H (label i) ^ (-t) * T.M (label i) ^ A ≤
        K * T.H (physical i) ^ δ := by
  apply n08_weight_transfer
    (fun i => (hT.2.1 _ (hphysical i)).2.1)
    (fun i => (hT.2.1 _ (hlabel i)).2.1)
    (fun i => Real.rpow_nonneg (zero_le_one.trans (hT.2.1 _ (hlabel i)).2.2.2) A)
    hC hθ hgap hcompare ?_ δ
  intro η hη
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdecay, _⟩ := hdata
  obtain ⟨K, hK, hKb, _, _⟩ := hdecay A η hη
  exact ⟨K, hK.le, fun i => hKb (label i) (hlabel i)⟩

end ContinuousFlexibility.Statements
