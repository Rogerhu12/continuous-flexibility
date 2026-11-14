module

public import ContinuousFlexibility.Analysis.N04PulledFieldsInverseAffineBounds

/-!
# Abstract assembly of the two inverse-coordinate prefixes

All coefficient arithmetic and prefix choices are made before the
concrete physical parameter grading is substituted. The two scalar
towers reconstruct any genuine tower of the same affine inverse point.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

private theorem n04PulledFieldsInversePoint_coefficient
    {E P B ell : ℝ} (hE : 1 ≤ E) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hell : |ell| ≤ P * E ^ P) :
    |ell| * (B * E ^ B) + B * E ^ B + 1 ≤
      (P * B + B + 1) * E ^ (P + B) := by
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have hEB : E ^ B ≤ E ^ (P + B) :=
    Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_left hP)
  have hone : 1 ≤ E ^ (P + B) := Real.one_le_rpow hE (add_nonneg hP hB)
  calc
    _ ≤ (P * E ^ P) * (B * E ^ B) + B * E ^ (P + B) + E ^ (P + B) :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hell (mul_nonneg hB (Real.rpow_nonneg hEpos.le _)))
        (mul_le_mul_of_nonneg_left hEB hB)) hone
    _ = _ := by rw [Real.rpow_add hEpos]; ring

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {U : Set X} {Ω : Set PolarPoint}

/-- Scalar prefixes and an independent length envelope reconstruct the
vector prefix. No concrete coordinate or parameter grading is unfolded. -/
theorem n04PulledFields_inversePoint_prefix_of_scalar
    {f : Bool → ℕ → X × PolarPoint → ℝ}
    (J : ∀ i m, SmoothDirections (U ×ˢ Ω) (f i m))
    {φ : ℕ → X × PolarPoint → PolarPoint}
    (origin length : ℕ → ℝ)
    (heq : ∀ m z, z ∈ U ×ˢ Ω →
      φ m z = (origin m + length m * f false m z, z.2.2 + f true m z))
    (p : ℕ → Seminorm ℝ X) (base : ℕ) (E H : ℕ → ℝ)
    (hE : ∀ m, 1 ≤ E m) (hH : ∀ m, 0 ≤ H m)
    (hlength : ∃ P : ℝ, 0 < P ∧ ∀ m, |length m| ≤ P * E m ^ P)
    (hscalar : ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ N : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i m z, z ∈ U → p low z ≤ 1 →
      ∀ q ∈ Ω, ∀ R : ℝ, 1 ≤ R → p (low + N + shift * K + 1) z ≤ R →
      ∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → X × PolarPoint,
      (∀ i, p low (v i).1 ≤ 1) →
      (∀ i, p (low + N + shift * K + 1) (v i).1 ≤ R) →
      (∀ i, ‖(v i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (v i).1 = 0) →
      (∀ i, w.isState i = true → (v i).2 = 0) →
        |(J i m).D n (z, q) v| ≤ B * E m ^ B * parameterHeightWeight (H m) w.stateArity *
          (R ^ (1 / (((N + shift * K : ℕ) : ℝ) + 1))) ^
            (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + shift * K)) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ offset : ℕ, ∀ N : ℕ,
      ∃ M A : ℝ, 1 ≤ M ∧ 0 ≤ A ∧
      ∀ m, ∀ Jφ : SmoothDirections (U ×ˢ Ω) (φ m),
      ∀ z ∈ U, p low z ≤ 1 → ∀ q ∈ Ω, ∀ R : ℝ, 1 ≤ R →
      p (low + N + offset + 1) z ≤ R →
      ∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → X × PolarPoint,
      (∀ i, p low (v i).1 ≤ 1) →
      (∀ i, p (low + N + offset + 1) (v i).1 ≤ R) →
      (∀ i, ‖(v i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (v i).1 = 0) →
      (∀ i, w.isState i = true → (v i).2 = 0) →
        ‖Jφ.D n (z, q) v‖ ≤ M * E m ^ A * parameterHeightWeight (H m) w.stateArity *
          (R ^ (1 / (((N + offset : ℕ) : ℝ) + 1))) ^
            (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + offset) := by
  refine hlength.elim fun P hP => ?_
  refine hscalar.elim fun low hlow => ⟨low, hlow.1, fun K => ?_⟩
  refine (hlow.2 K).elim fun shift hshift => ⟨shift * K, fun N => ?_⟩
  refine (hshift N).elim fun B hB => ?_
  have hM : 1 ≤ P * B + B + 1 := by
    nlinarith [mul_nonneg hP.1.le hB.1.le]
  refine ⟨P * B + B + 1, P + B, hM, add_nonneg hP.1.le hB.1.le, ?_⟩
  intro m Jφ z hz hzlow q hq R hR hzR n hn hnN w hw v hvlow hvR hvphys hvstate hvangle
  have ht : 1 ≤ R ^ (1 / (((N + shift * K : ℕ) : ℝ) + 1)) :=
    Real.one_le_rpow hR (by positivity)
  have hrad := hB.2 false m z hz hzlow q hq R hR hzR n hn hnN w hw
    v hvlow hvR hvphys hvstate hvangle
  have hang := hB.2 true m z hz hzlow q hq R hR hzR n hn hnN w hw
    v hvlow hvR hvphys hvstate hvangle
  have hraw := n04PulledFields_inverseAffine_pureWord_bound (J false m) (J true m) Jφ
    (origin m) (length m) (heq m) hn w (shift * K) ⟨hz, hq⟩ v hvphys hvangle
    (mul_nonneg hB.1.le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _))
    (hH m) ht hrad hang
  have hcoef := n04PulledFieldsInversePoint_coefficient (hE m) hP.1.le hB.1.le (hP.2 m)
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (parameterHeightWeight_nonneg (hH m) _))
    (pow_nonneg (Real.rpow_nonneg (zero_le_one.trans hR) _) _))

end ContinuousFlexibility.Analysis
