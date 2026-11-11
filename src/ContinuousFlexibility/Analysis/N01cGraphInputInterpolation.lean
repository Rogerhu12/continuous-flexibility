import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization

/-!
# Interpolated angular inputs for the complete graph estimate

The zero-state factors use a single fixed offset and effective order
beta minus one. Positive-state factors use the offset-zero interpolation
chosen once; their parameter-prefix loss is counted in their effective
spatial order, rather than changing the low base.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped BigOperators

section Seminorms

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

theorem oneHighVariationWeight_le_uniformHigh
    (p : ℕ → Seminorm ℝ X) (base high : ℕ) (x : X)
    {k : ℕ} (v : Fin k → X) {M : ℝ} (hM : 1 ≤ M)
    (hx : p high x ≤ M) (hlo : ∀ i, p base (v i) ≤ 1)
    (hhi : ∀ i, p high (v i) ≤ M) :
    oneHighVariationWeight p base high x v ≤ ((k : ℝ) + 2) * M := by
  classical
  have hprod (t : Finset (Fin k)) : (∏ i ∈ t, p base (v i)) ≤ 1 :=
    Finset.prod_le_one (fun i _ => apply_nonneg _ _) (fun i _ => hlo i)
  have hfirst : (1 + p high x) * ∏ i, p base (v i) ≤ 1 + M := by
    calc
      _ ≤ (1 + p high x) * 1 :=
        mul_le_mul_of_nonneg_left (hprod Finset.univ)
          (add_nonneg zero_le_one (apply_nonneg _ _))
      _ ≤ 1 + M := by simpa only [mul_one] using add_le_add le_rfl hx
  have hterm (i : Fin k) :
      p high (v i) * ∏ j ∈ Finset.univ.erase i, p base (v j) ≤ M := by
    exact (mul_le_mul_of_nonneg_left (hprod (Finset.univ.erase i))
      (apply_nonneg (p high) (v i))).trans (by simpa only [mul_one] using hhi i)
  have hsum : (∑ i : Fin k, p high (v i) *
      ∏ j ∈ Finset.univ.erase i, p base (v j)) ≤ (k : ℝ) * M := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  exact (add_le_add hfirst hsum).trans (by nlinarith)

theorem one_add_seminorm_le_spatialPower
    (p : Seminorm ℝ X) (x : X) {C R : ℝ} (hC : 1 ≤ C) (hR : 1 ≤ R)
    (n s : ℕ)
    (hx : p x ≤ C * R ^ ((n : ℝ) / ((s : ℝ) + 1))) :
    1 + p x ≤ 2 * C * R ^ ((n : ℝ) / ((s : ℝ) + 1)) := by
  have hp := Real.one_le_rpow hR (spatialOrder_fraction_nonneg n s)
  have hprod : 1 ≤ C * R ^ ((n : ℝ) / ((s : ℝ) + 1)) :=
    hC.trans (le_mul_of_one_le_right (zero_le_one.trans hC) hp)
  nlinarith

theorem oneHighVariationWeight_le_spatialPower
    (p : ℕ → Seminorm ℝ X) (base high : ℕ) (x : X)
    {k : ℕ} (v : Fin k → X) {C R : ℝ} (hC : 1 ≤ C) (hR : 1 ≤ R)
    (n s : ℕ) (hlo : ∀ i, p base (v i) ≤ 1)
    (hx : p high x ≤ C * R ^ ((n : ℝ) / ((s : ℝ) + 1)))
    (hv : ∀ i, p high (v i) ≤ C * R ^ ((n : ℝ) / ((s : ℝ) + 1))) :
    oneHighVariationWeight p base high x v ≤
      ((k : ℝ) + 2) * C * R ^ ((n : ℝ) / ((s : ℝ) + 1)) := by
  have hp := Real.one_le_rpow hR (spatialOrder_fraction_nonneg n s)
  have hM : 1 ≤ C * R ^ ((n : ℝ) / ((s : ℝ) + 1)) :=
    hC.trans (le_mul_of_one_le_right (zero_le_one.trans hC) hp)
  simpa only [mul_assoc] using
    oneHighVariationWeight_le_uniformHigh p base high x v hM hx hlo hv

end Seminorms

section ActualJets

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- A finite angular prefix of genuine flow jets has the raw inputs
needed for the graph formula on the already chosen common low ball. -/
theorem angularFlowJets_spatialPower_bound
    {U : Set X} {f : ℕ → X → ℝ} (J : ∀ b, SmoothDirections U (f b))
    (p : ℕ → Seminorm ℝ X) (center : X) (base high K N S o₀ offset : ℕ)
    (hNS : N + offset ≤ S)
    {x : X} (hx : x ∈ U) (hxlo : p base (x - center) ≤ 1)
    {R : ℝ} (hR : 1 ≤ R) (hxhi : p high (x - center) ≤ R)
    {Cz Cp Iz Ip E A H : ℝ} (hCz : 0 ≤ Cz) (hCp : 0 ≤ Cp)
    (hIz : 1 ≤ Iz) (hIp : 1 ≤ Ip) (hE : 1 ≤ E) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hzero : ∀ b, 1 ≤ b → b ≤ N →
      |f b x| ≤ Cz * (1 + p (b - 1 + o₀) (x - center)))
    (hpositive : ∀ j, 0 < j → j ≤ K → ∀ b, b ≤ N → ∀ v : Fin j → X,
      |(J b).D j x v| ≤ Cp * H * E ^ A *
        oneHighVariationWeight p base (b + offset) (x - center) v)
    (hIzero : ∀ a, a ≤ S → ∀ y, p base y ≤ 1 → p high y ≤ R →
      p (a + o₀) y ≤ Iz * R ^ ((a : ℝ) / ((S : ℝ) + 1)))
    (hIpositive : ∀ a, a ≤ S → ∀ y, p base y ≤ 1 → p high y ≤ R →
      p a y ≤ Ip * R ^ ((a : ℝ) / ((S : ℝ) + 1))) :
    ∀ j, j ≤ K → ∀ b, 0 < j + b → b ≤ N → ∀ v : Fin j → X,
      (∀ i, p base (v i) ≤ 1) → (∀ i, p high (v i) ≤ R) →
        |(J b).D j x v| ≤
          (1 + 2 * Cz * Iz + Cp * ((K : ℝ) + 2) * Ip) *
            E ^ A * parameterHeightWeight H j *
              R ^ (((if j = 0 then b - 1 else b + offset : ℕ) : ℝ) /
                ((S : ℝ) + 1)) := by
  let C : ℝ := 1 + 2 * Cz * Iz + Cp * ((K : ℝ) + 2) * Ip
  have hIz₀ : 0 ≤ Iz := zero_le_one.trans hIz
  have hIp₀ : 0 ≤ Ip := zero_le_one.trans hIp
  have hC₀ : 0 ≤ C := by dsimp only [C]; positivity
  have hEpow : 1 ≤ E ^ A := Real.one_le_rpow hE hA
  have hEpow₀ : 0 ≤ E ^ A := zero_le_one.trans hEpow
  intro j hj b hpart hb v hvlo hvhi
  by_cases hj0 : j = 0
  · subst j
    rw [smoothDirections_D_zero_apply (J b) hx v]
    simp only [parameterHeightWeight, if_pos rfl, ite_true, mul_one]
    have hbpos : 1 ≤ b := by omega
    have hbS : b - 1 ≤ S := by omega
    have hz := one_add_seminorm_le_spatialPower (p (b - 1 + o₀)) (x - center)
      hIz hR (b - 1) S (hIzero (b - 1) hbS _ hxlo hxhi)
    have hcoeff : 2 * Cz * Iz ≤ C * E ^ A := by
      have hle : 2 * Cz * Iz ≤ C := by
        dsimp only [C]
        have hnonneg : 0 ≤ Cp * ((K : ℝ) + 2) * Ip := by positivity
        linarith
      exact hle.trans (le_mul_of_one_le_right hC₀ hEpow)
    calc
      _ ≤ Cz * (1 + p (b - 1 + o₀) (x - center)) := hzero b hbpos hb
      _ ≤ Cz * (2 * Iz * R ^ (((b - 1 : ℕ) : ℝ) / ((S : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hz hCz
      _ = (2 * Cz * Iz) * R ^ (((b - 1 : ℕ) : ℝ) / ((S : ℝ) + 1)) := by ring
      _ ≤ (C * E ^ A) * R ^ (((b - 1 : ℕ) : ℝ) / ((S : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (zero_le_one.trans hR) _)
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    simp only [parameterHeightWeight, if_neg hj0]
    have hbS : b + offset ≤ S := (Nat.add_le_add hb le_rfl).trans hNS
    have hw := oneHighVariationWeight_le_spatialPower p base (b + offset)
      (x - center) v hIp hR (b + offset) S hvlo
      (hIpositive (b + offset) hbS _ hxlo hxhi)
      (fun i => hIpositive (b + offset) hbS _ (hvlo i) (hvhi i))
    have hcast : (j : ℝ) + 2 ≤ (K : ℝ) + 2 :=
      add_le_add (Nat.cast_le.mpr hj) le_rfl
    have hW : 0 ≤ Cp * H * E ^ A :=
      mul_nonneg (mul_nonneg hCp hH) hEpow₀
    have hcoeff : Cp * ((K : ℝ) + 2) * Ip ≤ C := by
      dsimp only [C]
      have hnonneg : 0 ≤ 2 * Cz * Iz := by positivity
      linarith
    calc
      _ ≤ Cp * H * E ^ A *
          oneHighVariationWeight p base (b + offset) (x - center) v :=
        hpositive j hjpos hj b hb v
      _ ≤ Cp * H * E ^ A *
          (((j : ℝ) + 2) * Ip * R ^ (((b + offset : ℕ) : ℝ) / ((S : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hw hW
      _ ≤ Cp * H * E ^ A *
          (((K : ℝ) + 2) * Ip * R ^ (((b + offset : ℕ) : ℝ) / ((S : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcast hIp₀)
            (Real.rpow_nonneg (zero_le_one.trans hR) _)) hW
      _ = (Cp * ((K : ℝ) + 2) * Ip) * E ^ A * H *
          R ^ (((b + offset : ℕ) : ℝ) / ((S : ℝ) + 1)) := by ring
      _ ≤ C * E ^ A * H * R ^ (((b + offset : ℕ) : ℝ) / ((S : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hEpow₀) hH)
          (Real.rpow_nonneg (zero_le_one.trans hR) _)

end ActualJets

end ContinuousFlexibility.Analysis
