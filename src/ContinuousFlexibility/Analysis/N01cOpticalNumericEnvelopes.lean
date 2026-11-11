import ContinuousFlexibility.Analysis.N01cOpticalRootProducts

/-!
# Finite numerical envelopes for the optical-root expansion

These lemmas only combine real scalar inequalities. They are applied to
the actual reference lower constant, upper optical bound and control
jets. Finite products and sums affect the coefficient and exponent, not
the state order or the common parameter neighbourhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

def HasPositiveEnvelope {X : Type*} (E F : X → ℝ) : Prop :=
  ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ x, F x ≤ C * E x ^ A

theorem hasPositiveEnvelope_const {X : Type*} (E : X → ℝ)
    (hE : ∀ x, 1 ≤ E x) (c : ℝ) : HasPositiveEnvelope E (fun _ => c) := by
  refine ⟨|c| + 1, 1, by positivity, zero_lt_one, fun x => ?_⟩
  rw [Real.rpow_one]
  exact (le_abs_self c).trans ((le_add_of_nonneg_right zero_le_one).trans
    (le_mul_of_one_le_right (by positivity) (hE x)))

theorem HasPositiveEnvelope.mul {X : Type*} {E F G : X → ℝ}
    (hE : ∀ x, 1 ≤ E x) (hF : HasPositiveEnvelope E F)
    (hG : HasPositiveEnvelope E G) (hG₀ : ∀ x, 0 ≤ G x) :
    HasPositiveEnvelope E (fun x => F x * G x) := by
  obtain ⟨C, A, hC, hA, hf⟩ := hF
  obtain ⟨B, K, hB, hK, hg⟩ := hG
  refine ⟨C * B, A + K, mul_pos hC hB, add_pos hA hK, fun x => ?_⟩
  have he : 0 < E x := zero_lt_one.trans_le (hE x)
  calc
    _ ≤ (C * E x ^ A) * (B * E x ^ K) :=
      mul_le_mul (hf x) (hg x) (hG₀ x) (mul_nonneg hC.le (Real.rpow_nonneg he.le _))
    _ = _ := by rw [Real.rpow_add he]; ring

theorem HasPositiveEnvelope.add {X : Type*} {E F G : X → ℝ}
    (hE : ∀ x, 1 ≤ E x) (hF : HasPositiveEnvelope E F)
    (hG : HasPositiveEnvelope E G) :
    HasPositiveEnvelope E (fun x => F x + G x) := by
  obtain ⟨C, A, hC, hA, hf⟩ := hF
  obtain ⟨B, K, hB, hK, hg⟩ := hG
  refine ⟨C + B, A + K, add_pos hC hB, add_pos hA hK, fun x => ?_⟩
  have ha := Real.rpow_le_rpow_of_exponent_le (hE x) (le_add_of_nonneg_right hK.le)
  have hk := Real.rpow_le_rpow_of_exponent_le (hE x) (le_add_of_nonneg_left hA.le)
  calc
    _ ≤ C * E x ^ A + B * E x ^ K := add_le_add (hf x) (hg x)
    _ ≤ C * E x ^ (A + K) + B * E x ^ (A + K) :=
      add_le_add (mul_le_mul_of_nonneg_left ha hC.le) (mul_le_mul_of_nonneg_left hk hB.le)
    _ = _ := by ring

theorem hasPositiveEnvelope_finsetSum {X ι : Type*} {E : X → ℝ}
    (hE : ∀ x, 1 ≤ E x) (s : Finset ι) (F : ι → X → ℝ)
    (hF : ∀ i ∈ s, HasPositiveEnvelope E (F i)) :
    HasPositiveEnvelope E (fun x => ∑ i ∈ s, F i x) := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty => intro _; simpa only [Finset.sum_empty] using hasPositiveEnvelope_const E hE 0
  | @insert i s hi ih =>
      intro hF
      have h := (hF i (Finset.mem_insert_self _ _)).add hE
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))
      simpa only [Finset.sum_insert hi] using h

theorem hasPositiveEnvelope_finsetProd {X ι : Type*} {E : X → ℝ}
    (hE : ∀ x, 1 ≤ E x) (s : Finset ι) (F : ι → X → ℝ)
    (hF₀ : ∀ i ∈ s, ∀ x, 0 ≤ F i x)
    (hF : ∀ i ∈ s, HasPositiveEnvelope E (F i)) :
    HasPositiveEnvelope E (fun x => ∏ i ∈ s, F i x) := by
  classical
  revert hF₀ hF
  induction s using Finset.induction_on with
  | empty => intro _ _; simpa only [Finset.prod_empty] using hasPositiveEnvelope_const E hE 1
  | @insert i s hi ih =>
      intro hF₀ hF
      have ht := ih (fun j hj => hF₀ j (Finset.mem_insert_of_mem hj))
        (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      have h := (hF i (Finset.mem_insert_self _ _)).mul hE ht
        (fun x => Finset.prod_nonneg (fun j hj => hF₀ j (Finset.mem_insert_of_mem hj) x))
      simpa only [Finset.prod_insert hi] using h

theorem HasPositiveEnvelope.pow {X : Type*} {E F : X → ℝ}
    (hE : ∀ x, 1 ≤ E x) (hF : HasPositiveEnvelope E F)
    (hF₀ : ∀ x, 0 ≤ F x) (n : ℕ) : HasPositiveEnvelope E (fun x => F x ^ n) := by
  have h := hasPositiveEnvelope_finsetProd hE (Finset.univ : Finset (Fin n))
    (fun _ => F) (fun _ _ => hF₀) (fun _ _ => hF)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

theorem HasPositiveEnvelope.sqrt {X : Type*} {E F : X → ℝ}
    (hE : ∀ x, 1 ≤ E x) (hF : HasPositiveEnvelope E F)
    (hF₀ : ∀ x, 0 ≤ F x) : HasPositiveEnvelope E (fun x => Real.sqrt (F x)) := by
  obtain ⟨C, A, hC, hA, hf⟩ := hF
  refine ⟨1 + C, A, by positivity, hA, fun x => ?_⟩
  have hs : Real.sqrt (F x) ≤ 1 + F x := Real.sqrt_le_iff.mpr
    ⟨by linarith [hF₀ x], by nlinarith [sq_nonneg (F x), hF₀ x]⟩
  calc
    _ ≤ 1 + F x := hs
    _ ≤ E x ^ A + C * E x ^ A := add_le_add (Real.one_le_rpow (hE x) hA.le) (hf x)
    _ = _ := by ring

theorem hasPositiveEnvelope_inv_of_lower {X : Type*} {E c : X → ℝ}
    (hE : ∀ x, 1 ≤ E x) {c₀ K : ℝ} (hc₀ : 0 < c₀) (hK : 0 < K)
    (hlower : ∀ x, c₀ * E x ^ (-K) ≤ c x) :
    HasPositiveEnvelope E (fun x => (c x)⁻¹) := by
  refine ⟨c₀⁻¹, K, inv_pos.mpr hc₀, hK, fun x => ?_⟩
  have he : 0 < E x := zero_lt_one.trans_le (hE x)
  have h := inv_anti₀ (mul_pos hc₀ (Real.rpow_pos_of_pos he (-K))) (hlower x)
  simpa only [mul_inv_rev, Real.rpow_neg he.le, inv_inv, mul_comm] using h

theorem endpointPowerCompositionMajorant_envelope {X : Type*}
    (E c M : X → ℝ) (A : ℕ → X → ℝ)
    (hE : ∀ x, 1 ≤ E x) (hc : ∀ x, 0 < c x) (hM₀ : ∀ x, 0 ≤ M x)
    (hA₀ : ∀ j x, 0 ≤ A j x)
    (hcInv : HasPositiveEnvelope E (fun x => (c x)⁻¹))
    (hM : HasPositiveEnvelope E M) (hA : ∀ j, HasPositiveEnvelope E (A j))
    (k n : ℕ) :
    HasPositiveEnvelope E (fun x => endpointPowerCompositionMajorant
      (c x) (M x) (fun j => A j x) k n) := by
  apply hasPositiveEnvelope_finsetSum hE Finset.univ
  intro d _
  have hp := hasPositiveEnvelope_finsetProd hE (Finset.univ : Finset (Fin d.length))
    (fun i x => A (d.partSize i) x) (fun i _ => hA₀ _) (fun i _ => hA _)
  have hi := hcInv.pow hE (fun x => (inv_pos.mpr (hc x)).le) (k + d.length)
  have hs := hM.sqrt hE hM₀
  have hq := hs.mul hE hi (fun x => pow_nonneg (inv_pos.mpr (hc x)).le _)
  have hcoeff := (hasPositiveEnvelope_const E hE
    |rpowJetCoefficient ((1 / 2 : ℝ) - (k : ℝ)) d.length|).mul hE hq
      (fun x => mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (inv_pos.mpr (hc x)).le _))
  have hall := hcoeff.mul hE hp (fun x => Finset.prod_nonneg (fun i _ => hA₀ _ x))
  simpa only [div_eq_mul_inv, inv_pow] using hall

theorem endpointRootProductMajorant_envelope {X : Type*}
    (E c M : X → ℝ) (A B : ℕ → X → ℝ)
    (hE : ∀ x, 1 ≤ E x) (hc : ∀ x, 0 < c x) (hM₀ : ∀ x, 0 ≤ M x)
    (hA₀ : ∀ j x, 0 ≤ A j x) (hB₀ : ∀ j x, 0 ≤ B j x)
    (hcInv : HasPositiveEnvelope E (fun x => (c x)⁻¹))
    (hM : HasPositiveEnvelope E M) (hA : ∀ j, HasPositiveEnvelope E (A j))
    (hB : ∀ j, HasPositiveEnvelope E (B j)) (k n : ℕ) :
    HasPositiveEnvelope E (fun x => endpointRootProductMajorant
      (c x) (M x) (fun j => A j x) (fun j => B j x) k n) := by
  apply hasPositiveEnvelope_finsetSum hE Finset.univ
  intro d _
  have hq := endpointPowerCompositionMajorant_envelope E c M A hE hc hM₀ hA₀
    hcInv hM hA k (radialLeibnizOrders k n d 0)
  have hp := hasPositiveEnvelope_finsetProd hE (Finset.univ : Finset (Fin k))
    (fun i x => B (radialLeibnizOrders k n d i.succ) x)
    (fun i _ => hB₀ _) (fun i _ => hB _)
  have hcoeff := (hasPositiveEnvelope_const E hE
    (radialLeibnizCoefficient k n d : ℝ)).mul hE hq
      (fun x => endpointPowerCompositionMajorant_nonneg (hc x).le _ (fun j => hA₀ j x) k _)
  exact hcoeff.mul hE hp (fun x => Finset.prod_nonneg (fun i _ => hB₀ _ x))

end ContinuousFlexibility.Analysis
