import ContinuousFlexibility.Analysis.N04PulledFieldsInversePrefixSlots
import ContinuousFlexibility.Analysis.N01cFiniteParameterProducts

/-!
# Abstract finite-family collection of raw inverse bounds

All finite sums, zero-order identities and coefficient normalization
are proved over an abstract parameter space. Concrete current-data
adapters only supply the already proved scalar estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

private theorem n04PulledFieldsInverseRawBounds_coefficients
    {ι : Type*} [Fintype ι] (A : ι → ℝ) (hA : ∀ i, 0 < A i) :
    ∃ B : ℝ, 0 < B ∧ ∀ i E, 1 ≤ E → A i * E ^ A i ≤ B * E ^ B := by
  classical
  let B : ℝ := 1 + ∑ i, A i
  have hB : 0 < B := by
    have hs : 0 ≤ ∑ i, A i := Finset.sum_nonneg (fun i _ => (hA i).le)
    dsimp only [B]
    linarith
  refine ⟨B, hB, fun i E hE => ?_⟩
  have hi : A i ≤ B :=
    (Finset.single_le_sum (fun j _ => (hA j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  exact mul_le_mul hi (Real.rpow_le_rpow_of_exponent_le hE hi)
    (Real.rpow_nonneg (zero_le_one.trans hE) _) hB.le

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

private theorem n04PulledFieldsInverseRawBounds_zero_weight
    {U : Set X} {f : X → ℝ} (J : SmoothDirections U f)
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (base low high : ℕ)
    (horder : low ≤ high) {x : X} (hx : x ∈ U) (v : Fin 0 → X)
    {A E H M : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E) (hM : 0 ≤ M) (hHM : H ≤ M)
    (hraw : |f x| ≤ A * E ^ A * (1 + H * p low x)) :
    |J.D 0 x v| ≤ (A * (1 + M)) * E ^ A * parameterHeightWeight H 0 *
      oneHighVariationWeight p base high x v := by
  have hmul := mul_le_mul hHM (hp horder x) (apply_nonneg (p low) x) hM
  have hweight : 1 + H * p low x ≤ (1 + M) * (1 + p high x) := by
    nlinarith [apply_nonneg (p high) x]
  have hv : v = Fin.elim0 := funext (fun i => i.elim0)
  rw [hv, J.zero x hx]
  simp only [parameterHeightWeight, if_pos rfl, ite_true, oneHighVariationWeight,
    Fin.prod_univ_zero, Fin.sum_univ_zero, mul_one, add_zero]
  exact (hraw.trans (mul_le_mul_of_nonneg_left hweight
    (mul_nonneg hA (Real.rpow_nonneg hE _)))).trans_eq (by ring)

/-- Collect a finite family before interpolation. The supplied functions
and their genuine directional towers are left unchanged. -/
theorem n04PulledFields_inverseRawBounds_oneHigh
    {ι : Type*} [Fintype ι] {Ω : Set PolarPoint} {U : Set X}
    {f : ι → ℕ → ℕ → ℕ → Ω → X → ℝ}
    (J : ∀ i m a b q, SmoothDirections U (f i m a b q))
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (base : ℕ)
    (E H : ℕ → ℝ) (hE : ∀ m, 1 ≤ E m) (hH : ∀ m, 0 ≤ H m)
    {M : ℝ} (hM : 0 ≤ M) (hHM : ∀ m, H m ≤ M)
    (hzero : ∀ i, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ x ∈ U, ∀ m (q : Ω) (a b : ℕ), a + b ≤ s →
        |f i m a b q x| ≤ B * E m ^ B * (1 + H m * p (s + d) x))
    (hpositive : ∀ i k, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      (0 < k → ∀ x ∈ U, ∀ v : Fin k → X, ∀ m (q : Ω) (a b : ℕ), a + b ≤ s →
        |(J i m a b q).D k x v| ≤ B * E m ^ B * H m *
          oneHighVariationWeight p base (s + d) x v)) :
    ∃ L : ℕ → ℕ, ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i m (q : Ω) (a b : ℕ), a + b = s → 0 < k + s →
      ∀ x ∈ U, ∀ v : Fin k → X,
        |(J i m a b q).D k x v| ≤ B * E m ^ B * parameterHeightWeight (H m) k *
          oneHighVariationWeight p base ((if k = 0 then s - 1 else s) + L k) x v := by
  classical
  let d₀ (i : ι) : ℕ := (hzero i).choose
  let d (k : ℕ) (i : ι) : ℕ := (hpositive i k).choose
  let L : ℕ → ℕ := fun k => if k = 0 then (∑ i, d₀ i) + 1 else ∑ i, d k i
  refine ⟨L, fun k s => ?_⟩
  by_cases hk : k = 0
  · subst k
    let A (i : ι) : ℝ := ((hzero i).choose_spec s).choose
    have hA (i : ι) : 0 < A i := ((hzero i).choose_spec s).choose_spec.1
    obtain ⟨A₀, hA₀, hAA⟩ := n04PulledFieldsInverseRawBounds_coefficients A hA
    obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (A₀ * (1 + M)) A₀
    refine ⟨B, hB, fun i m q a b hab hpositive x hx v => ?_⟩
    have hd : d₀ i ≤ ∑ j, d₀ j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hL : L 0 = (∑ j, d₀ j) + 1 := if_pos rfl
    have hindex : (if (0 : ℕ) = 0 then s - 1 else s) + L 0 = s + ∑ j, d₀ j := by
      rw [if_pos rfl, hL]
      omega
    rw [hindex]
    have hraw := ((hzero i).choose_spec s).choose_spec.2 x hx m q a b hab.le
    have hz := n04PulledFieldsInverseRawBounds_zero_weight (J i m a b q) p hp base
      (s + d₀ i) (s + ∑ j, d₀ j) (Nat.add_le_add_left hd s) hx v
      (hA i).le (zero_le_one.trans (hE m)) hM (hHM m) hraw
    have hcoef : (A i * (1 + M)) * E m ^ A i ≤ B * E m ^ B := by
      calc
        _ = (A i * E m ^ A i) * (1 + M) := by ring
        _ ≤ (A₀ * E m ^ A₀) * (1 + M) :=
          mul_le_mul_of_nonneg_right (hAA i _ (hE m)) (add_nonneg zero_le_one hM)
        _ = (A₀ * (1 + M)) * E m ^ A₀ := by ring
        _ ≤ _ := hpack _ (hE m)
    exact hz.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (parameterHeightWeight_nonneg (hH m) 0))
      (oneHighVariationWeight_nonneg p base (s + ∑ j, d₀ j) x v))
  · let A (i : ι) : ℝ := ((hpositive i k).choose_spec s).choose
    have hA (i : ι) : 0 < A i := ((hpositive i k).choose_spec s).choose_spec.1
    obtain ⟨B, hB, hAB⟩ := n04PulledFieldsInverseRawBounds_coefficients A hA
    refine ⟨B, hB, fun i m q a b hab _ x hx v => ?_⟩
    have hd : d k i ≤ ∑ j, d k j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hindex : (if k = 0 then s - 1 else s) + L k = s + ∑ j, d k j := by
      simp only [L, if_neg hk]
    rw [hindex]
    simp only [parameterHeightWeight, if_neg hk]
    have hraw := ((hpositive i k).choose_spec s).choose_spec.2 (Nat.pos_of_ne_zero hk)
      x hx v m q a b hab.le
    have hw := oneHighVariationWeight_mono hp (base := base) le_rfl
      (Nat.add_le_add_left hd s) x v
    have hc : 0 ≤ A i * E m ^ A i * H m :=
      mul_nonneg (mul_nonneg (hA i).le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)) (hH m)
    exact hraw.trans ((mul_le_mul_of_nonneg_left hw hc).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hAB i _ (hE m)) (hH m))
        (oneHighVariationWeight_nonneg p base (s + ∑ j, d k j) x v)))

variable [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Join the abstract scalar collection to the genuine joint towers.
This theorem keeps the concrete graded parameter representation opaque. -/
theorem n04PulledFields_inverseRawBounds_pureWord
    {ι : Type*} [Fintype ι] {U : Set X} {I : Set ℝ}
    {f : ι → X → ℕ → PolarPoint → ℝ}
    (RF : ∀ i m, MixedJetRegularity U (I ×ˢ (univ : Set ℝ)) (fun x => f i x m))
    (hU : IsOpen U) (hcU : Convex ℝ U) (hI : IsOpen I) (hcI : Convex ℝ I)
    (hb : ∀ i m a b, UniformScalarJetSeminormBounds
      (fun q : I ×ˢ (univ : Set ℝ) => (RF i m).parameter a b q.val q.property))
    (J : ∀ i m, SmoothDirections (U ×ˢ (I ×ˢ (univ : Set ℝ)))
      (fun z : X × PolarPoint => f i z.1 m z.2))
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hinterp : HasInterpolation p) (base : ℕ)
    (E H : ℕ → ℝ) (hE : ∀ m, 1 ≤ E m) (hH : ∀ m, 0 ≤ H m)
    {M : ℝ} (hM : 0 ≤ M) (hHM : ∀ m, H m ≤ M)
    (hzero : ∀ i, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ x ∈ U, ∀ m (q : I ×ˢ (univ : Set ℝ)) (a b : ℕ), a + b ≤ s →
        |mixedDerivative a b (f i x m) q.val| ≤
          B * E m ^ B * (1 + H m * p (s + d) x))
    (hpositive : ∀ i k, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      (0 < k → ∀ x ∈ U, ∀ v : Fin k → X,
      ∀ m (q : I ×ˢ (univ : Set ℝ)) (a b : ℕ), a + b ≤ s →
        |((RF i m).parameter a b q.val q.property).D k x v| ≤ B * E m ^ B * H m *
          oneHighVariationWeight p base (s + d) x v)) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ N : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i m (x : X), x ∈ U → p low x ≤ 1 →
      ∀ q ∈ I ×ˢ (univ : Set ℝ), ∀ R : ℝ, 1 ≤ R → p (low + N + shift * K + 1) x ≤ R →
      ∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → X × PolarPoint,
      (∀ j, p low (v j).1 ≤ 1) → (∀ j, p (low + N + shift * K + 1) (v j).1 ≤ R) →
      (∀ j, ‖(v j).2‖ ≤ 1) →
      (∀ j, w.isState j = false → (v j).1 = 0) →
      (∀ j, w.isState j = true → (v j).2 = 0) →
        |(J i m).D n (x, q) v| ≤ B * E m ^ B * parameterHeightWeight (H m) w.stateArity *
          (R ^ (1 / (((N + shift * K : ℕ) : ℝ) + 1))) ^
            (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + shift * K) := by
  let data := n04PulledFields_inverseRawBounds_oneHigh
    (fun i m a b q => (RF i m).parameter a b q.val q.property)
    p hp base E H hE hH hM hHM hzero hpositive
  let L : ℕ → ℕ := data.choose
  have hjet := data.choose_spec
  let bounds := n04PulledFields_inversePrefix_pureWord
    (ι := ι × ℕ) (fun i => RF i.1 i.2) hU hcU hI hcI
    (fun i => hb i.1 i.2) (fun i => J i.1 i.2) p hp hinterp base L
    (fun i => E i.2) (fun i => H i.2) (fun i => hE i.2) (fun i => hH i.2)
    (fun k s => ⟨(hjet k s).choose, (hjet k s).choose_spec.1,
      fun i q a b hab hpositive x hx v =>
        (hjet k s).choose_spec.2 i.1 i.2 q a b hab hpositive x hx v⟩)
  refine ⟨bounds.choose, bounds.choose_spec.1, fun K => ?_⟩
  let hk := bounds.choose_spec.2 K
  refine ⟨hk.choose, fun N => ?_⟩
  let hN := hk.choose_spec N
  exact ⟨hN.choose, hN.choose_spec.1, fun i m => hN.choose_spec.2 (i, m)⟩

end ContinuousFlexibility.Analysis
