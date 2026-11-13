import ContinuousFlexibility.Analysis.N04PulledFieldsRawPrefix
import ContinuousFlexibility.Analysis.N04PulledFieldsInversePrefixSlots

/-!
# Common raw losses for a finite family of geometry atoms

The losses are collected before interpolation. The zeroth parameter
loss is the finite sum of the raw spatial losses, plus one; each positive
parameter loss is a separate finite sum. Thus the low interpolation
order can be shared by both inverse coordinates without depending on
the eventual parameter prefix.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem n04PulledFieldsInverseRawFamily_coefficients
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

private theorem n04PulledFieldsInverseRawFamily_zero_weight
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
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
  rw [smoothDirections_D_zero_apply J hx v]
  simp only [parameterHeightWeight, if_pos rfl, oneHighVariationWeight,
    Fin.prod_univ_zero, Fin.sum_univ_zero, mul_one, add_zero]
  exact (hraw.trans (mul_le_mul_of_nonneg_left hweight
    (mul_nonneg hA (Real.rpow_nonneg hE _)))).trans_eq (by ring)

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- The same current data supply the common raw input of the scalar
prefix theorem. No composed-field estimate is a premise. -/
theorem n04PulledFields_currentData_rawFamily_oneHigh
    {ι : Type*} [Fintype ι]
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : ι → Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ι → ℕ → PolarPoint → ℝ}
    (hdata : ∀ i, CurrentJetDataOn S T cell (fun _ => True) base ε (f i) (f₀ i))
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    {M : ℝ} (hM : 0 ≤ M)
    (hHM : ∀ m, T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ M)
    (hreg : ∀ i m, ContDiffOn ℝ ∞ (f₀ i m) unitStrip)
    (href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i m, ∀ (q : unitStrip) (a b : ℕ),
      a + b ≤ s → |mixedDerivative a b (f₀ i m) q.val| ≤
        B * T.E0 (T.sample (cell m)) ^ B)
    (RF : ∀ i m, MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
      (fun z => f i z m)) :
    ∃ L : ℕ → ℕ, ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i m (q : unitStrip) (a b : ℕ), a + b = s → 0 < k + s →
      ∀ x ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        |((RF i m).parameter a b q.val q.property).D k x v| ≤
          B * T.E0 (T.sample (cell m)) ^ B *
            parameterHeightWeight (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) k *
              oneHighVariationWeight (parameterGrading S) base
                ((if k = 0 then s - 1 else s) + L k) x v := by
  classical
  have hp := n07aParameterGrading_monotone S
  let Z (i : ι) := n04PulledFields_currentData_rawSpatial (hdata i) hE hH
    (fun m _ => hreg i m)
    (fun s => ⟨(href s).choose, (href s).choose_spec.1,
      fun m _ q a b hab => (href s).choose_spec.2 i m q a b hab⟩)
  let P (i : ι) (k : ℕ) :=
    n04PulledFields_currentData_rawPositive_prefix (hdata i) hE hH (hreg i) (RF i) k
  let d₀ (i : ι) : ℕ := (Z i).choose
  let d (k : ℕ) (i : ι) : ℕ := (P i k).choose
  let L : ℕ → ℕ := fun k => if k = 0 then (∑ i, d₀ i) + 1 else ∑ i, d k i
  refine ⟨L, fun k s => ?_⟩
  by_cases hk : k = 0
  · subst k
    let A (i : ι) : ℝ := ((Z i).choose_spec s).choose
    have hA (i : ι) : 0 < A i := ((Z i).choose_spec s).choose_spec.1
    obtain ⟨A₀, hA₀, hAA⟩ := n04PulledFieldsInverseRawFamily_coefficients A hA
    obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (A₀ * (1 + M)) A₀
    refine ⟨B, hB, fun i m q a b hab hpositive x hx v => ?_⟩
    have hd : d₀ i ≤ ∑ j, d₀ j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hindex : (if (0 : ℕ) = 0 then s - 1 else s) + L 0 = s + ∑ j, d₀ j := by
      simp only [L, if_pos rfl]
      omega
    rw [hindex]
    have hraw := ((Z i).choose_spec s).choose_spec.2 x hx m trivial q a b hab.le
    have hz := n04PulledFieldsInverseRawFamily_zero_weight
      ((RF i m).parameter a b q.val q.property) (parameterGrading S) hp base
      (s + d₀ i) (s + ∑ j, d₀ j) (Nat.add_le_add_left hd s) hx v
      (hA i).le (zero_le_one.trans (hE m)) hM (hHM m) hraw
    have hcoef : (A i * (1 + M)) * T.E0 (T.sample (cell m)) ^ A i ≤
        B * T.E0 (T.sample (cell m)) ^ B := by
      calc
        _ = (A i * T.E0 (T.sample (cell m)) ^ A i) * (1 + M) := by ring
        _ ≤ (A₀ * T.E0 (T.sample (cell m)) ^ A₀) * (1 + M) :=
          mul_le_mul_of_nonneg_right (hAA i _ (hE m)) (add_nonneg zero_le_one hM)
        _ = (A₀ * (1 + M)) * T.E0 (T.sample (cell m)) ^ A₀ := by ring
        _ ≤ _ := hpack _ (hE m)
    exact hz.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef
        (parameterHeightWeight_nonneg (Real.rpow_nonneg (hH m) _) 0))
      (oneHighVariationWeight_nonneg (parameterGrading S) base (s + ∑ j, d₀ j) x v))
  · let A (i : ι) : ℝ := ((P i k).choose_spec s).choose
    have hA (i : ι) : 0 < A i := ((P i k).choose_spec s).choose_spec.1
    obtain ⟨B, hB, hAB⟩ := n04PulledFieldsInverseRawFamily_coefficients A hA
    refine ⟨B, hB, fun i m q a b hab _ x hx v => ?_⟩
    have hd : d k i ≤ ∑ j, d k j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hindex : (if k = 0 then s - 1 else s) + L k = s + ∑ j, d k j := by
      simp only [L, if_neg hk]
    rw [hindex]
    simp only [parameterHeightWeight, if_neg hk]
    have hraw := ((P i k).choose_spec s).choose_spec.2 k le_rfl (Nat.pos_of_ne_zero hk)
      x hx v m q a b hab.le
    have hw := oneHighVariationWeight_mono hp (base := base) le_rfl
      (Nat.add_le_add_left hd s) x v
    have hh : 0 ≤ T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (hH m) _
    have hc : 0 ≤ A i * T.E0 (T.sample (cell m)) ^ A i *
        T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) :=
      mul_nonneg (mul_nonneg (hA i).le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)) hh
    exact hraw.trans ((mul_le_mul_of_nonneg_left hw hc).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hAB i _ (hE m)) hh)
        (oneHighVariationWeight_nonneg (parameterGrading S) base (s + ∑ j, d k j) x v)))

/-- The finite family uses one common low order and one common power
scale. The given joint towers are retained by uniqueness. -/
theorem n04PulledFields_currentData_rawFamily_pureWord
    {ι : Type*} [Fintype ι]
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : ι → Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ι → ℕ → PolarPoint → ℝ}
    (hdata : ∀ i, CurrentJetDataOn S T cell (fun _ => True) base ε (f i) (f₀ i))
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    {M : ℝ} (hM : 0 ≤ M)
    (hHM : ∀ m, T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ M)
    (hreg : ∀ i m, ContDiffOn ℝ ∞ (f₀ i m) unitStrip)
    (href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i m, ∀ (q : unitStrip) (a b : ℕ),
      a + b ≤ s → |mixedDerivative a b (f₀ i m) q.val| ≤
        B * T.E0 (T.sample (cell m)) ^ B)
    (RF : ∀ i m, MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
      (fun z => f i z m))
    (J : ∀ i m, SmoothDirections (sectorNeighborhood S base ε ε ×ˢ unitStrip)
      (fun z : Parameter S × PolarPoint => f i z.1 m z.2))
    (hinterp : HasInterpolation (parameterGrading S)) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ N : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i m (x : Parameter S), x ∈ sectorNeighborhood S base ε ε → parameterGrading S low x ≤ 1 →
      ∀ q ∈ unitStrip, ∀ R : ℝ, 1 ≤ R → parameterGrading S (low + N + shift * K + 1) x ≤ R →
      ∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → Parameter S × PolarPoint,
      (∀ j, parameterGrading S low (v j).1 ≤ 1) →
      (∀ j, parameterGrading S (low + N + shift * K + 1) (v j).1 ≤ R) →
      (∀ j, ‖(v j).2‖ ≤ 1) →
      (∀ j, w.isState j = false → (v j).1 = 0) →
      (∀ j, w.isState j = true → (v j).2 = 0) →
        |(J i m).D n (x, q) v| ≤ B * T.E0 (T.sample (cell m)) ^ B *
          parameterHeightWeight (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) w.stateArity *
            (R ^ (1 / (((N + shift * K : ℕ) : ℝ) + 1))) ^
              (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + shift * K) := by
  letI : IsTopologicalAddGroup (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).continuousSMul
  obtain ⟨L, hjet⟩ := n04PulledFields_currentData_rawFamily_oneHigh
    hdata hE hH hM hHM hreg href RF
  have hbound := n04PulledFields_inversePrefix_pureWord
    (ι := ι × ℕ) (fun i => RF i.1 i.2)
    (isOpen_sectorNeighborhood S base ε ε) (sectorNeighborhood_convex S base ε ε)
    isOpen_Ioo (convex_Ioo (0 : ℝ) 1)
    (fun i a b => n04PulledFields_currentData_rawMixed_uniform (hdata i.1) hE hH (hreg i.1)
      (fun s => ⟨(href s).choose, (href s).choose_spec.1,
        fun m q a b hab => (href s).choose_spec.2 i.1 m q a b hab⟩)
      i.2 a b (RF i.1 i.2))
    (fun i => J i.1 i.2) (parameterGrading S) (n07aParameterGrading_monotone S)
    hinterp base L (fun i => T.E0 (T.sample (cell i.2)))
    (fun i => T.H (T.sample (cell i.2)) ^ (3 / 4 : ℝ))
    (fun i => hE i.2) (fun i => Real.rpow_nonneg (hH i.2) _)
    (fun k s => ⟨(hjet k s).choose, (hjet k s).choose_spec.1,
      fun i q a b hab hpositive x hx v =>
        (hjet k s).choose_spec.2 i.1 i.2 q a b hab hpositive x hx v⟩)
  refine ⟨hbound.choose, hbound.choose_spec.1, fun K => ?_⟩
  let hk := hbound.choose_spec.2 K
  refine ⟨hk.choose, fun N => ?_⟩
  let hN := hk.choose_spec N
  exact ⟨hN.choose, hN.choose_spec.1, fun i m => hN.choose_spec.2 (i, m)⟩

end ContinuousFlexibility.Analysis
