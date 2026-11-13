import ContinuousFlexibility.Analysis.N04PrincipalDividedValue

/-!
# Abstract transport of current data through cubic division

This interface leaves the parameter space, grading, open domain and
sample envelopes abstract. The quotient tower is constructed on every
piece, with a zero tower outside the pieces carrying the numerator.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

variable {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- The scalar current-data shape with an arbitrary external weight. -/
def N04PrincipalDividedCoreData (p : ℕ → Seminorm ℝ X) (U : Set X)
    (E H : ι → ℝ) (P : ι → Prop) (base : ℕ)
    (f : X → ι → PolarPoint → ℝ) (f₀ : ι → PolarPoint → ℝ) : Prop :=
  (∀ z ∈ U, ∀ m, P m → ContDiffOn ℝ ∞ (f z m) unitStrip ∧
    ∀ q ∈ unitStrip, f z m (q + (0, Real.pi)) = f z m q) ∧
  ∃ J : ∀ m (a b : ℕ) (q : unitStrip), SmoothDirections U
      (fun z => mixedDerivative a b (fun y => f z m y - f₀ m y) q.val),
    (∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ U, ∀ m, P m → ∀ (q : unitStrip) (a b : ℕ), a + b ≤ s →
        |mixedDerivative a b (fun y => f z m y - f₀ m y) q.val| ≤
          B * E m ^ B * H m * p (s + loss) z) ∧
    ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ U, ∀ v : Fin k → X, ∀ m, P m →
        ∀ (q : unitStrip) (a b : ℕ), a + b ≤ s →
          |(J m a b q).D k z v| ≤
            B * E m ^ B * H m * oneHighVariationWeight p base (s + loss) z v

/-- Genuine endpoint representatives transfer both current value bounds
and all parameter towers to the cubic quotient on the same domain. -/
theorem n04PrincipalDivided_coreData
    (p : ℕ → Seminorm ℝ X) (hp : WithSeminorms p) (hmono : Monotone p)
    {U : Set X} (hU : IsOpen U) (E H : ι → ℝ) (P : ι → Prop) (base : ℕ)
    {f g : X → ι → PolarPoint → ℝ} {f₀ : ι → PolarPoint → ℝ}
    (h : N04PrincipalDividedCoreData p U E H P base f f₀)
    (href : ∀ m, ContDiffOn ℝ ∞ (f₀ m) unitStrip ∧
      ∀ q ∈ unitStrip, f₀ m (q + (0, Real.pi)) = f₀ m q)
    (hE : ∀ m, 1 ≤ E m) (hH : ∀ m, 0 ≤ H m)
    (hrep : ∀ m, P m → ∀ z ∈ U,
      ∃ F : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧
        EqOn F (fun q => f z m q - f₀ m q) unitStrip ∧
        ∀ c : Bool, ∀ θ i, i ≤ 2 →
          iteratedDeriv i (fun t : ℝ => F (t, θ)) (if c then 1 else 0) = 0)
    (hfactor : ∀ m, P m → ∀ z ∈ U, ∀ q ∈ unitStrip,
      f z m q - f₀ m q = (q.1 * (1 - q.1)) ^ 3 * g z m q)
    (hzero : ∀ m, ¬ P m → ∀ z ∈ U, EqOn (g z m) (fun _ => 0) unitStrip) :
    N04PrincipalDividedCoreData p U E H (fun _ => True) base g (fun _ _ => 0) := by
  classical
  let I : Type _ := {m : ι // P m}
  let N : I → X → PolarPoint → ℝ := fun m z q => f z m.val q - f₀ m.val q
  let RN : ∀ m : I, MixedJetRegularity U unitStrip (N m) := fun m =>
    { spatial := fun z hz => (h.1 z hz m.val m.property).1.sub (href m.val).1
      parameter := fun a b q hq => h.2.choose m.val a b ⟨q, hq⟩ }
  have hnum : ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m : I, ∀ a b, a + b ≤ s → ∀ q (hq : q ∈ unitStrip),
      ∀ z ∈ U, ∀ v : Fin k → X,
        |((RN m).parameter a b q hq).D k z v| ≤
          B * E m.val ^ B *
            H m.val *
              oneHighVariationWeight p base (s + loss) z v := by
    intro k
    have ht := h.2.choose_spec.2 k
    refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
      (ht.choose_spec s).choose_spec.1, ?_⟩⟩
    intro m a b hab q hq z hz v
    exact (ht.choose_spec s).choose_spec.2 z hz v m.val m.property ⟨q, hq⟩ a b hab
  have hout := n04Realization_unitCubic_oneHigh_bounds hU
    p hp hmono base
    (fun m : I => E m.val)
    (fun m : I => H m.val)
    (fun _ : I => (1 : ℝ)) (fun m => hE m.val)
    (fun m => hH m.val) (fun _ => zero_lt_one)
    (bw := 1) zero_lt_one
    (fun m => by simpa only [inv_one, Real.rpow_one, one_mul] using hE m.val)
    N (fun m z => g z m.val) RN
    (fun m => hrep m.val m.property)
    (fun m z hz q hq => by
      simpa only [one_pow, one_mul] using hfactor m.val m.property z hz q hq) hnum
  let RE : ∀ m : I, MixedJetRegularity U unitStrip (fun z => g z m.val) := hout.choose
  have hRE := hout.choose_spec
  have hnegJet (m : ι) (hm : ¬ P m) (a b : ℕ) (q : unitStrip)
      (z : X) (hz : z ∈ U) :
      mixedDerivative a b (fun y => g z m y - 0) q.val = 0 := by
    simp only [sub_zero]
    calc
      mixedDerivative a b (g z m) q.val =
          mixedDerivative a b (fun _ : PolarPoint => (0 : ℝ)) q.val :=
        mixedDerivative_eq_of_eqOn_radialCylinder
          (fun r hr θ => hzero m hm z hz ⟨hr, mem_univ _⟩) a b q.property.1
      _ = 0 := by simp [mixedDerivative]
  let J : ∀ m (a b : ℕ) (q : unitStrip), SmoothDirections U
      (fun z => mixedDerivative a b (fun y => g z m y - 0) q.val) := fun m a b q =>
    if hm : P m then
      ((RE ⟨m, hm⟩).parameter a b q.val q.property).congr
        (fun _ _ => by simp only [sub_zero])
    else (smoothDirections_constant hU (0 : ℝ)).congr
      (fun z hz => (hnegJet m hm a b q z hz).symm)
  have hJDpos (m : ι) (hm : P m) (a b : ℕ) (q : unitStrip)
      (k : ℕ) (z : X) (hz : z ∈ U) (v : Fin k → X) :
      (J m a b q).D k z v = ((RE ⟨m, hm⟩).parameter a b q.val q.property).D k z v := by
    simp only [J, dif_pos hm, SmoothDirections.congr]
  have hJDneg (m : ι) (hm : ¬ P m) (a b : ℕ) (q : unitStrip)
      (k : ℕ) (z : X) (hz : z ∈ U) (v : Fin k → X) :
      (J m a b q).D k z v = 0 := by
    have he := n04Realization_smoothDirections_D_const_mul
      (J m a b q) (J m a b q) 0
      (fun y hy => by rw [hnegJet m hm a b q y hy, zero_mul]) k hz v
    simpa only [zero_mul] using he
  refine ⟨?_, J, ?_, ?_⟩
  · intro z hz m _
    have hshift (q : PolarPoint) (hq : q ∈ unitStrip) :
        q + (0, Real.pi) ∈ unitStrip := by
      refine ⟨?_, mem_univ _⟩
      change q.1 + 0 ∈ Ioo (0 : ℝ) 1
      rw [add_zero]
      exact hq.1
    by_cases hm : P m
    · refine ⟨(RE ⟨m, hm⟩).spatial z hz, ?_⟩
      intro q hq
      have hn : (q.1 * (1 - q.1)) ^ 3 ≠ 0 :=
        pow_ne_zero 3 (mul_pos hq.1.1 (sub_pos.mpr hq.1.2)).ne'
      apply mul_left_cancel₀ hn
      have hf1 := hfactor m hm z hz (q + (0, Real.pi)) (hshift q hq)
      have hf0 := hfactor m hm z hz q hq
      simpa only [Prod.fst_add, add_zero, (h.1 z hz m hm).2 q hq,
        (href m).2 q hq, hf0] using hf1.symm
    · refine ⟨contDiffOn_const.congr (fun q hq => hzero m hm z hz hq), ?_⟩
      intro q hq
      exact (hzero m hm z hz (hshift q hq)).trans (hzero m hm z hz hq).symm
  · exact n04PrincipalDivided_valueBounds
      (fun n z => p n z) (fun n z => apply_nonneg _ _)
      (fun m => E m)
      (fun m => H m)
      (fun m => zero_le_one.trans (hE m)) hH
      P (fun z m q => f z m q - f₀ m q) g h.2.choose_spec.1 hrep hfactor
      (fun m hm z hz q a b => hnegJet m hm a b q z hz)
  · intro k
    have ht := hRE k
    refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
      (ht.choose_spec s).choose_spec.1, ?_⟩⟩
    intro z hz v m _ q a b hab
    by_cases hm : P m
    · rw [hJDpos m hm a b q k z hz v]
      exact (ht.choose_spec s).choose_spec.2 ⟨m, hm⟩ a b hab q.val q.property z hz v
    · rw [hJDneg m hm a b q k z hz v, abs_zero]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (ht.choose_spec s).choose_spec.1.le
          (Real.rpow_nonneg (zero_le_one.trans (hE m)) _))
          (hH m)) (oneHighVariationWeight_nonneg _ _ _ _ _)
end ContinuousFlexibility.Analysis
