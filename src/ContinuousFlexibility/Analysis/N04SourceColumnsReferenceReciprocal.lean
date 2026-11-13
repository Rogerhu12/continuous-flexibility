import ContinuousFlexibility.Analysis.N04SourceColumnsReciprocal

/-!
# Scalar composition and reciprocals of reference families

The finite scalar chain rule acts on the actual mixed spatial jets.
A reciprocal value envelope supplies all higher scalar outer jets, so
inversion requires no independent higher derivative hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

/-- A fixed scalar composition preserves reference material envelopes
when its outer jets at the actual reference values have such envelopes. -/
theorem N04SourceReferenceData.sourceColumns_scalarComp
    {T : MaterialData} {cell : ℕ → ℕ} {f₀ : ℕ → PolarPoint → ℝ}
    (hf : N04SourceReferenceData T cell f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (g : ℝ → ℝ) (V : Set ℝ) (hV : IsOpen V)
    (hg : ContDiffOn ℝ ∞ g V) (hmap : ∀ m, MapsTo (f₀ m) unitStrip V)
    (houter : ∀ N : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ m q, q ∈ unitStrip →
      ∀ a b : ℕ, a + b ≤ N →
        ‖iteratedFDeriv ℝ a (iteratedDeriv b g) (f₀ m q)‖ ≤
          A * T.E0 (T.sample (cell m)) ^ A) :
    N04SourceReferenceData T cell (fun m q => g (f₀ m q)) := by
  classical
  refine ⟨fun m => ⟨hg.comp (hf.1 m).1 (hmap m),
    fun q hq => congrArg g ((hf.1 m).2 q hq)⟩, fun s => ?_⟩
  have ho := houter s
  have hi := hf.2 s
  choose C hC hCb using fun ij : Fin (s + 1) × Fin (s + 1) =>
    n04Realization_finiteScalarComposition_bound (X := ℝ) 0 ij.1.val ij.2.val 1
  let Q : ℝ := 1 + ∑ ij : Fin (s + 1) × Fin (s + 1), C ij
  have hQ : 1 ≤ Q := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun ij _ => zero_le_one.trans (hC ij)))
  have hCQ (ij : Fin (s + 1) × Fin (s + 1)) : C ij ≤ Q :=
    (Finset.single_le_sum (fun ij _ => zero_le_one.trans (hC ij))
      (Finset.mem_univ ij)).trans (le_add_of_nonneg_left zero_le_one)
  let P : ℝ := 1 + max ho.choose hi.choose
  have hP : 1 ≤ P := le_add_of_nonneg_right
    (ho.choose_spec.1.le.trans (le_max_left _ _))
  have hoP : ho.choose ≤ P := (le_max_left _ _).trans
    (le_add_of_nonneg_left zero_le_one)
  have hiP : hi.choose ≤ P := (le_max_right _ _).trans
    (le_add_of_nonneg_left zero_le_one)
  have hc := coefficientEnvelope_pack (Q * P ^ (s + 1)) (P * (s + 1 : ℕ))
  refine ⟨hc.choose, hc.choose_spec.1, ?_⟩
  intro m q hq a b hab
  let E : ℝ := T.E0 (T.sample (cell m))
  let M : ℝ := P * E ^ P
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hP
    (Real.one_le_rpow (hE m) (zero_le_one.trans hP))
  have hoM : ho.choose * E ^ ho.choose ≤ M :=
    mul_le_mul hoP (Real.rpow_le_rpow_of_exponent_le (hE m) hoP)
      (Real.rpow_nonneg (zero_le_one.trans (hE m)) _) (zero_le_one.trans hP)
  have hiM : hi.choose * E ^ hi.choose ≤ M :=
    mul_le_mul hiP (Real.rpow_le_rpow_of_exponent_le (hE m) hiP)
      (Real.rpow_nonneg (zero_le_one.trans (hE m)) _) (zero_le_one.trans hP)
  let RF : MixedJetRegularity (univ : Set ℝ) unitStrip (fun _ => f₀ m) :=
    n04Realization_mixedJetRegularity_fixedSpatial isOpen_univ (hf.1 m).1
  let J : SmoothDirections (univ : Set ℝ)
      (fun _ => mixedDerivative a b (fun p => g (f₀ m p)) q) :=
    smoothDirections_constant isOpen_univ _
  let ij : Fin (s + 1) × Fin (s + 1) :=
    (⟨a, by omega⟩, ⟨b, by omega⟩)
  have hb := hCb ij univ isOpen_univ unitStrip (isOpen_Ioo.prod isOpen_univ)
    V hV (fun _ : ℝ => f₀ m) g RF hg (fun _ _ => hmap m)
    q hq J 0 (mem_univ _) (fun _ => True) Fin.elim0 (fun i => i.elim0)
    1 M 1 zero_le_one le_rfl hM le_rfl
    (fun n hn j hj => (ho.choose_spec.2 m q hq j n (by omega)).trans hoM)
    (fun j hj u w huw z _ => by
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      have hsource := (hi.choose_spec.2 m q hq u w (huw.trans hab)).trans hiM
      simpa only [smoothDirections_D_zero_apply (RF.parameter u w q hq) (mem_univ _),
        Real.norm_eq_abs, parameterHeightWeight, if_pos rfl, one_pow, mul_one]
        using hsource)
  have hb' : |mixedDerivative a b (fun p => g (f₀ m p)) q| ≤
      C ij * M ^ (a + b + 1) := by
    simpa only [smoothDirections_D_zero_apply J (mem_univ _), Real.norm_eq_abs,
      Nat.zero_add, parameterHeightWeight, if_pos rfl, one_pow, mul_one] using hb
  have hbound : |mixedDerivative a b (fun p => g (f₀ m p)) q| ≤ Q * M ^ (s + 1) :=
    hb'.trans (mul_le_mul (hCQ ij) (pow_le_pow_right₀ hM (Nat.add_le_add_right hab 1))
      (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hQ))
  have hMp : M ^ (s + 1) = P ^ (s + 1) * E ^ (P * (s + 1 : ℕ)) := by
    dsimp only [M]
    rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans (hE m)) P (s + 1)]
  exact hbound.trans (by simpa only [hMp, mul_assoc] using hc.choose_spec.2 E (hE m))

/-- Reference reciprocals need only nonvanishing and their zeroth
reciprocal envelope; every higher mixed derivative is derived. -/
theorem N04SourceReferenceData.sourceColumns_inv
    {T : MaterialData} {cell : ℕ → ℕ} {f₀ : ℕ → PolarPoint → ℝ}
    (hf : N04SourceReferenceData T cell f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hne : ∀ m q, q ∈ unitStrip → f₀ m q ≠ 0)
    (hinv : ∃ A : ℝ, 0 < A ∧ ∀ m q, q ∈ unitStrip →
      |(f₀ m q)⁻¹| ≤ A * T.E0 (T.sample (cell m)) ^ A) :
    N04SourceReferenceData T cell (fun m q => (f₀ m q)⁻¹) := by
  let V : Set ℝ := {0}ᶜ
  have hV : IsOpen V := isClosed_singleton.isOpen_compl
  have hg : ContDiffOn ℝ ∞ (fun t : ℝ => t⁻¹) V :=
    contDiffOn_id.inv (fun t ht => ht)
  refine hf.sourceColumns_scalarComp hE (fun t : ℝ => t⁻¹) V hV hg
    (fun m q hq => hne m q hq) ?_
  obtain ⟨A, hA, hbound⟩ := hinv
  intro N
  obtain ⟨B, hB, hb⟩ := n04SourceColumns_inverse_abs_outer_envelope A A hA.le hA.le N
  exact ⟨B, hB, fun m q hq a b hab => hb _ _ (hE m) (hne m q hq)
    (hbound m q hq) a b hab⟩

end ContinuousFlexibility.Analysis
