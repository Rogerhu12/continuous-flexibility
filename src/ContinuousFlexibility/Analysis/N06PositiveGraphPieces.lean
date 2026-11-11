import ContinuousFlexibility.Analysis.N06GraphMaterialBounds
import ContinuousFlexibility.Analysis.N06MaterialJetRows

/-!
# All positive canonical graph fields in the original weighted lp space

Only actual positive pieces carry graph fields. Negative pieces are zero.
The physical source and height rows retain their original material weights;
E0^A is placed on the graph fields to compensate the normalized cubic
coefficient used by the original volume-source construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

abbrev N06PositiveWeakGraphFamily
    {S : PhysicalSpacesData} (T : MaterialData) (K : CanonicalData S)
    (β loss : ℝ) {b : ℕ} (F W : CanonicalVolumeJets S K b)
    (a c V : ℕ → ℝ → ℝ) (κ : ℕ → ℝ) :=
  ∀ m, K.positive m = true → N06UnitWeakGraphData (a m) (c m) (V m)
    (n06MaterialJetRow T K β (-loss) W m) (n06MaterialJetRow T K β 0 F m) (κ m)

variable {S : PhysicalSpacesData} {T : MaterialData} {K : CanonicalData S}
  {β loss : ℝ} {b : ℕ} {F W : CanonicalVolumeJets S K b}
  {a c V : ℕ → ℝ → ℝ} {κ : ℕ → ℝ}

/-- The original physical five fields, with the actual negative-piece mask. -/
def n06PositivePhysicalGraphFields (P : N06PositiveWeakGraphFamily T K β loss F W a c V κ)
    (r : Fin 5) (m : ℕ) : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m) :=
  if h : K.positive m = true then (P m h).field r else 0

theorem n06PositivePhysicalGraphFields_of_positive
    (P : N06PositiveWeakGraphFamily T K β loss F W a c V κ)
    (r : Fin 5) (m : ℕ) (hm : K.positive m = true) :
    n06PositivePhysicalGraphFields P r m = (P m hm).field r := by
  simp only [n06PositivePhysicalGraphFields, dif_pos hm]

theorem n06PositivePhysicalGraphFields_of_not_positive
    (P : N06PositiveWeakGraphFamily T K β loss F W a c V κ)
    (r : Fin 5) (m : ℕ) (hm : K.positive m ≠ true) :
    n06PositivePhysicalGraphFields P r m = 0 := by
  simp only [n06PositivePhysicalGraphFields, dif_neg hm]

theorem n06PositivePhysicalGraphFields_weak
    (P : N06PositiveWeakGraphFamily T K β loss F W a c V κ)
    (r : Fin 5) (m : ℕ) (j : Fin (b + 1)) :
    WeakCanonicalAngularDerivative S K m
      (n06PositivePhysicalGraphFields P r m 0) (n06PositivePhysicalGraphFields P r m j) j.val := by
  by_cases hm : K.positive m = true
  · rw [n06PositivePhysicalGraphFields_of_positive P r m hm]
    exact (P m hm).weakAngular r j
  · rw [n06PositivePhysicalGraphFields_of_not_positive P r m hm]
    exact WeakCanonicalAngularDerivative.n06_zero j.val

theorem n06_canonical_zero_reflection (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (σ : ℝ) :
    (fun p : PolarPoint => (0 : CanonicalL2 S K m) (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] fun p => σ * (0 : CanonicalL2 S K m) p := by
  have hz := Lp.coeFn_zero ℝ 2 (canonicalMeasure S K m)
  have hr := n06_measurePreserving_canonicalAngularReflection.quasiMeasurePreserving.ae_eq_comp hz
  filter_upwards [hr, hz] with p hpr hp
  simp only [Function.comp_apply, Pi.zero_apply] at hpr hp
  rw [hpr, hp, mul_zero]

theorem n06PositivePhysicalGraphFields_reflection
    (P : N06PositiveWeakGraphFamily T K β loss F W a c V κ) (r : Fin 5) (m : ℕ) :
    (fun p : PolarPoint => n06PositivePhysicalGraphFields P r m 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m]
        fun p => n06CubicGraphParity r * n06PositivePhysicalGraphFields P r m 0 p := by
  by_cases hm : K.positive m = true
  · rw [n06PositivePhysicalGraphFields_of_positive P r m hm]
    exact (P m hm).reflection r
  · rw [n06PositivePhysicalGraphFields_of_not_positive P r m hm]
    exact n06_canonical_zero_reflection S K m (n06CubicGraphParity r)

/-- A uniform material bound for every actual positive physical field row.
The constant is chosen before any source or modal representatives. -/
theorem n06_positiveGraphFields_material_bound
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (β A loss C : ℝ) (hβ : 0 < β) (hC : 0 < C)
    (a c V : ℕ → ℝ → ℝ) (κ : ℕ → ℝ)
    (hκ : ∀ m, K.positive m = true → 1 ≤ κ m)
    (hgrowth : ∀ m, K.positive m = true →
      κ m ≤ C * T.E0 (T.sample (K.cell m)) ^ C) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ F W : CanonicalVolumeJets S K b,
      ∀ P : N06PositiveWeakGraphFamily T K β loss F W a c V κ,
      ∀ r m,
        ‖T.E0 (T.sample (K.cell m)) ^ A • n06PositivePhysicalGraphFields P r m‖ ≤
          Q * (‖F m‖ + ‖W m‖) := by
  obtain ⟨Q, hQ, habsorb⟩ := n06_material_graph_row_absorb hT β A loss C hβ hC
  refine ⟨Q, hQ, ?_⟩
  intro F W P r m
  by_cases hm : K.positive m = true
  · have hs := spaces_trace_sample_mem hD hT (K.cell m)
    have hE : 0 ≤ T.E0 (T.sample (K.cell m)) ^ A :=
      Real.rpow_nonneg (hT.2.1 _ hs).2.2.1.le A
    have hK : 0 ≤ κ m := zero_le_one.trans (hκ m hm)
    calc
      _ = T.E0 (T.sample (K.cell m)) ^ A * ‖(P m hm).field r‖ := by
        rw [n06PositivePhysicalGraphFields_of_positive P r m hm, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg hE]
      _ ≤ T.E0 (T.sample (K.cell m)) ^ A *
          (128 * κ m ^ 5 *
            (‖n06MaterialJetRow T K β 0 F m‖ + ‖n06MaterialJetRow T K β (-loss) W m‖)) :=
        mul_le_mul_of_nonneg_left ((P m hm).field_norm_le hK r) hE
      _ = T.E0 (T.sample (K.cell m)) ^ A * (128 * κ m ^ 5) *
          T.H (T.sample (K.cell m)) ^ β *
            (‖F m‖ + T.M (T.sample (K.cell m)) ^ loss * ‖W m‖) := by
        rw [n06MaterialJetRow_norm hD hT β 0 F m,
          n06MaterialJetRow_norm hD hT β (-loss) W m]
        simp only [neg_zero, Real.rpow_zero, one_mul, neg_neg]
        ring
      _ ≤ Q * (‖F m‖ + ‖W m‖) :=
        habsorb _ hs (κ m) ‖F m‖ ‖W m‖ hK (hgrowth m hm) (norm_nonneg _) (norm_nonneg _)
  · rw [n06PositivePhysicalGraphFields_of_not_positive P r m hm, smul_zero, norm_zero]
    exact mul_nonneg hQ.le (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The five material-weighted physical graph fields lie in the original
canonical lp. Their weak jets and parity are retained on every piece. -/
theorem n06_positiveGraphFields_package
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (β A loss C : ℝ) (hβ : 0 < β) (hC : 0 < C)
    (a c V : ℕ → ℝ → ℝ) (κ : ℕ → ℝ)
    (hκ : ∀ m, K.positive m = true → 1 ≤ κ m)
    (hgrowth : ∀ m, K.positive m = true →
      κ m ≤ C * T.E0 (T.sample (K.cell m)) ^ C) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ F W : CanonicalVolumeJets S K b,
      ∀ P : N06PositiveWeakGraphFamily T K β loss F W a c V κ,
      ∃ f : Fin 5 → CanonicalVolumeJets S K b,
        (∀ r m, f r m = T.E0 (T.sample (K.cell m)) ^ A • n06PositivePhysicalGraphFields P r m) ∧
        (∀ r m j, WeakCanonicalAngularDerivative S K m (f r m 0) (f r m j) j.val) ∧
        (∀ r m, (fun p : PolarPoint => f r m 0 (p.1, Real.pi - p.2))
          =ᵐ[canonicalMeasure S K m] fun p => n06CubicGraphParity r * f r m 0 p) ∧
        (∀ r, ‖f r‖ ≤ Q * (‖F‖ + ‖W‖)) := by
  obtain ⟨Q, hQ, hlocal⟩ := n06_positiveGraphFields_material_bound
    hD hT β A loss C hβ hC a c V κ hκ hgrowth (b := b)
  refine ⟨Q, hQ, ?_⟩
  intro F W P
  choose f hf hnorm using fun r => n06_graphJets_of_piecewise_sum_bound F W
    (fun m => T.E0 (T.sample (K.cell m)) ^ A • n06PositivePhysicalGraphFields P r m)
    hQ.le (hlocal F W P r)
  refine ⟨f, hf, ?_, ?_, hnorm⟩
  · intro r m j
    rw [hf r m]
    simpa only [PiLp.smul_apply] using
      (n06PositivePhysicalGraphFields_weak P r m j).n06_smul (T.E0 (T.sample (K.cell m)) ^ A)
  · intro r m
    rw [hf r m]
    simpa only [PiLp.smul_apply] using
      n06_canonical_reflection_smul (n06CubicGraphParity r) (T.E0 (T.sample (K.cell m)) ^ A)
        (n06PositivePhysicalGraphFields P r m 0) (n06PositivePhysicalGraphFields_reflection P r m)

end ContinuousFlexibility.Analysis
