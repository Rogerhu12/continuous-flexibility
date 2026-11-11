import ContinuousFlexibility.Radial.TailMassResistanceData

/-!
# Starting a deep tail at a later mass entrance

The shifted tail uses the same density and endpoint. Restricting to it
preserves the actual weighted square-integrability and the differential
equation. A positive shift places its entrance inside the original smooth
open interval.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def deepTailShift (T : DeepTailData) (k : ℕ) : DeepTailData where
  entrance := T.node k
  endpoint := T.endpoint
  p := T.p
  node := fun n => T.node (k + n)
  massEnd := fun n => T.massEnd (k + n)
  Λ := T.Λ
  η := T.η
  K := T.K

@[simp] theorem tailMass_deepTailShift (T : DeepTailData) (k n : ℕ) :
    tailMass (deepTailShift T k) n = tailMass T (k + n) := rfl

@[simp] theorem tailInnerResistance_deepTailShift (T : DeepTailData) (k n : ℕ) :
    tailInnerResistance (deepTailShift T k) n = tailInnerResistance T (k + n) := rfl

@[simp] theorem tailGapMass_deepTailShift (T : DeepTailData) (k n : ℕ) :
    tailGapMass (deepTailShift T k) n = tailGapMass T (k + n) := by
  simp only [tailGapMass, deepTailShift, Nat.add_assoc]

@[simp] theorem tailResistance_deepTailShift (T : DeepTailData) (k n : ℕ) :
    tailResistance (deepTailShift T k) n = tailResistance T (k + n) := by
  simp only [tailResistance, deepTailShift, Nat.add_assoc]

theorem deepTailHypotheses_shift {T : DeepTailData} (hT : DeepTailHypotheses T)
    (k : ℕ) : DeepTailHypotheses (deepTailShift T k) := by
  have hke := deepTail_node_lt_endpoint hT k
  have hek := deepTail_entrance_le_node hT k
  rcases hT with ⟨_, _, hΛ, _, hη, hη₁, hK, hp, hpos, hlim, he⟩
  refine ⟨hke, ?_, hΛ, Or.inl ?_, hη, hη₁, hK, ?_, ?_, ?_, ?_⟩
  · simp only [deepTailShift, Nat.add_zero, le_refl]
  · simp only [deepTailShift, Nat.add_zero]
  · apply hp.mono
    intro x hx
    exact ⟨hek.trans hx.1, hx.2⟩
  · intro x hx
    exact hpos x ⟨hek.trans hx.1, hx.2⟩
  · have hs : Tendsto (fun n : ℕ => k + n) atTop atTop := by
      simpa only [Nat.add_comm] using tendsto_add_atTop_nat k
    exact hlim.comp hs
  · intro n
    simpa only [deepTailShift, tailMass, tailInnerResistance, tailGapMass,
      tailResistance, Nat.add_assoc] using he (k + n)

theorem deepTailShift_interval_subset {T : DeepTailData} (hT : DeepTailHypotheses T)
    (k : ℕ) : Ioo (deepTailShift T k).entrance (deepTailShift T k).endpoint ⊆
      Ioo T.entrance T.endpoint := by
  intro x hx
  exact ⟨(deepTail_entrance_le_node hT k).trans_lt hx.1, hx.2⟩

/-- The shifted weighted measure is literally the restriction of the
original measure, with the same density. -/
theorem deepTailMeasure_shift {T : DeepTailData} (hT : DeepTailHypotheses T)
    (k : ℕ) : deepTailMeasure (deepTailShift T k) =
      (deepTailMeasure T).restrict (Ioo (T.node k) T.endpoint) := by
  change (volume.restrict (Ioo (T.node k) T.endpoint)).withDensity
      (fun x => ENNReal.ofReal (T.p x)) =
    ((volume.restrict (Ioo T.entrance T.endpoint)).withDensity
      (fun x => ENNReal.ofReal (T.p x))).restrict (Ioo (T.node k) T.endpoint)
  rw [restrict_withDensity measurableSet_Ioo,
    Measure.restrict_restrict_of_subset (deepTailShift_interval_subset hT k)]

theorem deepTailMeasure_shift_le {T : DeepTailData} (hT : DeepTailHypotheses T)
    (k : ℕ) : deepTailMeasure (deepTailShift T k) ≤ deepTailMeasure T := by
  rw [deepTailMeasure_shift hT k]
  exact Measure.restrict_le_self

/-- The original natural solution is a natural solution on every
positively shifted tail. No extension across the old entrance is used. -/
theorem tailNaturalEquation_shift {T : DeepTailData} (hT : DeepTailHypotheses T)
    {u : ℝ → ℝ} (hu : TailNaturalEquation T u) {k : ℕ} (hk : 0 < k) :
    TailNaturalEquation (deepTailShift T k) u := by
  have hkin : T.node k ∈ Ioo T.entrance T.endpoint :=
    ⟨hT.2.1.trans_lt (by simpa only [Nat.zero_add] using
      deepTail_node_strictMono hT hk), deepTail_node_lt_endpoint hT k⟩
  refine ⟨hu.2.1.contDiffAt (isOpen_Ioo.mem_nhds hkin),
    hu.2.1.mono (deepTailShift_interval_subset hT k),
    MemLp.mono_measure (deepTailMeasure_shift_le hT k) hu.2.2.1, ?_⟩
  intro x hx
  exact hu.2.2.2 x (deepTailShift_interval_subset hT k hx)

end ContinuousFlexibility.Radial
