import ContinuousFlexibility.Analysis.StateProfileRegularity

/-!
# Actual root germs from strict support certificates

Topological support inside each negative component excludes every reference
root. Local finiteness then supplies a single neighborhood on which all
controls vanish. A border supported in the positive region vanishes on a
neighborhood of the same root, so the actual exponential profile agrees
there with the reference profile for every state.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology BigOperators

/-- A locally finite family of supports has a common zero neighborhood at
a point outside each individual topological support. -/
theorem locallyFinite_support_eventually_zero {ι : Type*}
    {f : ι → ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : LocallyFinite (fun i => {y : U | (y : ℝ) ∈ Function.support (f i)}))
    {r : ℝ} (hr : r ∈ U) (hzero : ∀ i, r ∉ tsupport (f i)) :
    ∀ᶠ y in 𝓝 r, ∀ i, f i y = 0 := by
  obtain ⟨t, ht, hfinite⟩ := hf ⟨r, hr⟩
  have hnear : (Subtype.val : U → ℝ) '' t ∈ 𝓝 r :=
    hU.isOpenMap_subtype_val.image_mem_nhds ht
  have hfinite_zero : ∀ᶠ y in 𝓝 r,
      ∀ i ∈ {i | ({y : U | (y : ℝ) ∈ Function.support (f i)} ∩ t).Nonempty},
        f i y = 0 :=
    hfinite.eventually_all.mpr fun i _ =>
      notMem_tsupport_iff_eventuallyEq.mp (hzero i)
  filter_upwards [hnear, hfinite_zero] with y hy hyzero i
  obtain ⟨z, hzt, rfl⟩ := hy
  by_cases hi : f i z = 0
  · exact hi
  · exact hyzero i ⟨z, hi, hzt⟩

/-- Strict support in a negative component excludes every zero of the
reference slope, and the control sum is identically zero near that point. -/
theorem stateControlSum_eventuallyEq_zero_at_root
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C)
    (hcontrol : ∀ m, tsupport (C.control m) ⊆ Ioo (C.left m) (C.right m))
    {r : ℝ} (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (x : AnnularState S) :
    stateControlSum C x =ᶠ[𝓝 r] (fun _ => 0) := by
  obtain ⟨_, _, _, hnegative, _, _, hfinite, _⟩ := hC
  have hzero (m : ℕ) : r ∉ tsupport (C.control m) := by
    intro hm
    have hneg := hnegative m r (hcontrol m hm)
    rw [hroot] at hneg
    exact (lt_irrefl (0 : ℝ)) hneg
  have hnear := locallyFinite_support_eventually_zero isOpen_Ioo hfinite hr hzero
  filter_upwards [hnear] with y hy
  simp only [stateControlSum, hy, mul_zero, tsum_zero]

/-- The actual logarithmic perturbation has zero germ at every reference
root. No smallness or symmetry condition on the state is needed. -/
theorem stateProfile_eventuallyEq_reference_at_root
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C)
    (hcontrol : ∀ m, tsupport (C.control m) ⊆ Ioo (C.left m) (C.right m))
    (hborder : tsupport D.chi ⊆
      {r | r ∈ radialCore D ∧ 0 < deriv D.w r})
    {r : ℝ} (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (x : AnnularState S) : stateProfile D S C x =ᶠ[𝓝 r] D.w := by
  have hchi : r ∉ tsupport D.chi := by
    intro h
    have hpos := (hborder h).2
    rw [hroot] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  have hchi_zero : D.chi =ᶠ[𝓝 r] (fun _ => 0) :=
    notMem_tsupport_iff_eventuallyEq.mp hchi
  have hsum := stateControlSum_eventuallyEq_zero_at_root hC hcontrol hr hroot x
  filter_upwards [hchi_zero, hsum] with y hy hysum
  change D.w y * Real.exp (x.2.1 * D.chi y + stateControlSum C x y) = D.w y
  rw [hy, hysum, mul_zero, zero_add, Real.exp_zero, mul_one]

end ContinuousFlexibility.Statements
