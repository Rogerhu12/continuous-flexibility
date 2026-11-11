import ContinuousFlexibility.Radial.ReferenceCellAlgebra
import Mathlib.Topology.Order.Compact

/-!
# Smooth finite-mode sources for the reference graph

The zero mode has vanishing ordinary radial integral. Every radial
coefficient is smooth and has compact topological support in the open
core, and the nonzero frequencies are precisely positive even cosine
frequencies. Such a source belongs to every fixed weighted source space.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- The smooth compact finite-mode sources used to form the graph core.
The scalar border datum is unrestricted. -/
def ReferenceSmoothFiniteSource (D : ReferenceData) (F : RadialSource) : Prop :=
  ∃ (J : Finset ℕ) (f₀ : ℝ → ℝ) (f : ℕ → ℝ → ℝ),
    (ContDiff ℝ ∞ f₀ ∧ HasCompactSupport f₀ ∧ tsupport f₀ ⊆ radialCore D) ∧
    (∀ n ∈ J, ContDiff ℝ ∞ (f n) ∧ HasCompactSupport (f n) ∧
      tsupport (f n) ⊆ radialCore D) ∧
    (∫ r in D.a..D.b, f₀ r) = 0 ∧
    ∀ r θ, F.1 (r, θ) =
      f₀ r + ∑ n ∈ J, f n r * cosineMode (2 * (n + 1)) θ

private theorem referenceSmooth_cosine_continuous (j : ℕ) :
    Continuous (cosineMode j) :=
  continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))

/-- Any globally continuous field is locally in the actual physical L²
space. The radial core and one angular period lie in a compact rectangle. -/
theorem memLp_radialPhysical_of_continuous (D : ReferenceData)
    {f : PolarPoint → ℝ} (hf : Continuous f) :
    MemLp f 2 (radialPhysicalMeasure D) := by
  let K : Set PolarPoint := Icc D.a D.b ×ˢ Icc (0 : ℝ) (2 * Real.pi)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hsub : radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) ⊆ K := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    exact ⟨⟨hr.1.le, hr.2.le⟩, ⟨hθ.1.le, hθ.2⟩⟩
  letI : IsFiniteMeasure (radialPhysicalMeasure D) := ⟨by
    change volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact (measure_mono hsub).trans_lt hK.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hK.bddAbove_image hf.norm.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem
    (show MeasurableSet (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) from
      measurableSet_Ioo.prod measurableSet_Ioc)] with x hx
  exact hC ⟨x, hsub hx, rfl⟩

theorem radialCellIntegrable_of_continuous {D : ReferenceData}
    (hD : RadialPartition D) {f : PolarPoint → ℝ} (hf : Continuous f) :
    RadialCellIntegrable D f := by
  intro m
  exact memLp_radialPhysical_of_continuous D
    (((hD.1 m).continuous.comp continuous_fst).mul hf)

/-- A compact radial support meets only finitely many actual cells. Thus
the frozen weighted square sum is finite for every fixed pair of weights. -/
theorem sourceCellSquare_summable_of_radialCompactSupport {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f : PolarPoint → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hcore : K ⊆ radialCore D)
    (hsupp : ∀ r ∉ K, ∀ θ, f (r, θ) = 0) (γ M : ℝ) :
    Summable (sourceCellSquare D γ M f) := by
  classical
  obtain ⟨C, hC⟩ := hD
  have hfinite : Set.Finite {m | (D.cells m ∩ K).Nonempty} :=
    hC.2.2.2.2.2.1 K hK hcore
  apply summable_of_ne_finset_zero (s := hfinite.toFinset)
  intro m hm
  have hm' : ¬(D.cells m ∩ K).Nonempty := by
    intro hmeet
    apply hm
    rw [Set.Finite.mem_toFinset]
    change (D.cells m ∩ K).Nonempty
    exact hmeet
  have hz (r θ : ℝ) : D.localizer m r * f (r, θ) = 0 := by
    by_cases hlocal : D.localizer m r = 0
    · rw [hlocal, zero_mul]
    · have hcell : r ∈ D.cells m :=
        hC.2.1.2.2.1 m (Function.mem_support.mpr hlocal)
      have hr : r ∉ K := fun hr => hm' ⟨r, hcell, hr⟩
      rw [hsupp r hr θ, mul_zero]
  simp only [sourceCellSquare, referenceCellSquare, radialAngularMean, hz,
    zero_pow (by decide : (2 : ℕ) ≠ 0), intervalIntegral.integral_zero, mul_zero]

theorem radialAngularMean_const (c : ℝ) :
    radialAngularMean (fun _ => c) = c := by
  simp only [radialAngularMean, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

/-- The nonzero frequencies are indexed without including the constant
cosine, whose normalization differs from the zero channel. -/
theorem radialAngularMean_smoothFiniteExpansion
    (J : Finset ℕ) (c₀ : ℝ) (c : ℕ → ℝ) :
    radialAngularMean (fun θ => c₀ + ∑ n ∈ J, c n * cosineMode (2 * (n + 1)) θ) = c₀ := by
  have ht (n : ℕ) : IntervalIntegrable
      (fun θ => c n * cosineMode (2 * (n + 1)) θ) volume 0 (2 * Real.pi) :=
    (continuous_const.mul (referenceSmooth_cosine_continuous _)).intervalIntegrable _ _
  have hsum : IntervalIntegrable
      (fun θ => ∑ n ∈ J, c n * cosineMode (2 * (n + 1)) θ) volume 0 (2 * Real.pi) :=
    (continuous_finsetSum J (fun n _ =>
      continuous_const.mul (referenceSmooth_cosine_continuous _))).intervalIntegrable _ _
  have hz (n : ℕ) :
      (∫ θ in (0 : ℝ)..2 * Real.pi, cosineMode (2 * (n + 1)) θ) = 0 :=
    integral_cosineMode _ (by omega)
  unfold radialAngularMean
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _) hsum,
    intervalIntegral.integral_finsetSum (fun n _ => ht n)]
  simp only [intervalIntegral.integral_const_mul, hz, mul_zero, Finset.sum_const_zero,
    add_zero]
  exact radialAngularMean_const c₀

theorem ReferenceSmoothFiniteSource.continuous {D : ReferenceData} {F : RadialSource}
    (hF : ReferenceSmoothFiniteSource D F) : Continuous F.1 := by
  obtain ⟨J, f₀, f, h₀, hf, _, heq⟩ := hF
  have hrepr : F.1 = fun x =>
      f₀ x.1 + ∑ n ∈ J, f n x.1 * cosineMode (2 * (n + 1)) x.2 :=
    funext (fun x => heq x.1 x.2)
  rw [hrepr]
  exact (h₀.1.continuous.comp continuous_fst).add
    (continuous_finsetSum J (fun n hn =>
      ((hf n hn).1.continuous.comp continuous_fst).mul
        ((referenceSmooth_cosine_continuous _).comp continuous_snd)))

theorem ReferenceSmoothFiniteSource.radialCompactSupport
    {D : ReferenceData} {F : RadialSource} (hF : ReferenceSmoothFiniteSource D F) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ radialCore D ∧
      ∀ r ∉ K, ∀ θ, F.1 (r, θ) = 0 := by
  classical
  obtain ⟨J, f₀, f, h₀, hf, _, heq⟩ := hF
  let K : Set ℝ := tsupport f₀ ∪ ⋃ n ∈ J, tsupport (f n)
  have hK : IsCompact K := h₀.2.1.union (J.isCompact_biUnion (fun n hn => (hf n hn).2.1))
  have hcore : K ⊆ radialCore D :=
    union_subset h₀.2.2 (iUnion₂_subset (fun n hn => (hf n hn).2.2))
  refine ⟨K, hK, hcore, ?_⟩
  intro r hr θ
  have hz₀ : f₀ r = 0 := by
    by_contra h
    exact hr (Or.inl (subset_tsupport f₀ (Function.mem_support.mpr h)))
  have hz (n : ℕ) (hn : n ∈ J) : f n r = 0 := by
    by_contra h
    exact hr (Or.inr (mem_iUnion₂.mpr
      ⟨n, hn, subset_tsupport (f n) (Function.mem_support.mpr h)⟩))
  rw [heq r θ, hz₀, Finset.sum_eq_zero (fun n hn => by rw [hz n hn, zero_mul]), add_zero]

/-- Smooth compact finite-mode sources belong to every fixed source
weight, with their prescribed scalar border datum. -/
theorem ReferenceSmoothFiniteSource.sourceMember
    {D : ReferenceData} {F : RadialSource} (hF : ReferenceSmoothFiniteSource D F)
    (hD : IsAccumulatingProfile D) (γ M : ℝ) : SourceMember D γ M F := by
  have hpart : RadialPartition D := by obtain ⟨C, hC⟩ := hD; exact hC.2.1
  have hlocal := radialCellIntegrable_of_continuous hpart hF.continuous
  obtain ⟨K, hK, hcore, hsupp⟩ := hF.radialCompactSupport
  have hsum := sourceCellSquare_summable_of_radialCompactSupport hD hK hcore hsupp γ M
  obtain ⟨J, f₀, f, h₀, hf, hzero, heq⟩ := hF
  have hmean (r : ℝ) : radialAngularMean (fun θ => F.1 (r, θ)) = f₀ r := by
    simp_rw [heq r]
    exact radialAngularMean_smoothFiniteExpansion J (f₀ r) (fun n => f n r)
  refine ⟨hlocal, hsum, ?_, ?_, ?_, ?_⟩
  · rintro ⟨r, θ⟩
    change F.1 (r + 0, θ + Real.pi) = F.1 (r, θ)
    rw [add_zero, heq, heq]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [cosineMode_even_frequency_periodic (n + 1) θ]
  · intro r θ
    rw [heq, heq]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [cosineMode_even (2 * (n + 1)) θ]
  · simpa only [hmean] using h₀.1.continuous.intervalIntegrable
      (μ := volume) D.a D.b
  · simpa only [hmean] using hzero

end ContinuousFlexibility.Radial
