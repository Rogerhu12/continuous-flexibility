import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Smooth compact approximation in L² on an open set

The measure need only be finite on compact subsets of the open set carrying
it. In particular, its mass may diverge at the boundary. Density follows
from the ordinary fundamental lemma for distributions and the Hilbert-space
orthogonal-complement criterion.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Classes with a globally smooth representative compactly supported in
the prescribed open set. -/
def smoothCompactL2Submodule (μ : Measure E) (U : Set E) :
    Submodule ℝ (Lp ℝ 2 μ) where
  carrier := {v | ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    tsupport f ⊆ U ∧ (v : E → ℝ) =ᵐ[μ] f}
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_, Lp.coeFn_zero ℝ 2 μ⟩
    simp
  add_mem' := by
    rintro v w ⟨f, hf, hfc, hfu, hfv⟩ ⟨g, hg, hgc, hgu, hgw⟩
    refine ⟨f + g, hf.add hg, hfc.add hgc, ?_, ?_⟩
    · exact (tsupport_add f g).trans (union_subset hfu hgu)
    · exact (Lp.coeFn_add v w).trans (hfv.add hgw)
  smul_mem' := by
    rintro c v ⟨f, hf, hfc, hfu, hfv⟩
    refine ⟨fun x => c * f x, contDiff_const.mul hf, ?_, ?_, ?_⟩
    · exact hfc.mul_left
    · exact tsupport_mul_subset_right.trans hfu
    · filter_upwards [Lp.coeFn_smul c v, hfv] with x hx hvx
      simpa only [Pi.smul_apply, smul_eq_mul, hvx] using hx

/-- Compact support strictly inside the open set avoids any singular mass
at its boundary. -/
theorem memLp_of_continuous_compact_support_inside
    {μ : Measure E} {U : Set E}
    (hfinite : ∀ K : Set E, IsCompact K → K ⊆ U → μ K < ⊤)
    {f : E → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfu : tsupport f ⊆ U) : MemLp f 2 μ := by
  apply (hf.memLp_top_of_hasCompactSupport hfc μ).mono_exponent_of_measure_support_ne_top
    (s := tsupport f)
  · intro x hx
    exact image_eq_zero_of_notMem_tsupport hx
  · exact (hfinite _ hfc hfu).ne
  · exact le_top

/-- L² functions are locally integrable wherever the measure is finite on
compact sets. This does not require a globally locally finite measure. -/
theorem locallyIntegrableOn_of_memLp_two
    {μ : Measure E} {U : Set E} (hU : IsOpen U)
    (hfinite : ∀ K : Set E, IsCompact K → K ⊆ U → μ K < ⊤)
    {f : E → ℝ} (hf : MemLp f 2 μ) : LocallyIntegrableOn f U μ := by
  rw [locallyIntegrableOn_iff hU.isLocallyClosed]
  intro K hKU hK
  haveI : Fact (μ K < ⊤) := ⟨hfinite K hK hKU⟩
  exact memLp_one_iff_integrable.mp ((hf.restrict K).mono_exponent (by norm_num))

/-- Smooth compactly supported classes are dense for any Borel measure
carried by an open set and finite on its compact subsets. -/
theorem smoothCompactL2Submodule_dense
    {μ : Measure E} {U : Set E} (hU : IsOpen U)
    (hcarry : ∀ᵐ x ∂μ, x ∈ U)
    (hfinite : ∀ K : Set E, IsCompact K → K ⊆ U → μ K < ⊤) :
    Dense (smoothCompactL2Submodule μ U : Set (Lp ℝ 2 μ)) := by
  have hclosure : (smoothCompactL2Submodule μ U).topologicalClosure = ⊤ := by
    apply (Submodule.topologicalClosure_eq_top_iff _).mpr
    apply le_antisymm
    · intro v hv
      have hloc := locallyIntegrableOn_of_memLp_two hU hfinite (Lp.memLp v)
      have hzero : ∀ᵐ x ∂μ, x ∈ U → v x = 0 := by
        apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
        intro g hg hgc hgu
        have hgp := memLp_of_continuous_compact_support_inside hfinite hg.continuous hgc hgu
        have hmem : hgp.toLp g ∈ smoothCompactL2Submodule μ U :=
          ⟨g, hg, hgc, hgu, hgp.coeFn_toLp⟩
        have hinner := hv (hgp.toLp g) hmem
        rw [L2.inner_def] at hinner
        calc
          (∫ x, g x • v x ∂μ) = ∫ x, inner ℝ (hgp.toLp g x) (v x) ∂μ := by
            apply integral_congr_ae
            filter_upwards [hgp.coeFn_toLp] with x hx
            simp only [hx, Real.inner_apply, smul_eq_mul]
          _ = 0 := hinner
      have hvzero : v = 0 := by
        apply Lp.ext
        filter_upwards [hzero, hcarry, Lp.coeFn_zero ℝ 2 μ] with x hx hU hz
        exact (hx hU).trans hz.symm
      simpa only [Submodule.mem_bot] using hvzero
    · exact bot_le
  intro v
  change v ∈ (smoothCompactL2Submodule μ U).topologicalClosure
  rw [hclosure]
  trivial

/-- An epsilon form of smooth compact approximation, with the actual
representative, its L² membership, and its quotient-space distance. -/
theorem MemLp.exists_contDiff_compact_approximation
    {μ : Measure E} {U : Set E} {f : E → ℝ} (hf : MemLp f 2 μ)
    (hU : IsOpen U) (hcarry : ∀ᵐ x ∂μ, x ∈ U)
    (hfinite : ∀ K : Set E, IsCompact K → K ⊆ U → μ K < ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      ∃ hg : MemLp g 2 μ, ‖hg.toLp g - hf.toLp f‖ < ε := by
  have hdense := smoothCompactL2Submodule_dense hU hcarry hfinite
  obtain ⟨v, hv, hvdist⟩ := Metric.mem_closure_iff.mp (hdense (hf.toLp f)) ε hε
  obtain ⟨g, hg, hgc, hgu, hgv⟩ := hv
  have hgp : MemLp g 2 μ := (memLp_congr_ae hgv).mp (Lp.memLp v)
  have heq : hgp.toLp g = v := by
    apply Lp.ext
    exact hgp.coeFn_toLp.trans hgv.symm
  refine ⟨g, hg, hgc, hgu, hgp, ?_⟩
  simpa only [heq, dist_eq_norm, norm_sub_rev] using hvdist

end ContinuousFlexibility.Analysis
