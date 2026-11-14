module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Algebra.Monoid

/-!
# Closure of finite L2 product bounds

L2 convergence of every member of a finite family supplies one common
almost-everywhere convergent subsequence. Fatou then transfers a uniform
product bound to the actual product of the limits. The measure may be
infinite, and no convergence of the products in L2 is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

variable {α ι E : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A finite family converging in measure admits a common almost-everywhere
convergent subsequence, on an arbitrary measure space. -/
theorem oneHigh_exists_common_subsequence [Fintype ι] [PseudoEMetricSpace E]
    (u : ℕ → ι → α → E) (f : ι → α → E)
    (hlim : ∀ i, TendstoInMeasure μ (fun N => u N i) atTop (f i)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, ∀ i, Tendsto (fun N => u (ns N) i x) atTop (𝓝 (f i x)) := by
  classical
  have hfinite (t : Finset ι) : ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, ∀ i ∈ t, Tendsto (fun N => u (ns N) i x) atTop (𝓝 (f i x)) := by
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨id, strictMono_id, Eventually.of_forall (fun x i hi => ?_)⟩
      simp at hi
    | @insert i t hit ih =>
      obtain ⟨ns, hns, hns_lim⟩ := ih
      obtain ⟨ms, hms, hms_lim⟩ :=
        ((hlim i).comp hns.tendsto_atTop).exists_seq_tendsto_ae
      refine ⟨ns ∘ ms, hns.comp hms, ?_⟩
      filter_upwards [hns_lim, hms_lim] with x hx hi
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hi
      · exact (hx j hj).comp hms.tendsto_atTop
  obtain ⟨ns, hns, hns_lim⟩ := hfinite Finset.univ
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hns_lim] with x hx
  exact fun i => hx i (Finset.mem_univ i)

/-- A uniform finite product bound is closed under factorwise physical L2
convergence. The real norm convergence is used only after the difference
has been proved to belong to L2. -/
theorem oneHigh_l2_product_limit [Fintype ι] [NormedCommRing E]
    (u : ℕ → ι → α → E) (f : ι → α → E)
    (hu : ∀ N i, MemLp (u N i) 2 μ) (hf : ∀ i, MemLp (f i) 2 μ)
    (hlim : ∀ i, Tendsto (fun N : ℕ =>
      (eLpNorm (fun x => u N i x - f i x) 2 μ).toReal) atTop (𝓝 0))
    (C : ℝ≥0∞) (hC : C < ⊤)
    (hbound : ∀ N, eLpNorm (fun x => ∏ i, u N i x) 2 μ ≤ C) :
    MemLp (fun x => ∏ i, f i x) 2 μ ∧ eLpNorm (fun x => ∏ i, f i x) 2 μ ≤ C := by
  classical
  have hmeasure (i : ι) : TendstoInMeasure μ (fun N => u N i) atTop (f i) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    apply (ENNReal.tendsto_toReal_iff
      (fun N => ((hu N i).sub (hf i)).ne) ENNReal.zero_ne_top).mp
    have hsub (N : ℕ) : (u N i - f i : α → E) = (fun x => u N i x - f i x) := rfl
    simpa only [ENNReal.toReal_zero, hsub] using hlim i
  obtain ⟨ns, hns, hns_lim⟩ := oneHigh_exists_common_subsequence u f hmeasure
  have hproduct_lim : ∀ᵐ x ∂μ,
      Tendsto (fun N => ∏ i, u (ns N) i x) atTop (𝓝 (∏ i, f i x)) := by
    filter_upwards [hns_lim] with x hx
    exact tendsto_finsetProd Finset.univ (fun i _ => hx i)
  have hprod_meas (N : ℕ) : AEStronglyMeasurable (fun x => ∏ i, u N i x) μ :=
    Finset.univ.aestronglyMeasurable_fun_prod (fun i _ => (hu N i).aestronglyMeasurable)
  have hlimit_meas : AEStronglyMeasurable (fun x => ∏ i, f i x) μ :=
    Finset.univ.aestronglyMeasurable_fun_prod (fun i _ => (hf i).aestronglyMeasurable)
  have hfinal : eLpNorm (fun x => ∏ i, f i x) 2 μ ≤ C :=
    Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall fun N => hbound (ns N))
      (fun N => hprod_meas (ns N)) hlimit_meas hproduct_lim
  exact ⟨hfinal.trans_lt hC, hfinal⟩

end ContinuousFlexibility.Analysis
