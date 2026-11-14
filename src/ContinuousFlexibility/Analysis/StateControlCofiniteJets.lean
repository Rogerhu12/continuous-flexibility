module

public import ContinuousFlexibility.Analysis.StateControlDecay
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Finite

/-!
# Flat control jets from cofinite bounds on the components

Every fixed negative component is separated from the two radial endpoints.
Thus, sufficiently close to either endpoint, only components outside any
given finite set can be active. Uniform smallness of the control jets on
all but finitely many components then gives the endpoint limit of the
actual locally finite control sum. No identification of a component with
the cell used to estimate its coefficient is needed here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

/-- Along any filter which eventually avoids each fixed component, a
cofinite uniform bound on the component jets bounds the actual sum. -/
theorem tendsto_stateControlSum_jet_of_eventually_small
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C) (x : AnnularState S) (n : ℕ)
    {l : Filter ℝ} (hcore : ∀ᶠ r in l, r ∈ Ioo D.a D.b)
    (havoid : ∀ m : ℕ, ∀ᶠ r in l, r ∉ Ioo (C.left m) (C.right m))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in cofinite,
      ∀ r ∈ Ioo (C.left m) (C.right m),
        |stateKappa S x m * iteratedDeriv n (C.control m) r| ≤ ε) :
    Tendsto (iteratedDeriv n (stateControlSum C x)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hfinite : {m : ℕ | ¬ ∀ r ∈ Ioo (C.left m) (C.right m),
      |stateKappa S x m * iteratedDeriv n (C.control m) r| ≤ ε / 2}.Finite :=
    eventually_cofinite.mp (hsmall (ε / 2) (half_pos hε))
  have hexclude : ∀ᶠ r in l, ∀ m ∈ {m : ℕ | ¬ ∀ s ∈ Ioo (C.left m) (C.right m),
      |stateKappa S x m * iteratedDeriv n (C.control m) s| ≤ ε / 2},
      r ∉ Ioo (C.left m) (C.right m) :=
    (eventually_all_finite hfinite).mpr fun m _ => havoid m
  filter_upwards [hcore, hexclude] with r hr hnot
  have hbound : |iteratedDeriv n (stateControlSum C x) r| ≤ ε / 2 := by
    apply abs_iteratedDeriv_stateControlSum_le hC x n hr (half_pos hε).le
    intro m hm
    by_cases hgood : ∀ s ∈ Ioo (C.left m) (C.right m),
        |stateKappa S x m * iteratedDeriv n (C.control m) s| ≤ ε / 2
    · exact hgood r hm
    · exact False.elim ((hnot m hgood) hm)
  simpa only [Real.dist_eq, sub_zero] using hbound.trans_lt (half_lt_self hε)

/-- Cofinite smallness of every ordinary control jet gives flat jets at
both endpoints of the annulus, using the same filter argument for each. -/
theorem stateControlSum_flatJets_of_eventually_small
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions D S C) (x : AnnularState S)
    (hsmall : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ m in cofinite,
      ∀ r ∈ Ioo (C.left m) (C.right m),
        |stateKappa S x m * iteratedDeriv n (C.control m) r| ≤ ε) :
    (∀ n : ℕ, Tendsto (iteratedDeriv n (stateControlSum C x)) (𝓝[>] D.a) (𝓝 0)) ∧
    (∀ n : ℕ, Tendsto (iteratedDeriv n (stateControlSum C x)) (𝓝[<] D.b) (𝓝 0)) := by
  have hab : D.a < D.b :=
    (hC.1 0).1.trans ((hC.1 0).2.1.trans (hC.1 0).2.2)
  have hcoreLeft : ∀ᶠ r in 𝓝[>] D.a, r ∈ Ioo D.a D.b := by
    filter_upwards [eventually_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hab)] with r ha hb
    exact ⟨ha, hb⟩
  have hcoreRight : ∀ᶠ r in 𝓝[<] D.b, r ∈ Ioo D.a D.b := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hab),
      eventually_mem_nhdsWithin] with r ha hb
    exact ⟨ha, hb⟩
  have havoidLeft (m : ℕ) :
      ∀ᶠ r in 𝓝[>] D.a, r ∉ Ioo (C.left m) (C.right m) := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (hC.1 m).1)] with r hr
    exact fun hm => (not_lt_of_ge hr.le) hm.1
  have havoidRight (m : ℕ) :
      ∀ᶠ r in 𝓝[<] D.b, r ∉ Ioo (C.left m) (C.right m) := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (hC.1 m).2.2)] with r hr
    exact fun hm => (not_lt_of_ge hr.le) hm.2
  exact ⟨fun n => tendsto_stateControlSum_jet_of_eventually_small hC x n
      hcoreLeft havoidLeft (hsmall n),
    fun n => tendsto_stateControlSum_jet_of_eventually_small hC x n
      hcoreRight havoidRight (hsmall n)⟩

end ContinuousFlexibility.Statements
