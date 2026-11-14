module

public import ContinuousFlexibility.Statements.DeepTailOperator
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The deep-tail form core and its Dirichlet truncations

The core uses smooth functions whose closed support is compactly contained in
the open interval. Its closure is a genuine closed linear subspace of the
product of the two weighted L² spaces. Every core element already belongs to
one finite truncation, and all elements of a truncated form vanish outside
that truncation, including their weak derivative coordinate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem deepTail_node_strictMono {T : DeepTailData} (hT : DeepTailHypotheses T) :
    StrictMono T.node := by
  rcases hT with ⟨_, _, _, _, _, _, _, _, _, _, he⟩
  exact strictMono_nat_of_lt_succ fun n => (he n).1.trans (he n).2.1

theorem deepTail_node_lt_endpoint {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) : T.node n < T.endpoint := by
  have hm := deepTail_node_strictMono hT
  have ht := hT.2.2.2.2.2.2.2.2.2.1
  exact (hm (Nat.lt_succ_self n)).trans_le (hm.monotone.ge_of_tendsto ht (n + 1))

theorem deepTail_entrance_le_node {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) : T.entrance ≤ T.node n :=
  hT.2.1.trans ((deepTail_node_strictMono hT).monotone (Nat.zero_le n))

theorem deepTail_entrance_lt_succ_node {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) : T.entrance < T.node (n + 1) :=
  (deepTail_entrance_le_node hT n).trans_lt (deepTail_node_strictMono hT (Nat.lt_succ_self n))

theorem tailEnergyCore_zero (T : DeepTailData) (endCut : ℝ) :
    (0 : DeepTailL2 T × DeepTailL2 T) ∈ TailEnergyCore T endCut := by
  refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_, ?_, ?_⟩
  · simp only [tsupport_zero, empty_subset]
  · simpa only [Prod.fst_zero] using (Lp.coeFn_zero ℝ 2 (deepTailMeasure T))
  · simpa only [Prod.snd_zero, deriv_zero] using (Lp.coeFn_zero ℝ 2 (deepTailMeasure T))

theorem tailEnergyCore_add {T : DeepTailData} {endCut : ℝ}
    {p q : DeepTailL2 T × DeepTailL2 T}
    (hp : p ∈ TailEnergyCore T endCut) (hq : q ∈ TailEnergyCore T endCut) :
    p + q ∈ TailEnergyCore T endCut := by
  rcases hp with ⟨φ, hφ, hcφ, hsφ, hφ₀, hφ₁⟩
  rcases hq with ⟨ψ, hψ, hcψ, hsψ, hψ₀, hψ₁⟩
  refine ⟨φ + ψ, hφ.add hψ, hcφ.add hcψ, (tsupport_add φ ψ).trans
    (union_subset hsφ hsψ), ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add p.1 q.1, hφ₀, hψ₀] with x hx hφx hψx
    simp only [Prod.fst_add, Pi.add_apply] at hx ⊢
    exact hx.trans (congrArg₂ (· + ·) hφx hψx)
  · filter_upwards [Lp.coeFn_add p.2 q.2, hφ₁, hψ₁] with x hx hφx hψx
    rw [Prod.snd_add, hx, Pi.add_apply, hφx, hψx]
    exact (deriv_add (hφ.differentiable (by simp)).differentiableAt
      (hψ.differentiable (by simp)).differentiableAt).symm

theorem tailEnergyCore_smul {T : DeepTailData} {endCut : ℝ}
    {p : DeepTailL2 T × DeepTailL2 T} (hp : p ∈ TailEnergyCore T endCut) (a : ℝ) :
    a • p ∈ TailEnergyCore T endCut := by
  rcases hp with ⟨φ, hφ, hcφ, hsφ, hφ₀, hφ₁⟩
  refine ⟨fun x => a * φ x, contDiff_const.mul hφ, hcφ.mul_left, ?_, ?_, ?_⟩
  · exact tsupport_mul_subset_right.trans hsφ
  · filter_upwards [Lp.coeFn_smul a p.1, hφ₀] with x hx hφx
    simpa only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, hφx] using hx
  · filter_upwards [Lp.coeFn_smul a p.2, hφ₁] with x hx hφx
    simpa only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, hφx, deriv_const_mul_field] using hx

/-- The algebraic core as a submodule, before taking the energy closure. -/
def tailEnergyCoreSubmodule (T : DeepTailData) (endCut : ℝ) :
    Submodule ℝ (DeepTailL2 T × DeepTailL2 T) where
  carrier := TailEnergyCore T endCut
  zero_mem' := tailEnergyCore_zero T endCut
  add_mem' := tailEnergyCore_add
  smul_mem' := fun a _ hp => tailEnergyCore_smul hp a

theorem mem_tailEnergyCoreSubmodule (T : DeepTailData) (endCut : ℝ)
    (p : DeepTailL2 T × DeepTailL2 T) :
    p ∈ tailEnergyCoreSubmodule T endCut ↔ p ∈ TailEnergyCore T endCut := Iff.rfl

/-- The closed form lift, with its linear structure retained. -/
def tailFormSubmodule (T : DeepTailData) (endCut : ℝ) :
    Submodule ℝ (DeepTailL2 T × DeepTailL2 T) :=
  (tailEnergyCoreSubmodule T endCut).topologicalClosure

theorem coe_tailFormSubmodule (T : DeepTailData) (endCut : ℝ) :
    (tailFormSubmodule T endCut : Set (DeepTailL2 T × DeepTailL2 T)) =
      TailFormLift T endCut := by
  rw [tailFormSubmodule, Submodule.topologicalClosure_coe]
  rfl

theorem mem_tailFormSubmodule (T : DeepTailData) (endCut : ℝ)
    (p : DeepTailL2 T × DeepTailL2 T) :
    p ∈ tailFormSubmodule T endCut ↔ p ∈ TailFormLift T endCut := by
  exact Set.ext_iff.mp (coe_tailFormSubmodule T endCut) p

theorem tailFormLift_isClosed (T : DeepTailData) (endCut : ℝ) :
    IsClosed (TailFormLift T endCut) := isClosed_closure

theorem tailEnergyCore_mono (T : DeepTailData) {a b : ℝ} (hab : a ≤ b) :
    TailEnergyCore T a ⊆ TailEnergyCore T b := by
  rintro p ⟨φ, hφ, hc, hs, hu, hd⟩
  exact ⟨φ, hφ, hc, fun x hx => ⟨(hs hx).1, (hs hx).2.trans_le hab⟩, hu, hd⟩

theorem tailFormLift_mono (T : DeepTailData) {a b : ℝ} (hab : a ≤ b) :
    TailFormLift T a ⊆ TailFormLift T b :=
  closure_mono (tailEnergyCore_mono T hab)

theorem tailFormSubmodule_mono (T : DeepTailData) {a b : ℝ} (hab : a ≤ b) :
    tailFormSubmodule T a ≤ tailFormSubmodule T b := by
  intro p hp
  exact (mem_tailFormSubmodule T b p).mpr
    (tailFormLift_mono T hab ((mem_tailFormSubmodule T a p).mp hp))

/-- Compact sets in the open tail fit into a finite Dirichlet truncation. -/
theorem deepTail_compact_subset_some_cut {T : DeepTailData}
    (hT : DeepTailHypotheses T) {K : Set ℝ} (hK : IsCompact K)
    (hs : K ⊆ Ioo T.entrance T.endpoint) :
    ∃ n : ℕ, K ⊆ Ioo T.entrance (T.node (n + 1)) := by
  rcases K.eq_empty_or_nonempty with he | hn
  · exact ⟨0, by rw [he]; exact empty_subset _⟩
  · obtain ⟨b, hb, hmax⟩ := hK.exists_isGreatest hn
    have ht : Tendsto T.node atTop (𝓝 T.endpoint) := hT.2.2.2.2.2.2.2.2.2.1
    obtain ⟨n, hn⟩ := (ht.eventually (Ioi_mem_nhds (hs hb).2)).exists
    refine ⟨n, ?_⟩
    intro x hx
    exact ⟨(hs hx).1, (hmax hx).trans_lt (hn.trans
      (deepTail_node_strictMono hT (Nat.lt_succ_self n)))⟩

/-- Compact containment makes every smooth core element belong to a finite
Dirichlet truncation. No endpoint cutoff estimate is needed here. -/
theorem tailEnergyCore_mem_some_truncation {T : DeepTailData}
    (hT : DeepTailHypotheses T) {p : DeepTailL2 T × DeepTailL2 T}
    (hp : p ∈ TailEnergyCore T T.endpoint) :
    ∃ n : ℕ, p ∈ TailEnergyCore T (T.node (n + 1)) := by
  rcases hp with ⟨φ, hφ, hc, hs, hu, hd⟩
  obtain ⟨n, hn⟩ := deepTail_compact_subset_some_cut hT hc hs
  exact ⟨n, φ, hφ, hc, hn, hu, hd⟩

/-- The full Friedrichs form is the closure of its finite Dirichlet forms. -/
theorem tailFormLift_eq_closure_iUnion {T : DeepTailData} (hT : DeepTailHypotheses T) :
    TailFormLift T T.endpoint =
      closure (⋃ n : ℕ, TailFormLift T (T.node (n + 1))) := by
  apply le_antisymm
  · apply closure_mono
    intro p hp
    obtain ⟨n, hn⟩ := tailEnergyCore_mem_some_truncation hT hp
    exact mem_iUnion.mpr ⟨n, subset_closure hn⟩
  · apply closure_minimal
    · intro p hp
      obtain ⟨n, hn⟩ := mem_iUnion.mp hp
      exact tailFormLift_mono T (deepTail_node_lt_endpoint hT (n + 1)).le hn
    · exact tailFormLift_isClosed T T.endpoint

/-! ## Bounded restriction and support of the closed form -/

private def tailIndicatorValue (T : DeepTailData) (s : Set ℝ) (hs : MeasurableSet s)
    (f : DeepTailL2 T) : DeepTailL2 T :=
  ((Lp.memLp f).indicator hs).toLp (s.indicator (f : ℝ → ℝ))

private theorem tailIndicatorValue_coeFn (T : DeepTailData) (s : Set ℝ)
    (hs : MeasurableSet s) (f : DeepTailL2 T) :
    (tailIndicatorValue T s hs f : ℝ → ℝ) =ᵐ[deepTailMeasure T]
      s.indicator (f : ℝ → ℝ) :=
  MemLp.coeFn_toLp _

private theorem tailIndicatorValue_add (T : DeepTailData) (s : Set ℝ)
    (hs : MeasurableSet s) (f g : DeepTailL2 T) :
    tailIndicatorValue T s hs (f + g) =
      tailIndicatorValue T s hs f + tailIndicatorValue T s hs g := by
  apply Lp.ext
  filter_upwards [tailIndicatorValue_coeFn T s hs (f + g),
    tailIndicatorValue_coeFn T s hs f, tailIndicatorValue_coeFn T s hs g,
    Lp.coeFn_add f g, Lp.coeFn_add (tailIndicatorValue T s hs f)
      (tailIndicatorValue T s hs g)] with x hfg hf hg ha hb
  rw [hfg, hb, Pi.add_apply, hf, hg]
  by_cases hx : x ∈ s
  · simpa only [indicator_of_mem hx, Pi.add_apply] using ha
  · simp only [indicator_of_notMem hx, add_zero]

private theorem tailIndicatorValue_smul (T : DeepTailData) (s : Set ℝ)
    (hs : MeasurableSet s) (a : ℝ) (f : DeepTailL2 T) :
    tailIndicatorValue T s hs (a • f) = a • tailIndicatorValue T s hs f := by
  apply Lp.ext
  filter_upwards [tailIndicatorValue_coeFn T s hs (a • f),
    tailIndicatorValue_coeFn T s hs f, Lp.coeFn_smul a f,
    Lp.coeFn_smul a (tailIndicatorValue T s hs f)] with x haf hf ha hb
  rw [haf, hb, Pi.smul_apply, hf]
  by_cases hx : x ∈ s
  · simpa only [indicator_of_mem hx, Pi.smul_apply] using ha
  · simp only [indicator_of_notMem hx, smul_zero]

private theorem tailIndicatorValue_norm_le (T : DeepTailData) (s : Set ℝ)
    (hs : MeasurableSet s) (f : DeepTailL2 T) :
    ‖tailIndicatorValue T s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [tailIndicatorValue_coeFn T s hs f] with x hx
  rw [hx]
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs]
  · rw [indicator_of_notMem hxs, norm_zero]
    exact norm_nonneg _

private def tailIndicatorLinear (T : DeepTailData) (s : Set ℝ) (hs : MeasurableSet s) :
    DeepTailL2 T →ₗ[ℝ] DeepTailL2 T where
  toFun := tailIndicatorValue T s hs
  map_add' := tailIndicatorValue_add T s hs
  map_smul' := tailIndicatorValue_smul T s hs

private theorem tailIndicatorLinear_apply (T : DeepTailData) (s : Set ℝ)
    (hs : MeasurableSet s) (f : DeepTailL2 T) :
    tailIndicatorLinear T s hs f = tailIndicatorValue T s hs f := rfl

/-- Multiplication by a measurable indicator is a contraction on the actual
weighted L² space. In particular no finite-total-mass hypothesis is used. -/
def tailIndicator (T : DeepTailData) (s : Set ℝ) (hs : MeasurableSet s) :
    DeepTailL2 T →L[ℝ] DeepTailL2 T :=
  (tailIndicatorLinear T s hs).mkContinuous 1
    (fun f => by simpa only [tailIndicatorLinear_apply, one_mul] using
      tailIndicatorValue_norm_le T s hs f)

private theorem tailIndicator_apply (T : DeepTailData) (s : Set ℝ)
    (hs : MeasurableSet s) (f : DeepTailL2 T) :
    tailIndicator T s hs f = tailIndicatorValue T s hs f := by
  rw [tailIndicator, LinearMap.mkContinuous_apply, tailIndicatorLinear_apply]

theorem tailIndicator_coeFn (T : DeepTailData) (s : Set ℝ) (hs : MeasurableSet s)
    (f : DeepTailL2 T) :
    (tailIndicator T s hs f : ℝ → ℝ) =ᵐ[deepTailMeasure T]
      s.indicator (f : ℝ → ℝ) := by
  rw [tailIndicator_apply]
  exact tailIndicatorValue_coeFn T s hs f

theorem tailIndicator_norm_le (T : DeepTailData) (s : Set ℝ) (hs : MeasurableSet s) :
    ‖tailIndicator T s hs‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [tailIndicator_apply, one_mul] using tailIndicatorValue_norm_le T s hs f

theorem tailIndicator_eq_zero_iff (T : DeepTailData) (s : Set ℝ)
    (hs : MeasurableSet s) (f : DeepTailL2 T) :
    tailIndicator T s hs f = 0 ↔ ∀ᵐ x ∂deepTailMeasure T, x ∈ s → f x = 0 := by
  constructor
  · intro h
    have he := tailIndicator_coeFn T s hs f
    rw [h] at he
    filter_upwards [he, Lp.coeFn_zero ℝ 2 (deepTailMeasure T)] with x hx hz
    simp only [Pi.zero_apply] at hz
    intro hxs
    rw [indicator_of_mem hxs] at hx
    exact hx.symm.trans hz
  · intro h
    apply Lp.ext
    filter_upwards [tailIndicator_coeFn T s hs f, h,
      Lp.coeFn_zero ℝ 2 (deepTailMeasure T)] with x hx hf hz
    simp only [Pi.zero_apply] at hz
    rw [hx, hz]
    by_cases hxs : x ∈ s
    · rw [indicator_of_mem hxs, hf hxs]
    · exact indicator_of_notMem hxs _

/-- Both coordinates of the closed Dirichlet form are zero outside its
interval. This follows by continuity of restriction, so it applies to arbitrary
energy limits, not just classical functions. -/
theorem tailFormLift_ae_zero_outside {T : DeepTailData} {endCut : ℝ}
    {p : DeepTailL2 T × DeepTailL2 T} (hp : p ∈ TailFormLift T endCut) :
    (∀ᵐ x ∂deepTailMeasure T, x ∉ Ioo T.entrance endCut → p.1 x = 0) ∧
      (∀ᵐ x ∂deepTailMeasure T, x ∉ Ioo T.entrance endCut → p.2 x = 0) := by
  let S : Set ℝ := (Ioo T.entrance endCut)ᶜ
  let Q : DeepTailL2 T →L[ℝ] DeepTailL2 T :=
    tailIndicator T S measurableSet_Ioo.compl
  have hclosed : IsClosed {q : DeepTailL2 T × DeepTailL2 T |
      Q q.1 = 0 ∧ Q q.2 = 0} :=
    (isClosed_eq (Q.continuous.comp continuous_fst) continuous_const).inter
      (isClosed_eq (Q.continuous.comp continuous_snd) continuous_const)
  have hcore : TailEnergyCore T endCut ⊆
      {q : DeepTailL2 T × DeepTailL2 T | Q q.1 = 0 ∧ Q q.2 = 0} := by
    rintro q ⟨φ, hφ, hc, hs, hbase, hderiv⟩
    constructor
    · apply (tailIndicator_eq_zero_iff T S measurableSet_Ioo.compl q.1).mpr
      filter_upwards [hbase] with x hx
      intro hxs
      rw [hx]
      exact image_eq_zero_of_notMem_tsupport (fun h => hxs (hs h))
    · apply (tailIndicator_eq_zero_iff T S measurableSet_Ioo.compl q.2).mpr
      filter_upwards [hderiv] with x hx
      intro hxs
      rw [hx]
      exact image_eq_zero_of_notMem_tsupport
        (fun h => hxs (hs (tsupport_deriv_subset h)))
  have hq : Q p.1 = 0 ∧ Q p.2 = 0 := (closure_minimal hcore hclosed) hp
  exact ⟨(tailIndicator_eq_zero_iff T S measurableSet_Ioo.compl p.1).mp hq.1,
    (tailIndicator_eq_zero_iff T S measurableSet_Ioo.compl p.2).mp hq.2⟩

end ContinuousFlexibility.Radial
