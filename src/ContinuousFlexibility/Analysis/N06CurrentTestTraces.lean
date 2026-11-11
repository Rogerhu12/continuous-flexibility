import ContinuousFlexibility.Analysis.N06CurrentInverseTestJets
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Genuine closed traces of the current transformed physical test

The original inverse chart is only used on its open domain. Its actual
directional derivatives are pullbacks of smooth physical vector-field
derivatives. Compact physical bounds make these functions Lipschitz on
the measured canonical rectangle. Lipschitz extension then supplies
continuous representatives for the value and first jets.

Their values on the physical boundary follow from the actual forward
identity by continuity from the interior. Nothing is asserted about the
arbitrary totalized inverse-chart values on the canonical boundary.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology NNReal

set_option backward.isDefEq.respectTransparency false

/-- The two coordinate values bound a real plane covector in the product
norm used by the original physical and canonical spaces. -/
theorem n06_plane_covector_norm_le (A : PolarPoint →L[ℝ] ℝ) :
    ‖A‖ ≤ ‖A (1, 0)‖ + ‖A (0, 1)‖ := by
  apply A.opNorm_le_bound (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro v
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by
    ext <;> simp
  have he : A v = v.1 • A (1, 0) + v.2 • A (0, 1) := by
    calc
      A v = A (v.1 • (1, 0) + v.2 • (0, 1)) := congrArg A hv
      _ = _ := by rw [map_add, map_smul, map_smul]
  calc
    ‖A v‖ = ‖v.1 • A (1, 0) + v.2 • A (0, 1)‖ := congrArg norm he
    _ ≤ ‖v.1 • A (1, 0)‖ + ‖v.2 • A (0, 1)‖ := norm_add_le _ _
    _ = ‖v.1‖ * ‖A (1, 0)‖ + ‖v.2‖ * ‖A (0, 1)‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ ‖v‖ * ‖A (1, 0)‖ + ‖v‖ * ‖A (0, 1)‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (norm_fst_le v) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (norm_snd_le v) (norm_nonneg _))
    _ = (‖A (1, 0)‖ + ‖A (0, 1)‖) * ‖v‖ := by ring

/-- A global Lipschitz representative supplies genuine AC radial
slices, with no use of the totalized inverse at an endpoint. -/
theorem n06_lipschitz_radial_slice_ac {M : ℝ≥0} {g : PolarPoint → ℝ}
    (hg : LipschitzWith M g) (θ a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun y => g (y, θ)) a b := by
  have hline : ContDiff ℝ 1 (fun y : ℝ => (y, θ)) := contDiff_id.prodMk contDiff_const
  exact hg.comp_absolutelyContinuousOnInterval hline.contDiffOn.absolutelyContinuousOnInterval

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology NNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The real inverse pullback has a Lipschitz representative on the
closed tile, and its physical boundary trace is the original physical
function evaluated at that point. Only the forward chart is used there. -/
theorem n06_inverseChart_comp_exists_trace
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ)
    {f : PolarPoint → ℝ}
    (hf : ∀ x : PolarPoint, x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) →
      ContDiffAt ℝ ∞ f x) :
    ∃ M : ℝ≥0, ∃ g : PolarPoint → ℝ, LipschitzWith M g ∧
      EqOn g (fun p => f (K.inverseChart z m p))
        (Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi) ∧
      ∀ x ∈ Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi,
        g (K.chart z m x) = f x := by
  let Q : Set PolarPoint :=
    Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi
  let P : Set PolarPoint :=
    Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi
  let R : Set PolarPoint := Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi
  let g₁ := n06InverseChartDerivative (K.chart z m) (1, 0) f
  let g₂ := n06InverseChartDerivative (K.chart z m) (0, 1) f
  have hc := h04.2.2.2.2.2.2.2.1 z hz hs m
  have hb := h04.2.2.2.2.2.2.2.2.1 z hz hs m
  obtain ⟨hFmap, hGmap⟩ := n06_canonicalChart_halfPeriod_maps h04 hz hs m
  have hmap : MapsTo (K.inverseChart z m) R Q := by
    intro p hp
    have hx := hGmap hp
    exact ⟨mem_Icc_of_Ioo hx.1, hx.2.1.le, hx.2.2⟩
  have hjet₁ : ContinuousOn g₁ Q := fun x hx =>
    (n06InverseChartDerivative_contDiffAt (1, 0)
      (hb x hx.1).1 (hb x hx.1).2.2.1 (hf x hx.1)).continuousAt.continuousWithinAt
  have hjet₂ : ContinuousOn g₂ Q := fun x hx =>
    (n06InverseChartDerivative_contDiffAt (0, 1)
      (hb x hx.1).1 (hb x hx.1).2.2.1 (hf x hx.1)).continuousAt.continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (hjet₁.norm.add hjet₂.norm)
  let M : ℝ≥0 := ⟨max M₀ 0, le_max_right _ _⟩
  have hdiff : ∀ p ∈ R,
      DifferentiableAt ℝ (fun q => f (K.inverseChart z m q)) p := by
    intro p hp
    have hpc : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
    exact ((hf _ (hmap hp).1).differentiableAt (by simp)).comp p
      ((hc.2.2.2.2.2.1.contDiffAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds hpc)).differentiableAt (by simp))
  have hbound : ∀ p ∈ R,
      ‖fderiv ℝ (fun q => f (K.inverseChart z m q)) p‖₊ ≤ M := by
    intro p hp
    have hpc : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
    have hfd := (hf _ (hmap hp).1).differentiableAt (by simp)
    have hreal : ‖fderiv ℝ (fun q => f (K.inverseChart z m q)) p‖ ≤ max M₀ 0 := by
      calc
        _ ≤ ‖fderiv ℝ (fun q => f (K.inverseChart z m q)) p (1, 0)‖ +
            ‖fderiv ℝ (fun q => f (K.inverseChart z m q)) p (0, 1)‖ :=
          n06_plane_covector_norm_le _
        _ = ‖g₁ (K.inverseChart z m p)‖ + ‖g₂ (K.inverseChart z m p)‖ := by
          rw [n06_current_inverseChart_comp_fderiv h04 hz hs m (1, 0) hpc hfd,
            n06_current_inverseChart_comp_fderiv h04 hz hs m (0, 1) hpc hfd]
        _ ≤ M₀ := hM₀ ⟨K.inverseChart z m p, hmap hp, rfl⟩
        _ ≤ max M₀ 0 := le_max_left _ _
    exact hreal
  have hLip : LipschitzOnWith M (fun p => f (K.inverseChart z m p)) R :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le hdiff hbound
      ((convex_Ioo _ _).prod (convex_Ioc _ _))
  obtain ⟨g, hg, he⟩ := hLip.extend_real
  refine ⟨M, g, hg, he.symm, ?_⟩
  have hephysical : EqOn (fun x => g (K.chart z m x)) f P := by
    intro x hx
    calc
      _ = f (K.inverseChart z m (K.chart z m x)) := (he (hFmap hx)).symm
      _ = f x := congrArg f (hc.2.2.1 x ⟨hx.1, mem_univ _⟩)
  have hcont : ContinuousOn (fun x => g (K.chart z m x)) Q :=
    hg.continuous.comp_continuousOn
      (fun x hx => (hb x hx.1).1.continuousAt.continuousWithinAt)
  have hfcont : ContinuousOn f Q := fun x hx => (hf x hx.1).continuousAt.continuousWithinAt
  have hPQ : P ⊆ Q := fun _ hx => ⟨mem_Icc_of_Ioo hx.1, hx.2.1.le, hx.2.2⟩
  have hQP : Q ⊆ closure P := by
    simpa only [P, Q, closure_prod_eq, closure_Ioo (h04.2.2.2.1 m).1.ne,
      closure_Ioc Real.pi_pos.ne] using (Subset.rfl : Q ⊆ Q)
  exact hephysical.of_subset_closure hcont hfcont hPQ hQP

/-- The three closed representatives carry their actual physical traces.
Their radial slices are absolutely continuous by their Lipschitz bounds. -/
structure N06CurrentHeightTestTraces
    (S : PhysicalSpacesData) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (φ : PolarPoint → ℝ) where
  value : PolarPoint → ℝ
  radial : PolarPoint → ℝ
  angular : PolarPoint → ℝ
  value_bound : ℝ≥0
  radial_bound : ℝ≥0
  angular_bound : ℝ≥0
  value_lipschitz : LipschitzWith value_bound value
  radial_lipschitz : LipschitzWith radial_bound radial
  angular_lipschitz : LipschitzWith angular_bound angular
  value_eq : EqOn value (canonicalHeight S K z m φ)
    (Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi)
  radial_eq : EqOn radial (radialPartial (canonicalHeight S K z m φ))
    (Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi)
  angular_eq : EqOn angular (angularPartial (canonicalHeight S K z m φ))
    (Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi)
  physical_value : ∀ x ∈
      Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi,
    value (K.chart z m x) = φ x / K.height z m x
  physical_radial : ∀ x ∈
      Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi,
    radial (K.chart z m x) = n06InverseChartDerivative (K.chart z m) (1, 0)
      (fun q => φ q / K.height z m q) x
  physical_angular : ∀ x ∈
      Icc (K.physicalLeft m) (K.physicalRight m) ×ˢ Icc (0 : ℝ) Real.pi,
    angular (K.chart z m x) = n06InverseChartDerivative (K.chart z m) (0, 1)
      (fun q => φ q / K.height z m q) x

/-- The genuine N04 forward data construct the actual current test
traces. No extra endpoint smoothness or boundedness is an input. -/
theorem n06_currentHeightTest_exists_traces
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Nonempty (N06CurrentHeightTestTraces S K z m φ) := by
  let f : PolarPoint → ℝ := fun x => φ x / K.height z m x
  let fr := n06InverseChartDerivative (K.chart z m) (1, 0) f
  let ft := n06InverseChartDerivative (K.chart z m) (0, 1) f
  have hb := h04.2.2.2.2.2.2.2.2.1 z hz hs m
  have hc := h04.2.2.2.2.2.2.2.1 z hz hs m
  have hf (x : PolarPoint) (hx : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      ContDiffAt ℝ ∞ f x := hφ.contDiffAt.div (hb x hx).2.1 (hb x hx).2.2.2.ne'
  have hfr (x : PolarPoint) (hx : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      ContDiffAt ℝ ∞ fr x :=
    n06InverseChartDerivative_contDiffAt (1, 0) (hb x hx).1 (hb x hx).2.2.1 (hf x hx)
  have hft (x : PolarPoint) (hx : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) :
      ContDiffAt ℝ ∞ ft x :=
    n06InverseChartDerivative_contDiffAt (0, 1) (hb x hx).1 (hb x hx).2.2.1 (hf x hx)
  obtain ⟨Mv, W, hW, heW, htW⟩ := n06_inverseChart_comp_exists_trace h04 hz hs m hf
  obtain ⟨Mr, Wr, hWr, heWr, htWr⟩ := n06_inverseChart_comp_exists_trace h04 hz hs m hfr
  obtain ⟨Mt, Wt, hWt, heWt, htWt⟩ := n06_inverseChart_comp_exists_trace h04 hz hs m hft
  refine ⟨{
    value := W
    radial := Wr
    angular := Wt
    value_bound := Mv
    radial_bound := Mr
    angular_bound := Mt
    value_lipschitz := hW
    radial_lipschitz := hWr
    angular_lipschitz := hWt
    value_eq := heW
    radial_eq := ?_
    angular_eq := ?_
    physical_value := htW
    physical_radial := htWr
    physical_angular := htWt
  }⟩
  · intro p hp
    have hpc : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
    exact (heWr hp).trans (n06_current_inverseChart_comp_fderiv h04 hz hs m (1, 0) hpc
      ((hf _ (mem_Icc_of_Ioo (hc.2.1 hpc).1)).differentiableAt (by simp))).symm
  · intro p hp
    have hpc : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
    exact (heWt hp).trans (n06_current_inverseChart_comp_fderiv h04 hz hs m (0, 1) hpc
      ((hf _ (mem_Icc_of_Ioo (hc.2.1 hpc).1)).differentiableAt (by simp))).symm

end ContinuousFlexibility.Statements
