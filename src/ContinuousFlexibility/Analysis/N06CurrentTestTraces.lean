import ContinuousFlexibility.Analysis.N06CurrentInverseTestJets
import ContinuousFlexibility.Analysis.N05CanonicalBoundarySymmetry
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import ContinuousFlexibility.Analysis.N05N06ClosedChartBridge

/-!
# Genuine closed traces of the current transformed physical test

The actual stored inverse is smooth on the closed canonical cylinder by
its boundary inverse germs. The inverse pullback and its genuine jets
therefore have bounded derivatives on the compact canonical tile.
Lipschitz extension supplies global representatives with the correct
closed traces. Their physical values use the actual closed moving domain
and the two genuine closed inverse identities.
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
function evaluated at that point. Both stored maps satisfy the genuine closed inverse identities. -/
theorem n06_inverseChart_comp_exists_trace
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ)
    {f : PolarPoint → ℝ}
    (hf : ∀ x : PolarPoint, x ∈ physicalPieceClosed S K z m →
      ContDiffAt ℝ ∞ f x) :
    ∃ M : ℝ≥0, ∃ g : PolarPoint → ℝ, LipschitzWith M g ∧
      EqOn g (fun p => f (K.inverseChart z m p))
        (Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi) ∧
      ∀ x ∈ physicalPieceClosed S K z m ∩ (univ ×ˢ Icc (0 : ℝ) Real.pi),
        g (K.chart z m x) = f x := by
  let Q : Set PolarPoint := Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi
  let R : Set PolarPoint := Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi
  let g₀ : PolarPoint → ℝ := fun p => f (K.inverseChart z m p)
  have hb := h04.1.boundary z hz hs m
  have hcomp (p : PolarPoint) (hp : p ∈ Q) : ContDiffAt ℝ ∞ g₀ p := by
    have hpc : p ∈ canonicalClosed S K m := ⟨hp.1, mem_univ _⟩
    exact (hf _ (hb.2.1 hpc)).comp p
      (n04b_inverseChart_contDiffAt_closed h04.1 hz hs m hpc)
  have hderiv : ContinuousOn (fderiv ℝ g₀) Q := fun p hp =>
    ((hcomp p hp).fderiv_right (m := ∞) (by simp)).continuousAt.continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hderiv.norm
  let M : ℝ≥0 := ⟨max M₀ 0, le_max_right _ _⟩
  have hbound : ∀ p ∈ Q, ‖fderiv ℝ g₀ p‖₊ ≤ M := by
    intro p hp
    exact (hM₀ ⟨p, hp, rfl⟩).trans (le_max_left _ _)
  have hLip : LipschitzOnWith M g₀ Q :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun p hp => (hcomp p hp).differentiableAt (by simp)) hbound
      ((convex_Icc _ _).prod (convex_Icc _ _))
  obtain ⟨g, hg, he⟩ := hLip.extend_real
  have hRQ : R ⊆ Q := Set.prod_mono Ioo_subset_Icc_self Ioc_subset_Icc_self
  refine ⟨M, g, hg, he.symm.mono hRQ, ?_⟩
  intro x hx
  have hFx := (n05_canonicalChart_closedAngular_maps h04 hz hs m).1 hx
  calc
    g (K.chart z m x) = f (K.inverseChart z m (K.chart z m x)) := (he hFx).symm
    _ = f x := congrArg f (hb.2.2.1 x hx.1)

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
      physicalPieceClosed S K z m ∩ (univ ×ˢ Icc (0 : ℝ) Real.pi),
    value (K.chart z m x) = φ x / K.height z m x
  physical_radial : ∀ x ∈
      physicalPieceClosed S K z m ∩ (univ ×ˢ Icc (0 : ℝ) Real.pi),
    radial (K.chart z m x) = n06InverseChartDerivative (K.chart z m) (1, 0)
      (fun q => φ q / K.height z m q) x
  physical_angular : ∀ x ∈
      physicalPieceClosed S K z m ∩ (univ ×ˢ Icc (0 : ℝ) Real.pi),
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
  have hb := (h04.1.boundary z hz hs m).2.2.2.2.1
  have hc := h04.1.charts z hz hs m
  have hf (x : PolarPoint) (hx : x ∈ physicalPieceClosed S K z m) :
      ContDiffAt ℝ ∞ f x := hφ.contDiffAt.div (hb x hx).2.1 (hb x hx).2.2.2.ne'
  have hfr (x : PolarPoint) (hx : x ∈ physicalPieceClosed S K z m) :
      ContDiffAt ℝ ∞ fr x :=
    n06InverseChartDerivative_contDiffAt (1, 0) (hb x hx).1 (hb x hx).2.2.1 (hf x hx)
  have hft (x : PolarPoint) (hx : x ∈ physicalPieceClosed S K z m) :
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
      ((hf _ (subset_closure (hc.2.1 hpc))).differentiableAt (by simp))).symm
  · intro p hp
    have hpc : p ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
    exact (heWt hp).trans (n06_current_inverseChart_comp_fderiv h04 hz hs m (0, 1) hpc
      ((hf _ (subset_closure (hc.2.1 hpc))).differentiableAt (by simp))).symm

end ContinuousFlexibility.Statements
