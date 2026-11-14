module

public import ContinuousFlexibility.Analysis.N06WeakGraphParity

/-!
# A single canonical cylinder's actual weak graph package

The package retains one family of H2 modal representatives, the precise
finite field cutoffs, their original L2 limits, all weak angular jets and
the five reflection signs. Its sole analytic input is the actual weak PDE.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

structure N06UnitWeakGraphData
    {S : PhysicalSpacesData} {Kc : CanonicalData S} {m b : ℕ}
    (a c V : ℝ → ℝ)
    (U F : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S Kc m)) (K : ℝ) where
  modes : ℕ → ℝ → ℝ
  representative : ∀ i, N06WeakModeRepresentative a c V
    (n06HalfCosineCoefficient (U 0) i) (n06HalfCosineCoefficient (F 0) i) (modes i)
      (((2 * i : ℕ) : ℝ))
  field : Fin 5 → PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S Kc m)
  cutMemLp : ∀ N : ℕ, ∀ k : Fin (b + 1), ∀ r : Fin 5, MemLp
    (n06WeakFiniteGraphFields (Finset.range (N + 1)) modes k.val r) 2
      (canonicalMeasure S Kc m)
  cut_tendsto : ∀ k r, Tendsto (fun N => (cutMemLp N k r).toLp
    (n06WeakFiniteGraphFields (Finset.range (N + 1)) modes k.val r)) atTop (𝓝 (field r k))
  weakAngular : ∀ r k, WeakCanonicalAngularDerivative S Kc m (field r 0) (field r k) k.val
  reflection : ∀ r, (fun p : PolarPoint => field r 0 (p.1, Real.pi - p.2))
    =ᵐ[canonicalMeasure S Kc m] fun p => n06CubicGraphParity r * field r 0 p
  norm_sq_bound : (∑ r : Fin 5, ‖field r‖ ^ 2) ≤
    16384 * K ^ 10 * (‖F‖ ^ 2 + ‖U‖ ^ 2)

/-- Every field row obeys the same useful unsquared graph estimate. -/
theorem N06UnitWeakGraphData.field_norm_le
    {S : PhysicalSpacesData} {Kc : CanonicalData S} {m b : ℕ}
    {a c V : ℝ → ℝ}
    {U F : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S Kc m)} {K : ℝ}
    (P : N06UnitWeakGraphData a c V U F K) (hK : 0 ≤ K) (r : Fin 5) :
    ‖P.field r‖ ≤ 128 * K ^ 5 * (‖F‖ + ‖U‖) := by
  have hsingle : ‖P.field r‖ ^ 2 ≤ ∑ i : Fin 5, ‖P.field i‖ ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg ‖P.field i‖) (Finset.mem_univ r)
  have hsum : ‖F‖ ^ 2 + ‖U‖ ^ 2 ≤ (‖F‖ + ‖U‖) ^ 2 := by
    nlinarith only [mul_nonneg (norm_nonneg F) (norm_nonneg U)]
  have hsquare : ‖P.field r‖ ^ 2 ≤ (128 * K ^ 5 * (‖F‖ + ‖U‖)) ^ 2 := by
    calc
      _ ≤ 16384 * K ^ 10 * (‖F‖ ^ 2 + ‖U‖ ^ 2) := hsingle.trans P.norm_sq_bound
      _ ≤ 16384 * K ^ 10 * (‖F‖ + ‖U‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) (pow_nonneg hK 10))
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsquare

/-- Actual weak canonical data produce the complete graph package. The
coefficient assumptions are exactly the scalar graph theorem's assumptions. -/
theorem n06_unitWeakGraphData_nonempty
    {S : PhysicalSpacesData} {Kc : CanonicalData S} {m b : ℕ}
    (hl : Kc.left m = 0) (hr : Kc.right m = 1)
    (U F : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S Kc m))
    (hUeven : (fun p : PolarPoint => U 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S Kc m] (U 0 : PolarPoint → ℝ))
    (hFeven : (fun p : PolarPoint => F 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S Kc m] (F 0 : PolarPoint → ℝ))
    (hUjets : ∀ k, WeakCanonicalAngularDerivative S Kc m (U 0) (U k) k.val)
    (hFjets : ∀ k, WeakCanonicalAngularDerivative S Kc m (F 0) (F k) k.val)
    {a c V q : ℝ → ℝ} {K : ℝ}
    (ha : ContDiff ℝ ∞ a) (hc : Continuous c) (hV : Continuous V) (hq : ContDiff ℝ 2 q)
    (hweak : ∀ φ, CanonicalTest S Kc m φ →
      (∫ p, U 0 p * n06UnitReferenceTestOperator a c V φ p ∂canonicalMeasure S Kc m) =
        ∫ p, F 0 p * φ p ∂canonicalMeasure S Kc m)
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K) :
    Nonempty (N06UnitWeakGraphData a c V U F K) := by
  obtain ⟨v, hv, hgraph, G, hlim, hbound⟩ := n06_canonical_unit_weak_graph_complete
    hl hr U F hUeven hFeven hUjets hFjets ha hc hV hq hweak
    hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂
  let H : Fin 5 → PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S Kc m) :=
    fun r => WithLp.toLp 2 (fun k => G k r)
  have hweakG := n06_weak_graph_limit_angular_jets hl hr v
    (fun i => (hv i).memLp) (fun i => (hv i).firstMemLp)
    (fun i => (hv i).secondMemLp) hgraph G hlim
  have hparity := n06_weak_graph_limit_reflection v hgraph G hlim
  refine ⟨{
    modes := v
    representative := hv
    field := H
    cutMemLp := hgraph
    cut_tendsto := hlim
    weakAngular := fun r k => hweakG k r
    reflection := hparity
    norm_sq_bound := ?_ }⟩
  calc
    (∑ r : Fin 5, ‖H r‖ ^ 2) = ∑ k : Fin (b + 1), ∑ r : Fin 5, ‖G k r‖ ^ 2 := by
      simp only [H, PiLp.norm_sq_eq_of_L2, PiLp.toLp_apply]
      rw [Finset.sum_comm]
    _ ≤ 16384 * K ^ 10 *
        ((∑ k : Fin (b + 1), ‖F k‖ ^ 2) + ∑ k : Fin (b + 1), ‖U k‖ ^ 2) := hbound
    _ = 16384 * K ^ 10 * (‖F‖ ^ 2 + ‖U‖ ^ 2) := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]

end ContinuousFlexibility.Analysis
