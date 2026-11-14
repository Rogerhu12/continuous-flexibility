module

public import ContinuousFlexibility.Analysis.N06WeakGraphCompletion
public import ContinuousFlexibility.Analysis.N06WeakTensorCalculus
public import ContinuousFlexibility.Analysis.N06WeakAngularCalculus
public import ContinuousFlexibility.Radial.R11bWeakNormalLimit

/-!
# The graph limits retain their actual weak angular jets

Each weighted radial coefficient is merely L2. Periodic angular integration
by parts nevertheless proves every finite field identity. The original
canonical L2 limits retain those identities by continuity of test pairing.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- One angular differentiation of an actual finite graph field. -/
theorem n06_weak_graph_fields_first_angular
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (r : Fin 5)
    (hw : ∀ i ∈ s, MemLp (n06WeakFiniteGraphCoefficients v r i) 2
      (volume.restrict (Ioo (0 : ℝ) 1))) (k : ℕ)
    {φ : PolarPoint → ℝ} (hφ : n06UnitCanonicalTest φ) :
    (∫ p, n06WeakFiniteGraphFields s v (k + 1) r p * φ p
      ∂cylinderWindowMeasure 0) =
      -(∫ p, n06WeakFiniteGraphFields s v k r p * angularPartial φ p
        ∂cylinderWindowMeasure 0) := by
  have h := n06_finiteSynthesis_weak_angular s (n06WeakFiniteGraphCoefficients v r)
    (fun i => iteratedDeriv (k + n06WeakFiniteGraphShift r) (referenceAngularBasis i)) hw
    (fun i _ => circleFourier_contDiff_iteratedDeriv (contDiff_referenceAngularBasis i) _)
    (fun i _ => circleFourier_periodic_iteratedDeriv (referenceAngularBasis_periodic i) _) hφ
  have hn : k + 1 + n06WeakFiniteGraphShift r =
      (k + n06WeakFiniteGraphShift r) + 1 := by omega
  simpa only [n06WeakFiniteGraphFields, hn, iteratedDeriv_succ] using h

/-- Arbitrary finite angular order, without a radial smoothness hypothesis. -/
theorem n06_weak_graph_fields_angular_pairing
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (r : Fin 5)
    (hw : ∀ i ∈ s, MemLp (n06WeakFiniteGraphCoefficients v r i) 2
      (volume.restrict (Ioo (0 : ℝ) 1))) (k : ℕ)
    {φ : PolarPoint → ℝ} (hφ : n06UnitCanonicalTest φ) :
    (∫ p, n06WeakFiniteGraphFields s v k r p * φ p
      ∂cylinderWindowMeasure 0) =
      (-1 : ℝ) ^ k * ∫ p,
        n06WeakFiniteGraphFields s v 0 r p * mixedDerivative 0 k φ p
          ∂cylinderWindowMeasure 0 := by
  induction k generalizing φ with
  | zero => simp only [pow_zero, one_mul, spaces_mixedDerivative_zero]
  | succ k ih =>
    rw [n06_weak_graph_fields_first_angular s v r hw k hφ,
      ih hφ.n06_angularPartial,
      ← n06_mixedAngular_one_eq_angularPartial hφ.1, n06_mixedAngular_comp, pow_succ]
    ring

/-- The finite identity is the frozen canonical weak derivative predicate,
with the original measure and the actual L2 representatives. -/
theorem n06_weak_graph_fields_canonical_angular
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (hl : K.left m = 0) (hr : K.right m = 1)
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (r : Fin 5)
    (hw : ∀ i ∈ s, MemLp (n06WeakFiniteGraphCoefficients v r i) 2
      (volume.restrict (Ioo (0 : ℝ) 1))) (k : ℕ)
    (h₀ : MemLp (n06WeakFiniteGraphFields s v 0 r) 2 (canonicalMeasure S K m))
    (hₖ : MemLp (n06WeakFiniteGraphFields s v k r) 2 (canonicalMeasure S K m)) :
    WeakCanonicalAngularDerivative S K m
      (h₀.toLp (n06WeakFiniteGraphFields s v 0 r))
      (hₖ.toLp (n06WeakFiniteGraphFields s v k r)) k := by
  intro φ hφ
  have hraw := n06_weak_graph_fields_angular_pairing s v r hw k
    ((n06_unitCanonicalTest_iff hl hr φ).mpr hφ)
  rw [← n06_canonical_unit_measure_eq_window hl hr] at hraw
  calc
    _ = ∫ p, n06WeakFiniteGraphFields s v k r p * φ p
        ∂canonicalMeasure S K m := by
      apply integral_congr_ae
      filter_upwards [hₖ.coeFn_toLp] with p hp
      rw [hp]
    _ = _ := hraw.trans (congrArg (fun x : ℝ => (-1 : ℝ) ^ k * x) (by
      apply integral_congr_ae
      filter_upwards [h₀.coeFn_toLp] with p hp
      rw [hp]))

/-- Actual canonical weak derivatives are closed under original L2 convergence. -/
theorem n06_weak_canonical_angular_of_tendsto
    {S : PhysicalSpacesData} {K : CanonicalData S} {m j : ℕ}
    {f g : ℕ → CanonicalL2 S K m} {u v : CanonicalL2 S K m}
    (hfu : Tendsto f atTop (𝓝 u)) (hgv : Tendsto g atTop (𝓝 v))
    (hweak : ∀ N, WeakCanonicalAngularDerivative S K m (f N) (g N) j) :
    WeakCanonicalAngularDerivative S K m u v j := by
  intro φ hφ
  have hleft := r11b_tendsto_integral_mul_of_L2_tendsto
    (fun N => Lp.memLp (g N)) (Lp.memLp v) hφ.n06_memLp
    (by simpa only [Lp.toLp_coeFn] using hgv)
  have hright := r11b_tendsto_integral_mul_of_L2_tendsto
    (fun N => Lp.memLp (f N)) (Lp.memLp u) (hφ.n06_mixedDerivative 0 j).n06_memLp
    (by simpa only [Lp.toLp_coeFn] using hfu)
  have hseq : (fun N => ∫ p, g N p * φ p ∂canonicalMeasure S K m) =
      (fun N => (-1 : ℝ) ^ j *
        ∫ p, f N p * mixedDerivative 0 j φ p ∂canonicalMeasure S K m) :=
    funext (fun N => hweak N φ hφ)
  rw [hseq] at hleft
  exact tendsto_nhds_unique hleft (hright.const_mul ((-1 : ℝ) ^ j))

/-- Every graph limit produced from the same H2 modal family has all of its
stored weak angular jets. The hypotheses here are supplied by the proved
weak-PDE graph completion theorem. -/
theorem n06_weak_graph_limit_angular_jets
    {S : PhysicalSpacesData} {K : CanonicalData S} {m b : ℕ}
    (hl : K.left m = 0) (hr : K.right m = 1)
    (v : ℕ → ℝ → ℝ)
    (hv₀ : ∀ i, MemLp (v i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₁ : ∀ i, MemLp (deriv (v i)) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₂ : ∀ i, MemLp (deriv (deriv (v i))) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hgraph : ∀ N : ℕ, ∀ k : Fin (b + 1), ∀ r : Fin 5, MemLp
      (n06WeakFiniteGraphFields (Finset.range (N + 1)) v k.val r) 2 (canonicalMeasure S K m))
    (G : Fin (b + 1) → Fin 5 → CanonicalL2 S K m)
    (hlim : ∀ k r, Tendsto (fun N => (hgraph N k r).toLp
      (n06WeakFiniteGraphFields (Finset.range (N + 1)) v k.val r)) atTop (𝓝 (G k r))) :
    ∀ k r, WeakCanonicalAngularDerivative S K m (G 0 r) (G k r) k.val := by
  intro k r
  apply n06_weak_canonical_angular_of_tendsto (hlim 0 r) (hlim k r)
  intro N
  exact n06_weak_graph_fields_canonical_angular hl hr (Finset.range (N + 1)) v r
    (n06_weak_graphCoefficients_memLp (Finset.range (N + 1)) v
      (fun i _ => hv₀ i) (fun i _ => hv₁ i) (fun i _ => hv₂ i) r)
    k.val (hgraph N 0 r) (hgraph N k r)

end ContinuousFlexibility.Analysis
