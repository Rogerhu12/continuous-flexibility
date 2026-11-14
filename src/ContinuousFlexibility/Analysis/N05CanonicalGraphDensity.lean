module

public import ContinuousFlexibility.Analysis.N05CanonicalEvenMollifiedJets
public import ContinuousFlexibility.Analysis.N05CanonicalFiniteApproximation

/-!
# Density of the actual smooth canonical graph core

Smooth periodic even tests are dense in each finite angular weak-jet
row. Finite-cell truncation then proves that the span of their genuine
single-cell graph realizations is dense in the full canonical closed
volume graph, at every finite angular order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal

def n05CanonicalSmoothRowCarrier (S : PhysicalSpacesData) (K : CanonicalData S)
    (m s : ℕ) : Set (PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m)) :=
  {v | ∃ (φ : PolarPoint → ℝ) (hφ : CanonicalTest S K m φ),
    (∀ p : PolarPoint, φ (p.1, Real.pi - p.2) = φ p) ∧
      WithLp.toLp 2 (fun j : Fin (s + 1) => n05CanonicalSmoothJet S K m hφ.1 j.val) = v}

theorem n05CanonicalSmoothRow_mem_closure (S : PhysicalSpacesData)
    (K : CanonicalData S) (m s : ℕ)
    (v : PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m))
    (heven : n05CanonicalReflection S K m (v 0) = v 0)
    (hweak : ∀ j : Fin (s + 1), WeakCanonicalAngularDerivative S K m (v 0) (v j) j.val) :
    v ∈ closure (n05CanonicalSmoothRowCarrier S K m s) := by
  let c (n : ℕ) : PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m) :=
    WithLp.toLp 2 (fun j => n05CanonicalRadialCutoffOperator S K m n (v j))
  have hc : Tendsto c atTop (𝓝 v) := by
    exact (PiLp.continuous_toLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m)).continuousAt.tendsto.comp
      (tendsto_pi_nhds.mpr (fun j => n05CanonicalRadialCutoffOperator_tendsto S K m (v j)))
  apply isClosed_closure.mem_of_tendsto hc
  apply Eventually.of_forall
  intro n
  let a (k : ℕ) : PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m) :=
    WithLp.toLp 2 (fun j => n05CanonicalSmoothJet S K m
      (n05CanonicalEvenCutoffMollification_contDiff S K m n (v 0) k) j.val)
  have ha : Tendsto a atTop (𝓝 (c n)) := by
    exact (PiLp.continuous_toLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m)).continuousAt.tendsto.comp
      (tendsto_pi_nhds.mpr (fun j =>
        n05CanonicalEvenCutoffMollification_jet_tendsto S K m n heven (hweak j)))
  apply mem_closure_of_tendsto ha
  exact Eventually.of_forall fun k =>
    ⟨n05CanonicalEvenCutoffMollification S K m n (v 0) k,
      n05CanonicalEvenCutoffMollification_test S K m n (v 0) k,
      n05CanonicalEvenCutoffMollification_even S K m n (v 0) k, rfl⟩

def n05CanonicalSmoothSingleCarrier (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) : Set (n05CanonicalClosedSubmodule S K s) :=
  {v | ∃ (m : ℕ) (φ : PolarPoint → ℝ) (hφ : CanonicalTest S K m φ)
    (he : ∀ p : PolarPoint, φ (p.1, Real.pi - p.2) = φ p),
      n05CanonicalSmoothSingle S K m s hφ.1 hφ.2.1 he = v}

def n05CanonicalSmoothCoreSubmodule (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) : Submodule ℝ (n05CanonicalClosedSubmodule S K s) :=
  Submodule.span ℝ (n05CanonicalSmoothSingleCarrier S K s)

theorem n05CanonicalFiniteTruncate_singleton_val (S : PhysicalSpacesData)
    (K : CanonicalData S) (s m : ℕ) (v : n05CanonicalClosedSubmodule S K s) :
    (n05CanonicalFiniteTruncate S K s {m} v).val = lp.single 2 m (v.val m) := by
  change n05CanonicalFiniteTruncateRaw S K s {m} v.val = _
  rw [n05CanonicalFiniteTruncateRaw_eq_sum]
  simp only [Finset.sum_singleton]

theorem n05CanonicalSingle_mem_smoothCoreClosure (S : PhysicalSpacesData)
    (K : CanonicalData S) (s m : ℕ) (v : n05CanonicalClosedSubmodule S K s) :
    n05CanonicalFiniteTruncate S K s {m} v ∈
      closure (n05CanonicalSmoothCoreSubmodule S K s : Set (n05CanonicalClosedSubmodule S K s)) := by
  have hv : v.val ∈ canonicalVolumeGraph S K s := by
    rw [← n05CanonicalClosedSubmodule_carrier]
    exact v.property
  have hrow := n05CanonicalSmoothRow_mem_closure S K m s (v.val m)
    ((n05CanonicalReflection_fixed_iff S K m (v.val m 0)).mpr (hv.1 m)) (hv.2 m)
  have hc :=
    (lp.isometry_single (p := (2 : ENNReal))
      (E := fun k : ℕ => PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K k)) m).continuous
  have hi := mem_closure_image hc.continuousAt hrow
  rw [closure_subtype, n05CanonicalFiniteTruncate_singleton_val]
  apply closure_mono ?_ hi
  rintro w ⟨row, ⟨φ, hφ, he, rfl⟩, rfl⟩
  exact ⟨n05CanonicalSmoothSingle S K m s hφ.1 hφ.2.1 he,
    Submodule.subset_span ⟨m, φ, hφ, he, rfl⟩, rfl⟩

theorem n05CanonicalSmoothCoreSubmodule_dense (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) :
    Dense (n05CanonicalSmoothCoreSubmodule S K s : Set (n05CanonicalClosedSubmodule S K s)) := by
  intro v
  have hs (m : ℕ) : n05CanonicalFiniteTruncate S K s {m} v ∈
      (n05CanonicalSmoothCoreSubmodule S K s).topologicalClosure :=
    n05CanonicalSingle_mem_smoothCoreClosure S K s m v
  have ht : Tendsto (fun q : Finset ℕ => ∑ m ∈ q, n05CanonicalFiniteTruncate S K s {m} v)
      atTop (𝓝 v) := by
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun q : Finset ℕ => (n05CanonicalClosedSubmodule S K s).subtypeL
      (∑ m ∈ q, n05CanonicalFiniteTruncate S K s {m} v))
      atTop (𝓝 ((n05CanonicalClosedSubmodule S K s).subtypeL v))
    simp only [map_sum, Submodule.subtypeL_apply, n05CanonicalFiniteTruncate_singleton_val]
    exact lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) v.val
  apply isClosed_closure.mem_of_tendsto ht
  exact Eventually.of_forall fun q =>
    (n05CanonicalSmoothCoreSubmodule S K s).topologicalClosure.sum_mem (fun m _ => hs m)

end ContinuousFlexibility.Statements
