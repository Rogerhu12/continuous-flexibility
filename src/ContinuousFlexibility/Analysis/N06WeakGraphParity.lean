module

public import ContinuousFlexibility.Analysis.N06WeakGraphJetClosure
public import ContinuousFlexibility.Analysis.N06CubicMultiplierSymmetry
public import ContinuousFlexibility.Analysis.N06WeakAngularMultiplier

/-!
# Reflection signs of the actual weak graph fields

The even cosine basis has alternating signs after angular differentiation.
The exact measure-preserving canonical reflection carries those signs
through the original L2 limits, without choosing pointwise representatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n06_referenceAngularBasis_reflection (i : ℕ) (θ : ℝ) :
    referenceAngularBasis i (Real.pi - θ) = referenceAngularBasis i θ := by
  rw [sub_eq_add_neg, add_comm, referenceAngularBasis_periodic,
    referenceAngularBasis_even]

theorem n06_referenceAngularBasis_iterated_reflection (i j : ℕ) (θ : ℝ) :
    iteratedDeriv j (referenceAngularBasis i) (Real.pi - θ) =
      (-1 : ℝ) ^ j * iteratedDeriv j (referenceAngularBasis i) θ := by
  have he : (fun t : ℝ => referenceAngularBasis i (Real.pi - t)) =
      referenceAngularBasis i := funext (n06_referenceAngularBasis_reflection i)
  have h := congrFun (iteratedDeriv_comp_const_sub j (referenceAngularBasis i) Real.pi) θ
  rw [he] at h
  simp only [smul_eq_mul] at h
  have hsign : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  have hs := congrArg (fun x : ℝ => (-1 : ℝ) ^ j * x) h
  simpa only [← mul_assoc, hsign, one_mul] using hs.symm

theorem n06CubicGraphParity_eq_pow_shift (r : Fin 5) :
    n06CubicGraphParity r = (-1 : ℝ) ^ n06WeakFiniteGraphShift r := by
  fin_cases r <;> norm_num [n06CubicGraphParity, n06WeakFiniteGraphShift]

/-- The actual five finite reconstructions have the same signs as their
corresponding cubic multipliers. -/
theorem n06_weak_graph_fields_reflection
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (r : Fin 5) (p : PolarPoint) :
    n06WeakFiniteGraphFields s v 0 r (p.1, Real.pi - p.2) =
      n06CubicGraphParity r * n06WeakFiniteGraphFields s v 0 r p := by
  simp only [n06WeakFiniteGraphFields, r11bFiniteSynthesis, Nat.zero_add,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [n06_referenceAngularBasis_iterated_reflection,
    ← n06CubicGraphParity_eq_pow_shift]
  ring

/-- A fixed reflection factor is closed under actual canonical L2 convergence. -/
theorem n06_canonical_reflection_of_tendsto
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {f : ℕ → CanonicalL2 S K m} {g : CanonicalL2 S K m} (σ : ℝ)
    (hlim : Tendsto f atTop (𝓝 g))
    (hf : ∀ N, (fun p : PolarPoint => f N (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] fun p => σ * f N p) :
    (fun p : PolarPoint => g (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] fun p => σ * g p := by
  let R : CanonicalL2 S K m →ₗᵢ[ℝ] CanonicalL2 S K m :=
    Lp.compMeasurePreservingₗᵢ ℝ (fun p : PolarPoint => (p.1, Real.pi - p.2))
      n06_measurePreserving_canonicalAngularReflection
  have hseq (N : ℕ) : R (f N) = σ • f N := by
    apply Lp.ext
    have hR : (R (f N) : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        fun p => f N (p.1, Real.pi - p.2) :=
      Lp.coeFn_compMeasurePreserving (f N) n06_measurePreserving_canonicalAngularReflection
    filter_upwards [hR, hf N, Lp.coeFn_smul σ (f N)] with p hp hpar hs
    simp only [Pi.smul_apply, smul_eq_mul] at hs
    exact hp.trans (hpar.trans hs.symm)
  have hleft : Tendsto (fun N => R (f N)) atTop (𝓝 (R g)) :=
    (R.continuous.tendsto g).comp hlim
  rw [show (fun N => R (f N)) = (fun N => σ • f N) from funext hseq] at hleft
  have heq : R g = σ • g := tendsto_nhds_unique hleft (hlim.const_smul σ)
  have hR : (R g : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => g (p.1, Real.pi - p.2) :=
    Lp.coeFn_compMeasurePreserving g n06_measurePreserving_canonicalAngularReflection
  rw [heq] at hR
  have hs : ((σ • g : CanonicalL2 S K m) : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] fun p => σ * g p := by
    filter_upwards [Lp.coeFn_smul σ g] with p hp
    exact hp
  exact hR.symm.trans hs

theorem n06_weak_graph_fields_toLp_reflection
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (r : Fin 5)
    (h : MemLp (n06WeakFiniteGraphFields s v 0 r) 2 (canonicalMeasure S K m)) :
    (fun p : PolarPoint => h.toLp (n06WeakFiniteGraphFields s v 0 r)
      (p.1, Real.pi - p.2)) =ᵐ[canonicalMeasure S K m]
      fun p => n06CubicGraphParity r * h.toLp (n06WeakFiniteGraphFields s v 0 r) p := by
  have hreflection :=
    n06_measurePreserving_canonicalAngularReflection.quasiMeasurePreserving.ae_eq_comp
      h.coeFn_toLp
  filter_upwards [hreflection, h.coeFn_toLp] with p hr hp
  change h.toLp (n06WeakFiniteGraphFields s v 0 r) (p.1, Real.pi - p.2) =
    n06WeakFiniteGraphFields s v 0 r (p.1, Real.pi - p.2) at hr
  rw [hr, hp]
  exact n06_weak_graph_fields_reflection s v r p

/-- The strong limits of the five finite fields retain their original
reflection signs, including the two odd mixed/angular fields. -/
theorem n06_weak_graph_limit_reflection
    {S : PhysicalSpacesData} {K : CanonicalData S} {m b : ℕ}
    (v : ℕ → ℝ → ℝ)
    (hgraph : ∀ N : ℕ, ∀ k : Fin (b + 1), ∀ r : Fin 5, MemLp
      (n06WeakFiniteGraphFields (Finset.range (N + 1)) v k.val r) 2 (canonicalMeasure S K m))
    (G : Fin (b + 1) → Fin 5 → CanonicalL2 S K m)
    (hlim : ∀ k r, Tendsto (fun N => (hgraph N k r).toLp
      (n06WeakFiniteGraphFields (Finset.range (N + 1)) v k.val r)) atTop (𝓝 (G k r))) :
    ∀ r, (fun p : PolarPoint => G 0 r (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] fun p => n06CubicGraphParity r * G 0 r p := by
  intro r
  apply n06_canonical_reflection_of_tendsto (n06CubicGraphParity r) (hlim 0 r)
  intro N
  exact n06_weak_graph_fields_toLp_reflection (Finset.range (N + 1)) v r (hgraph N 0 r)

end ContinuousFlexibility.Analysis
