module

public import ContinuousFlexibility.Analysis.N07aSampleJetBounds
public import ContinuousFlexibility.Analysis.N07aMixedLocalCalculus
public import ContinuousFlexibility.Analysis.TameLocalCalculus

/-!
# Sampled coefficient bounds on state-dependent open sets

The envelope retains subpower growth and the state appears in one fixed
shift of its grading. All operations below act on the original functions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

def N07aStateSampleJetBounds (T : MaterialData) {S : PhysicalSpacesData}
    (K : CanonicalData S) (p : ℕ → Seminorm ℝ E) (U : Set E)
    (W : E → ℕ → Set PolarPoint) (loss : ℕ) (f : E → ℕ → PolarPoint → ℝ) : Prop :=
  ∀ i j : ℕ, ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
    ∀ z ∈ U, ∀ m x, x ∈ W z m →
      |mixedDerivative i j (f z m) x| ≤ e m * (1 + p (i + j + loss) z)

/-- A fixed domain is a special case of a state-dependent domain. -/
theorem N07aSampleJetBounds.to_state
    {p : ℕ → Seminorm ℝ E} {U : Set E} {W : ℕ → Set PolarPoint}
    {d : ℕ} {f : E → ℕ → PolarPoint → ℝ}
    (hf : N07aSampleJetBounds T K p U W d f) :
    N07aStateSampleJetBounds T K p U (fun _ => W) d f := hf

namespace N07aStateSampleJetBounds

variable {p : ℕ → Seminorm ℝ E} {U U' : Set E} {W : E → ℕ → Set PolarPoint}
  {d d' : ℕ} {f g : E → ℕ → PolarPoint → ℝ}

theorem restrict (hf : N07aStateSampleJetBounds T K p U W d f) (hU : U' ⊆ U) :
    N07aStateSampleJetBounds T K p U' W d f := by
  intro i j
  obtain ⟨e, he, he0, heb⟩ := hf i j
  exact ⟨e, he, he0, fun z hz => heb z (hU hz)⟩

theorem loss_mono (hp : Monotone p) (hdd : d ≤ d')
    (hf : N07aStateSampleJetBounds T K p U W d f) :
    N07aStateSampleJetBounds T K p U W d' f := by
  intro i j
  obtain ⟨e, he, he0, heb⟩ := hf i j
  refine ⟨e, he, he0, fun z hz m x hx => (heb z hz m x hx).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (hp (Nat.add_le_add_left hdd (i + j)) z)) (he0 m)

theorem add (hf : N07aStateSampleJetBounds T K p U W d f)
    (hg : N07aStateSampleJetBounds T K p U W d g)
    (hW : ∀ z ∈ U, ∀ m, IsOpen (W z m))
    (hfs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (f z m) (W z m))
    (hgs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (g z m) (W z m)) :
    N07aStateSampleJetBounds T K p U W d (fun z m x => f z m x + g z m x) := by
  intro i j
  obtain ⟨e, he, he0, heb⟩ := hf i j
  obtain ⟨a, ha, ha0, hab⟩ := hg i j
  refine ⟨fun m => e m + a m, he.add ha, fun m => add_nonneg (he0 m) (ha0 m), ?_⟩
  intro z hz m x hx
  rw [n07a_mixedDerivative_add_on (hW z hz m) (hfs z hz m) (hgs z hz m) i j hx]
  exact (abs_add_le _ _).trans ((add_le_add (heb z hz m x hx)
    (hab z hz m x hx)).trans_eq (by ring))

theorem const_mul (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hf : N07aStateSampleJetBounds T K p U W d f) (c : ℝ) :
    N07aStateSampleJetBounds T K p U W d (fun z m x => c * f z m x) := by
  intro i j
  obtain ⟨e, he, he0, heb⟩ := hf i j
  refine ⟨fun m => |c| * e m,
    N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT |c|) he,
    fun m => mul_nonneg (abs_nonneg _) (he0 m), ?_⟩
  intro z hz m x hx
  rw [spaces_mixedDerivative_const_mul, abs_mul]
  exact (mul_le_mul_of_nonneg_left (heb z hz m x hx) (abs_nonneg _)).trans_eq
    (by ring)

theorem jet (hf : N07aStateSampleJetBounds T K p U W d f)
    (hW : ∀ z ∈ U, ∀ m, IsOpen (W z m))
    (hfs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (f z m) (W z m)) (a b : ℕ) :
    N07aStateSampleJetBounds T K p U W (a + b + d)
      (fun z m => mixedDerivative a b (f z m)) := by
  intro i j
  obtain ⟨e, he, he0, heb⟩ := hf (i + a) (j + b)
  refine ⟨e, he, he0, fun z hz m x hx => ?_⟩
  rw [n07a_mixedDerivative_mixedDerivative_on (hW z hz m) (hfs z hz m) i j a b hx]
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heb z hz m x hx

end N07aStateSampleJetBounds

end ContinuousFlexibility.Analysis
