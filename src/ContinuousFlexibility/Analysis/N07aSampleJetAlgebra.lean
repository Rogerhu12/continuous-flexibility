import ContinuousFlexibility.Analysis.N07aSampleJetProducts

/-!
# Fixed coefficient algebra on the actual pieces

Piecewise scalar factors remain sampled subpower envelopes. The bounds
below retain a single state loss when forming the six normal coefficients.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

namespace N07aSampleJetBounds

variable {p : ℕ → Seminorm ℝ E} {U : Set E} {W : ℕ → Set PolarPoint}
  {d : ℕ} {f g : E → ℕ → PolarPoint → ℝ}

omit [TopologicalSpace E] in
theorem sample_mul (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hf : N07aSampleJetBounds T K p U W d f)
    (c : ℕ → ℝ) (hc : N07aSampleSubpower T K c) :
    N07aSampleJetBounds T K p U W d (fun z m x => c m * f z m x) := by
  intro i j
  obtain ⟨e, he, he0, heb⟩ := hf i j
  refine ⟨fun m => |c m| * e m, N07aSampleSubpower.mul hD hT hc.abs he,
    fun m => mul_nonneg (abs_nonneg _) (he0 m), ?_⟩
  intro z hz m x hx
  rw [spaces_mixedDerivative_const_mul, abs_mul]
  exact (mul_le_mul_of_nonneg_left (heb z hz m x hx) (abs_nonneg _)).trans_eq
    (by ring)

omit [TopologicalSpace E] in
theorem neg (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hf : N07aSampleJetBounds T K p U W d f) :
    N07aSampleJetBounds T K p U W d (fun z m x => -f z m x) := by
  simpa only [neg_one_mul] using hf.const_mul hD hT (-1)

omit [TopologicalSpace E] in
theorem sub (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hf : N07aSampleJetBounds T K p U W d f)
    (hg : N07aSampleJetBounds T K p U W d g)
    (hW : ∀ m, IsOpen (W m))
    (hfs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (f z m) (W m))
    (hgs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (g z m) (W m)) :
    N07aSampleJetBounds T K p U W d (fun z m x => f z m x - g z m x) := by
  simpa only [sub_eq_add_neg] using
    hf.add (hg.neg hD hT) hW hfs (fun z hz m => (hgs z hz m).neg)

end N07aSampleJetBounds

def n07aNormalCoefficientFamily (f : Fin 5 → E → ℕ → PolarPoint → ℝ)
    (σ : ℕ → ℝ) (k : Fin 6) : E → ℕ → PolarPoint → ℝ :=
  ![fun z m x => -2 * f 3 z m x * f 1 z m x,
    fun z m x => -f 3 z m x * f 2 z m x,
    fun z m x => mixedDerivative 1 0 (f 3 z m) x * f 0 z m x -
      f 3 z m x * mixedDerivative 0 1 (f 1 z m) x,
    fun z m x => -f 3 z m x *
      (mixedDerivative 1 0 (f 1 z m) x + mixedDerivative 0 1 (f 2 z m) x),
    fun z m x => -f 3 z m x * (σ m * f 4 z m x),
    f 3] k

theorem n07a_normalCoefficientFamily_sampleJetBounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hIp : HasSmoothing p)
    (U : Set E) (W : ℕ → Set PolarPoint) (hW : ∀ m, IsOpen (W m))
    (d : ℕ) (f : Fin 5 → E → ℕ → PolarPoint → ℝ)
    (hf : ∀ k, N07aSampleJetBounds T K p U W d (f k))
    (hfs : ∀ k z, z ∈ U → ∀ m, ContDiffOn ℝ ∞ (f k z m) (W m))
    (σ : ℕ → ℝ) (hσ : ∀ m, |σ m| ≤ 1) :
    ∃ low loss : ℕ, ∀ k : Fin 6,
      N07aSampleJetBounds T K p {z | z ∈ U ∧ p low z ≤ 1} W loss
        (n07aNormalCoefficientFamily f σ k) := by
  obtain ⟨low, loss, hmul⟩ :=
    n07a_sampleJetBounds_mul_uniform hD hT p hp hIp U W hW (d + 1)
  let finalLoss := max loss (d + 1)
  have hf' (k : Fin 5) : N07aSampleJetBounds T K p U W (d + 1) (f k) :=
    (hf k).loss_mono hp (Nat.le_succ d)
  have hj (k : Fin 5) (a b : ℕ) (hab : a + b ≤ 1) :
      N07aSampleJetBounds T K p U W (d + 1)
        (fun z m => mixedDerivative a b (f k z m)) :=
    ((hf k).jet hW (hfs k) a b).loss_mono hp (by omega)
  have hjs (k : Fin 5) (a b : ℕ) (z : E) (hz : z ∈ U) (m : ℕ) :
      ContDiffOn ℝ ∞ (mixedDerivative a b (f k z m)) (W m) :=
    contDiffOn_mixedDerivative (hW m) (hfs k z hz m) a b
  have hm (a b : E → ℕ → PolarPoint → ℝ)
      (ha : N07aSampleJetBounds T K p U W (d + 1) a)
      (hb : N07aSampleJetBounds T K p U W (d + 1) b)
      (has : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (a z m) (W m))
      (hbs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (b z m) (W m)) :
      N07aSampleJetBounds T K p {z | z ∈ U ∧ p low z ≤ 1} W finalLoss
        (fun z m x => a z m x * b z m x) :=
    (hmul a b ha hb has hbs).loss_mono hp (le_max_left _ _)
  refine ⟨low, finalLoss, fun k => ?_⟩
  fin_cases k
  · have h := (hm (f 3) (f 1) (hf' 3) (hf' 1) (hfs 3) (hfs 1)).const_mul hD hT (-2)
    change N07aSampleJetBounds T K p {z | z ∈ U ∧ p low z ≤ 1} W finalLoss
      (fun z m x => -2 * f 3 z m x * f 1 z m x)
    simpa only [mul_assoc] using h
  · have h := (hm (f 3) (f 2) (hf' 3) (hf' 2) (hfs 3) (hfs 2)).neg hD hT
    change N07aSampleJetBounds T K p {z | z ∈ U ∧ p low z ≤ 1} W finalLoss
      (fun z m x => -f 3 z m x * f 2 z m x)
    simpa only [neg_mul] using h
  · have h₁ := hm _ _ (hj 3 1 0 (by omega)) (hf' 0) (hjs 3 1 0) (hfs 0)
    have h₂ := hm _ _ (hf' 3) (hj 1 0 1 (by omega)) (hfs 3) (hjs 1 0 1)
    exact h₁.sub hD hT h₂ hW
      (fun z hz m => (hjs 3 1 0 z hz.1 m).mul (hfs 0 z hz.1 m))
      (fun z hz m => (hfs 3 z hz.1 m).mul (hjs 1 0 1 z hz.1 m))
  · have hsum := (hj 1 1 0 (by omega)).add (hj 2 0 1 (by omega)) hW
      (hjs 1 1 0) (hjs 2 0 1)
    have hsum_s (z : E) (hz : z ∈ U) (m : ℕ) :=
      (hjs 1 1 0 z hz m).add (hjs 2 0 1 z hz m)
    have h := (hm _ _ (hf' 3) hsum (hfs 3) hsum_s).neg hD hT
    change N07aSampleJetBounds T K p {z | z ∈ U ∧ p low z ≤ 1} W finalLoss
      (fun z m x => -f 3 z m x *
        (mixedDerivative 1 0 (f 1 z m) x + mixedDerivative 0 1 (f 2 z m) x))
    simpa only [neg_mul] using h
  · have hsig : N07aSampleSubpower T K (fun m => -σ m) :=
      (N07aSampleSubpower.const hD hT (K := K) 1).mono
        (fun m => by simpa only [abs_neg, abs_one] using hσ m)
    have h := (hm (f 3) (f 4) (hf' 3) (hf' 4) (hfs 3) (hfs 4)).sample_mul
      hD hT (fun m => -σ m) hsig
    have he : (fun z m x => -σ m * (f 3 z m x * f 4 z m x)) =
        n07aNormalCoefficientFamily f σ 4 := by
      funext z m x
      change -σ m * (f 3 z m x * f 4 z m x) = -f 3 z m x * (σ m * f 4 z m x)
      ring
    rw [he] at h
    exact h
  · exact ((hf' 3).restrict (fun _ hz => hz.1)).loss_mono hp (le_max_right _ _)

end ContinuousFlexibility.Analysis
