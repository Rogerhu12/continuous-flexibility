module

public import ContinuousFlexibility.Analysis.N07aForwardCoefficients
public import ContinuousFlexibility.Scalar.WeightedCoefficientAlgebra

/-!
# A complete finite coefficient product costs one material power

Sampled coefficient envelopes have every positive subpower bound. Finite
sums and products preserve this property. The exponent is chosen only
after the complete finite expression has been formed, so the final cost
is one power of M, independently of the length of a normal expansion.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

def N07aSampleSubpower (T : MaterialData) {S : PhysicalSpacesData}
    (K : CanonicalData S) (f : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ m,
    |f m| ≤ C * T.M (T.sample (K.cell m)) ^ δ

namespace N07aSampleSubpower

theorem const (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (c : ℝ) :
    N07aSampleSubpower T K (fun _ => c) := by
  intro δ hδ
  refine ⟨|c| + 1, by positivity, fun m => ?_⟩
  have hm := (hT.2.1 _
    (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))).2.2.2
  have hp : 1 ≤ T.M (T.sample (K.cell m)) ^ δ := Real.one_le_rpow hm hδ.le
  calc
    |c| ≤ |c| + 1 := by linarith
    _ ≤ (|c| + 1) * T.M (T.sample (K.cell m)) ^ δ :=
      le_mul_of_one_le_right (by positivity) hp

theorem e0_rpow (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (A : ℝ) :
    N07aSampleSubpower T K (fun m => T.E0 (T.sample (K.cell m)) ^ A) := by
  intro δ hδ
  obtain ⟨C, hC, hCb⟩ := materialE0_rpow_le_subpowerM hT A hδ
  refine ⟨C, hC, fun m => ?_⟩
  have hm := materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m)
  rw [abs_of_nonneg (Real.rpow_nonneg (hT.2.1 _ hm).2.2.1.le _)]
  exact hCb _ hm

theorem mono {f g : ℕ → ℝ} (hf : N07aSampleSubpower T K f)
    (hg : ∀ m, |g m| ≤ |f m|) : N07aSampleSubpower T K g := by
  intro δ hδ
  obtain ⟨C, hC, hCb⟩ := hf δ hδ
  exact ⟨C, hC, fun m => (hg m).trans (hCb m)⟩

theorem add {f g : ℕ → ℝ} (hf : N07aSampleSubpower T K f)
    (hg : N07aSampleSubpower T K g) : N07aSampleSubpower T K (fun m => f m + g m) := by
  intro δ hδ
  obtain ⟨C, hC, hCb⟩ := hf δ hδ
  obtain ⟨B, hB, hBb⟩ := hg δ hδ
  refine ⟨C + B, add_pos hC hB, fun m => ?_⟩
  calc
    |f m + g m| ≤ |f m| + |g m| := abs_add_le _ _
    _ ≤ C * T.M (T.sample (K.cell m)) ^ δ +
        B * T.M (T.sample (K.cell m)) ^ δ := add_le_add (hCb m) (hBb m)
    _ = _ := by ring

theorem mul (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {f g : ℕ → ℝ} (hf : N07aSampleSubpower T K f)
    (hg : N07aSampleSubpower T K g) : N07aSampleSubpower T K (fun m => f m * g m) := by
  intro δ hδ
  obtain ⟨C, hC, hCb⟩ := hf (δ / 2) (half_pos hδ)
  obtain ⟨B, hB, hBb⟩ := hg (δ / 2) (half_pos hδ)
  refine ⟨C * B, mul_pos hC hB, fun m => ?_⟩
  have hm := (hT.2.1 _
    (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))).2.2.2
  have hmp : 0 < T.M (T.sample (K.cell m)) := zero_lt_one.trans_le hm
  calc
    |f m * g m| = |f m| * |g m| := abs_mul _ _
    _ ≤ (C * T.M (T.sample (K.cell m)) ^ (δ / 2)) *
        (B * T.M (T.sample (K.cell m)) ^ (δ / 2)) :=
      mul_le_mul (hCb m) (hBb m) (abs_nonneg _) (by positivity)
    _ = C * B * T.M (T.sample (K.cell m)) ^ δ := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hmp, add_halves]

theorem list_prod (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {ι : Type*} (l : List ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ l, N07aSampleSubpower T K (f i)) :
    N07aSampleSubpower T K (fun m => (l.map (fun i => f i m)).prod) := by
  induction l with
  | nil => simpa only [List.map_nil, List.prod_nil] using const hD hT (K := K) 1
  | cons i l ih =>
    simpa only [List.map_cons, List.prod_cons] using
      mul hD hT (hf i List.mem_cons_self)
        (ih (fun j hj => hf j (List.mem_cons_of_mem i hj)))

theorem list_sum (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {ι : Type*} (l : List ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ l, N07aSampleSubpower T K (f i)) :
    N07aSampleSubpower T K (fun m => (l.map (fun i => f i m)).sum) := by
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil] using const hD hT (K := K) 0
  | cons i l ih =>
    simpa only [List.map_cons, List.sum_cons] using
      (hf i List.mem_cons_self).add (ih (fun j hj => hf j (List.mem_cons_of_mem i hj)))

/-- Apply this once to the complete coefficient expression. -/
theorem one_power {f : ℕ → ℝ} (hf : N07aSampleSubpower T K f) :
    ∃ C : ℝ, 0 < C ∧ ∀ m, |f m| ≤ C * T.M (T.sample (K.cell m)) := by
  simpa only [Real.rpow_one] using hf 1 (by norm_num)

/-- A genuine positive height gain absorbs every complete coefficient
expression, uniformly over all pieces. -/
theorem height_absorption (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {f : ℕ → ℝ} (hf : N07aSampleSubpower T K f) {γ : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m,
      T.H (T.sample (K.cell m)) ^ γ * |f m| ≤ C := by
  obtain ⟨B, hB, hBb⟩ := hf.one_power
  obtain ⟨C, hC, hCb, _⟩ := hT.2.2.2.2.2.2.2.2.2.2.2.2.1 1 γ hγ
  refine ⟨B * C, mul_pos hB hC, fun m => ?_⟩
  have hm := materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m)
  have hH := (hT.2.1 _ hm).2.1
  calc
    T.H (T.sample (K.cell m)) ^ γ * |f m| ≤
        T.H (T.sample (K.cell m)) ^ γ * (B * T.M (T.sample (K.cell m))) :=
      mul_le_mul_of_nonneg_left (hBb m) (Real.rpow_nonneg hH.le _)
    _ = B * (T.H (T.sample (K.cell m)) ^ γ * T.M (T.sample (K.cell m))) := by ring
    _ ≤ B * C := mul_le_mul_of_nonneg_left
      (by simpa only [Real.rpow_one] using hCb _ hm) hB.le

end N07aSampleSubpower

end ContinuousFlexibility.Analysis
