import ContinuousFlexibility.Analysis.N01cPhysicalGraphJets
import ContinuousFlexibility.Analysis.N01cPhysicalGraphTermBounds

/-!
# Raw bounds for the complete genuine state-flow composition

All ordered-partition terms are estimated before normalization. The
finite outer-word sum costs only constants and material powers. Its
spatial exponent is the original angular order plus a prefix-dependent
multiple of the original state order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

def n01c_graphPartitionWordCount (N : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition N, (Fintype.card (StateAngleWord c.length) : ℝ)

private theorem n01c_graphWordEnvelope_mono
    {l N : ℕ} (hl : l ≤ N) {C₀ C₁ L E A₀ A₁ : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 1 ≤ C₁) (hL : 1 ≤ L)
    (hE : 1 ≤ E) (hA₁ : 0 ≤ A₁) :
    (C₀ * C₁ ^ l * L ^ l) * E ^ (A₀ + A₁ * (l : ℝ)) ≤
      (C₀ * C₁ ^ N * L ^ N) * E ^ (A₀ + A₁ * (N : ℝ)) := by
  have hcoeff : C₀ * C₁ ^ l * L ^ l ≤ C₀ * C₁ ^ N * L ^ N :=
    mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC₁ hl) hC₀)
      (pow_le_pow_right₀ hL hl) (pow_nonneg (zero_le_one.trans hL) _)
      (mul_nonneg hC₀ (pow_nonneg (zero_le_one.trans hC₁) _))
  have hpower := Real.rpow_le_rpow_of_exponent_le hE
    (add_le_add (le_rfl : A₀ ≤ A₀)
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hl) hA₁))
  exact mul_le_mul hcoeff hpower (Real.rpow_nonneg (zero_le_one.trans hE) _)
    (mul_nonneg (mul_nonneg hC₀ (pow_nonneg (zero_le_one.trans hC₁) _))
      (pow_nonneg (zero_le_one.trans hL) _))

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]

/-- A pointwise estimate for the complete actual graph jet. The outer
bounds are uniform in their real angle argument. No size of that angle
is included in the state grading. -/
theorem stateFlow_composition_raw_bound
    {U : Set X} {Θ f : X × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) Θ)
    (Ja : ∀ b : ℕ, ∀ θ : ℝ, SmoothDirections U
      (fun x => iteratedDeriv b (fun η => Θ (x, η)) θ))
    (K : SmoothDirections (U ×ˢ (univ : Set ℝ)) f)
    (Ka : ∀ b : ℕ, ∀ θ : ℝ, SmoothDirections U
      (fun x => iteratedDeriv b (fun η => f (x, η)) θ))
    {N : ℕ} (input : StateAngleWord N) (hk : 0 < input.stateArity)
    (p₀ p₁ : Seminorm ℝ X) (n s offset : ℕ)
    {x : X} (hx : x ∈ U) (θ : ℝ) (v : Fin input.stateArity → X)
    (hv₀ : ∀ i, p₀ (v i) ≤ 1) {R : ℝ} (hR : 1 ≤ R)
    (hv₁ : ∀ i, p₁ (v i) ≤ R)
    {δ C₀ C₁ E A₀ A₁ H L : ℝ} (hδ : 0 ≤ δ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 1 ≤ C₁) (hE : 1 ≤ E) (hA₁ : 0 ≤ A₁)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L)
    (houter : ∀ j b, j + b ≤ N → ∀ η (u : Fin j → X),
      (∀ i, p₀ (u i) ≤ 1) → (∀ i, p₁ (u i) ≤ R) →
      δ * |(Ka b η).D j x u| ≤
        C₀ * E ^ A₀ * parameterHeightWeight H j *
          R ^ (((n + b : ℕ) : ℝ) / ((s : ℝ) + 1)))
    (hflow : ∀ j b, 0 < j + b → j + b ≤ N → j ≤ input.stateArity →
      ∀ u : Fin j → X, (∀ i, p₀ (u i) ≤ 1) → (∀ i, p₁ (u i) ≤ R) →
        |(Ja b θ).D j x u| ≤
          C₁ * E ^ A₁ * parameterHeightWeight H j *
            R ^ (((if j = 0 then b - 1 else b + offset : ℕ) : ℝ) /
              ((s : ℝ) + 1))) :
    δ * |(smoothDirections_realCompTVS (smoothDirections_stateFlowGraph J) K
        (fun q hq => Set.mem_prod.mpr ⟨(Set.mem_prod.mp hq).1, mem_univ _⟩)).D N
          (x, θ) (input.pureSlots v)| ≤
      n01c_graphPartitionWordCount N * (C₀ * C₁ ^ N * L ^ N) *
        E ^ (A₀ + A₁ * (N : ℝ)) * H *
          R ^ (((n + input.angleArity + (offset + 1) * input.stateArity : ℕ) : ℝ) /
            ((s : ℝ) + 1)) := by
  classical
  let slots := fun c : OrderedFinpartition N => stateFlowPartitionSlot J input c (x, θ) v
  let term := fun (c : OrderedFinpartition N) (w : StateAngleWord c.length) =>
    (Ka w.angleArity (Θ (x, θ))).D w.stateArity x (w.stateDirections (slots c)) *
      w.angleFactor (slots c)
  let W : ℝ := E ^ (A₀ + A₁ * (N : ℝ)) * H *
    R ^ (((n + input.angleArity + (offset + 1) * input.stateArity : ℕ) : ℝ) /
      ((s : ℝ) + 1))
  let B : ℝ := C₀ * C₁ ^ N * L ^ N
  have hterm (c : OrderedFinpartition N) (w : StateAngleWord c.length) :
      δ * |term c w| ≤ B * W := by
    let κ : Fin c.length → ℕ := fun i => (input.restrict (c.emb i)).stateArity
    let β : Fin c.length → ℕ := fun i => (input.restrict (c.emb i)).angleArity
    have hpart (i : Fin c.length) : 0 < κ i + β i := by
      rw [show κ i + β i = c.partSize i from (input.restrict (c.emb i)).arity_sum]
      exact c.partSize_pos i
    have hκsum : (∑ i, κ i) = input.stateArity := input.sum_restrict_stateArity c
    have hβsum : (∑ i, β i) = input.angleArity := input.sum_restrict_angleArity c
    have hlow (i : Fin w.stateArity) : p₀ (w.stateDirections (slots c) i) ≤ 1 := by
      obtain ⟨j, hj, he⟩ := w.stateDirections_mem_range (slots c) i
      rw [he]
      exact stateFlowPartitionSlot_fst_seminorm_le J input c (x, θ) v p₀
        zero_le_one hv₀ j
    have hhigh (i : Fin w.stateArity) : p₁ (w.stateDirections (slots c) i) ≤ R := by
      obtain ⟨j, hj, he⟩ := w.stateDirections_mem_range (slots c) i
      rw [he]
      exact stateFlowPartitionSlot_fst_seminorm_le J input c (x, θ) v p₁
        (zero_le_one.trans hR) hv₁ j
    have ho := houter w.stateArity w.angleArity
      (by rw [w.arity_sum]; exact c.length_le) (Θ (x, θ))
      (w.stateDirections (slots c)) hlow hhigh
    have hf (i : Fin c.length) :
        |(slots c i).2| ≤ C₁ * E ^ A₁ * parameterHeightWeight H (κ i) *
          R ^ (((if κ i = 0 then β i - 1 else β i + offset : ℕ) : ℝ) /
            ((s : ℝ) + 1)) := by
      have hki : κ i ≤ input.stateArity := by
        calc
          _ ≤ ∑ j, κ j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          _ = _ := hκsum
      have hs : κ i + β i ≤ N := by
        rw [show κ i + β i = c.partSize i from (input.restrict (c.emb i)).arity_sum]
        exact c.partSize_le i
      rw [show (slots c i).2 = (Ja (β i) θ).D (κ i) x
          ((input.restrict (c.emb i)).stateDirections (input.pureSlots v ∘ c.emb i)) from
        stateFlowPartitionSlot_snd J Ja input c hx θ v i]
      apply hflow (κ i) (β i) (hpart i) hs hki
      · intro l
        obtain ⟨j, hj, he⟩ := (input.restrict (c.emb i)).stateDirections_mem_range
          (input.pureSlots v ∘ c.emb i) l
        rw [he]
        exact input.pureSlots_fst_seminorm_le p₀ zero_le_one v hv₀ (c.emb i j)
      · intro l
        obtain ⟨j, hj, he⟩ := (input.restrict (c.emb i)).stateDirections_mem_range
          (input.pureSlots v ∘ c.emb i) l
        rw [he]
        exact input.pureSlots_fst_seminorm_le p₁ (zero_le_one.trans hR) v hv₁ (c.emb i j)
    have hraw := n01c_stateAngleGraph_term_bound w κ β offset n s hpart
      (by simpa only [hκsum] using hk) (slots c)
      hC₀ hC₁ hE hA₁ hR hH hHL hL ho hf
    rw [hκsum, hβsum] at hraw
    have henv := n01c_graphWordEnvelope_mono c.length_le hC₀ hC₁ hL hE hA₁
      (A₀ := A₀)
    calc
      _ ≤ (C₀ * C₁ ^ c.length * L ^ c.length) *
          E ^ (A₀ + A₁ * (c.length : ℝ)) * H *
            R ^ (((n + input.angleArity + (offset + 1) * input.stateArity : ℕ) : ℝ) /
              ((s : ℝ) + 1)) := hraw
      _ ≤ (C₀ * C₁ ^ N * L ^ N) * E ^ (A₀ + A₁ * (N : ℝ)) * H *
            R ^ (((n + input.angleArity + (offset + 1) * input.stateArity : ℕ) : ℝ) /
              ((s : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right henv hH)
          (Real.rpow_nonneg (zero_le_one.trans hR) _)
      _ = B * W := by dsimp only [B, W]; ring
  rw [stateFlow_composition_D_pureSlots J K Ka input hx θ v]
  change δ * |∑ c : OrderedFinpartition N, ∑ w : StateAngleWord c.length, term c w| ≤ _
  calc
    _ ≤ δ * ∑ c : OrderedFinpartition N, |∑ w : StateAngleWord c.length, term c w| :=
      mul_le_mul_of_nonneg_left
        (by
          simpa only [Real.norm_eq_abs] using
            (norm_sum_le (Finset.univ : Finset (OrderedFinpartition N))
              (fun c => ∑ w : StateAngleWord c.length, term c w))) hδ
    _ ≤ δ * ∑ c : OrderedFinpartition N, ∑ w : StateAngleWord c.length, |term c w| :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => by
        simpa only [Real.norm_eq_abs] using
          norm_sum_le (Finset.univ : Finset (StateAngleWord c.length)) (term c))) hδ
    _ = ∑ c : OrderedFinpartition N, ∑ w : StateAngleWord c.length, δ * |term c w| := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ c : OrderedFinpartition N, ∑ _w : StateAngleWord c.length, B * W :=
      Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun w _ => hterm c w))
    _ = (∑ c : OrderedFinpartition N, (Fintype.card (StateAngleWord c.length) : ℝ)) *
          (B * W) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_mul]
    _ = _ := by dsimp only [n01c_graphPartitionWordCount, B, W]; ring

end ContinuousFlexibility.Analysis
