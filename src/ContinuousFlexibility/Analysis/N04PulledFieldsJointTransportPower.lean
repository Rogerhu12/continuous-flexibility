import ContinuousFlexibility.Analysis.N04PulledFieldsTransportPowerGrowth
import ContinuousFlexibility.Analysis.N04PulledFieldsTransportParameterBudget

/-!
# Actual transport jets with a fixed parameter charge

The exact radial transport identities are evaluated in the parameter
budget recurrence. A common low grading is retained. Only the high loss
and the charge per parameter slot depend on the finite parameter prefix.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : I → Set PolarPoint}

/-- Genuine radial transport, its angular boundary estimates, and the
original characteristic estimates imply the exact power-growth bound
for both corrected velocity products. -/
theorem n04PulledFields_jointTransport_parameterPowerGrowth
    (p : ℕ → Seminorm ℝ E) (W H : I → ℝ)
    (hW : ∀ i, 1 ≤ W i) (hH : ∀ i, 0 ≤ H i)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    {fL fC fA : I → E × PolarPoint → ℝ}
    {fZ : Fin 2 → I → E × PolarPoint → ℝ}
    (JL : ∀ i, SmoothDirections (U ×ˢ V i) (fL i))
    (JC : ∀ i, SmoothDirections (U ×ˢ V i) (fC i))
    (JA : ∀ i, SmoothDirections (U ×ˢ V i) (fA i))
    (JZ : ∀ c i, SmoothDirections (U ×ˢ V i) (fZ c i))
    (nmax B highLoss shift : ℕ)
    (hL : N04PulledFieldsMixedPowerGrowth p W (fun _ => 1) JL nmax B highLoss shift)
    (hC : ∀ n a b, ∃ K P : ℝ, 0 ≤ K ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U → ∀ w, ∀ y ∈ V i,
        |jointMixedDiagonal (JC i) n a b x w y| ≤ K * W i ^ P)
    (hA : N04PulledFieldsAngularPowerGrowth p W (fun _ => 1) JA nmax B highLoss shift)
    (hZ : ∀ c : Fin 2, N04PulledFieldsAngularPowerGrowth p W (fun i => H i ^ c.val) (JZ c) nmax B highLoss shift)
    (hAr : ∀ i x, x ∈ U → ∀ y ∈ V i,
      radialPartial (fun q => fA i (x, q)) y =
        angularPartial (fun q => fL i (x, q)) y * fA i (x, y) -
          fL i (x, y) * angularPartial (fun q => fA i (x, q)) y)
    (hZr : ∀ c i x, x ∈ U → ∀ y ∈ V i,
      radialPartial (fun q => fZ c i (x, q)) y =
        -((fL i (x, y) + fC i (x, y) * fA i (x, y) * fZ 0 i (x, y)) *
          angularPartial (fun q => fZ c i (x, q)) y)) :
    ∀ c : Fin 2, N04PulledFieldsMixedPowerGrowth p W (fun i => H i ^ c.val)
      (fun i => ((JC i).mul (JA i)).mul (JZ c i)) nmax B highLoss shift := by
  intro c R hR N n hn a b hab
  let X := I × ((E × E) × PolarPoint)
  let Ω : Set X := {q | q.2.1.1 ∈ U ∧ p B q.2.1.1 ≤ R ∧
    p B q.2.1.2 ≤ 1 ∧ q.2.2 ∈ V q.1}
  let WW : X → ℝ := fun q => W q.1
  let HH : X → ℝ := fun q => H q.1
  let QQ : X → ℝ := fun q => 1 + p (N + highLoss) q.2.1.1 + p (N + highLoss) q.2.1.2
  let L : ℕ → ℕ → ℕ → X → ℝ := fun k i j q =>
    jointMixedDiagonal (JL q.1) k i j q.2.1.1 q.2.1.2 q.2.2
  let C : ℕ → ℕ → ℕ → X → ℝ := fun k i j q =>
    jointMixedDiagonal (JC q.1) k i j q.2.1.1 q.2.1.2 q.2.2
  let A : ℕ → ℕ → ℕ → X → ℝ := fun k i j q =>
    jointMixedDiagonal (JA q.1) k i j q.2.1.1 q.2.1.2 q.2.2
  let Z : Fin 2 → ℕ → ℕ → ℕ → X → ℝ := fun d k i j q =>
    jointMixedDiagonal (JZ d q.1) k i j q.2.1.1 q.2.1.2 q.2.2
  let JT := fun i => smoothDirectionsAdd (JL i) (((JC i).mul (JA i)).mul (JZ 0 i))
  let Tj : ℕ → ℕ → ℕ → X → ℝ := fun k i j q =>
    jointMixedDiagonal (JT q.1) k i j q.2.1.1 q.2.1.2 q.2.2
  have hWW (q : X) (_ : q ∈ Ω) : 1 ≤ WW q := hW q.1
  have hHH (q : X) (_ : q ∈ Ω) : 0 ≤ HH q := hH q.1
  have hQQ (q : X) (_ : q ∈ Ω) : 1 ≤ QQ q := by
    dsimp only [QQ]
    linarith only [apply_nonneg (p (N + highLoss)) q.2.1.1,
      apply_nonneg (p (N + highLoss)) q.2.1.2]
  have hdenom : 0 < (N : ℝ) + 1 := by positivity
  have hLb (k i j : ℕ) (hk : k ≤ nmax) (hij : i + j ≤ N) :
      HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (i + j + shift * k) 0 (L k i j) := by
    obtain ⟨K, P, hK, hP, hbnd⟩ := hL R hR N k hk i j hij
    refine ⟨K, P, hK, hP, fun q hq => ?_⟩
    have hb := hbnd q.1 q.2.1.1 hq.1 hq.2.1 q.2.1.2 hq.2.2.1 q.2.2 hq.2.2.2
    simpa only [L, WW, HH, QQ, pow_zero, mul_one] using hb
  have hCb (k i j : ℕ) (_hk : k ≤ nmax) (_hij : i + j ≤ N) :
      HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (shift * k) 0 (C k i j) := by
    have hc0 : HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) 0 0 (C k i j) := by
      obtain ⟨K, P, hK, hP, hbnd⟩ := hC k i j
      refine ⟨K, P, hK, hP, fun q hq => ?_⟩
      simpa only [C, WW, HH, QQ, pow_zero, Nat.cast_zero, zero_div, Real.rpow_zero, mul_one]
        using hbnd q.1 q.2.1.1 hq.1 q.2.1.2 q.2.2 hq.2.2.2
    exact hc0.monoDegree hWW hHH hQQ hdenom (Nat.zero_le _)
  have hAb (k j : ℕ) (hk : k ≤ nmax) (hj : j ≤ N) :
      HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (j + shift * k) 0 (A k 0 j) := by
    obtain ⟨K, P, hK, hP, hbnd⟩ := hA R hR N k hk j hj
    refine ⟨K, P, hK, hP, fun q hq => ?_⟩
    simpa only [A, WW, HH, QQ, Real.rpow_zero, pow_zero, mul_one]
      using hbnd q.1 q.2.1.1 hq.1 hq.2.1 q.2.1.2 hq.2.2.1 q.2.2 hq.2.2.2
  have hZb (d : Fin 2) (k j : ℕ) (hk : k ≤ nmax) (hj : j ≤ N) :
      HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (j + shift * k) d.val (Z d k 0 j) := by
    obtain ⟨K, P, hK, hP, hbnd⟩ := hZ d R hR N k hk j hj
    refine ⟨K, P, hK, hP, fun q hq => ?_⟩
    simpa only [Z, WW, HH, QQ, Real.rpow_zero, mul_one]
      using hbnd q.1 q.2.1.1 hq.1 hq.2.1 q.2.1.2 hq.2.2.1 q.2.2 hq.2.2.2
  have hTj (k i j : ℕ) (_hk : k ≤ nmax) (_hij : i + j ≤ N) (q : X) (hq : q ∈ Ω) :
      Tj k i j q = L k i j q + diagonalJetProduct (diagonalJetProduct C A) (Z 0) k i j q :=
    jointMixedDiagonal_add_triple_mul (JL q.1) (JC q.1) (JA q.1) (JZ 0 q.1) (JT q.1)
      hU (hV q.1) (hc q.1) (fun _ _ _ _ => rfl)
      k i j q.2.1.1 q.2.1.2 hq.1 q.2.2 hq.2.2.2
  have hAj (k i j : ℕ) (_hk : k ≤ nmax) (_hij : i + 1 + j ≤ N) (q : X) (hq : q ∈ Ω) :
      A k (i + 1) j q =
        diagonalJetProduct (fun t u v => L t u (v + 1)) A k i j q -
          diagonalJetProduct L (fun t u v => A t u (v + 1)) k i j q :=
    jointMixedDiagonal_variational_transport (JA q.1) (JL q.1) hU (hV q.1) (hc q.1)
      (hAr q.1) k i j q.2.1.1 q.2.1.2 hq.1 hq.2.2.2
  have hZj (d : Fin 2) (k i j : ℕ) (_hk : k ≤ nmax) (_hij : i + 1 + j ≤ N)
      (q : X) (hq : q ∈ Ω) :
      Z d k (i + 1) j q = -diagonalJetProduct Tj (fun t u v => Z d t u (v + 1)) k i j q :=
    jointMixedDiagonal_transport (JZ d q.1) (JT q.1) hU (hV q.1) (hc q.1)
      (hZr d q.1) k i j q.2.1.1 q.2.1.2 hq.1 hq.2.2.2
  have hsystem := n04PulledFields_transportSystem_parameterDegree nmax N shift hWW hHH hQQ hdenom
    L C A Tj Z hLb hCb hAb hZb hTj hAj hZj
  have hCA (k i j : ℕ) (hk : k ≤ nmax) (hij : i + j ≤ N) :
      HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (i + j + shift * k) 0
        (diagonalJetProduct C A k i j) := by
    have hcf (t : ℕ) (ht : t ≤ k) (u : ℕ) (hu : u ≤ i) (v : ℕ) (hv : v ≤ j) :
        HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (u + v + 0 + shift * t) 0 (C t u v) :=
      (hCb t u v (ht.trans hk) (by omega)).monoDegree hWW hHH hQQ hdenom (Nat.le_add_left _ _)
    have haf (t : ℕ) (ht : t ≤ k) (u : ℕ) (hu : u ≤ i) (v : ℕ) (hv : v ≤ j) :
        HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (u + v + 0 + shift * t) 0 (A t u v) := by
      simpa only [Nat.add_zero] using (hsystem u t v (ht.trans hk) (by omega)).1
    simpa only [Nat.add_zero] using n04PulledFields_diagonalJetProduct_parameterDegree
      hWW hHH hQQ C A k i j shift 0 0 0 0 hcf haf
  have hcf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a) (j : ℕ) (hj : j ≤ b) :
      HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (i + j + 0 + shift * k) 0
        (diagonalJetProduct C A k i j) := by
    simpa only [Nat.add_zero] using hCA k i j (hk.trans hn) (by omega)
  have hzf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a) (j : ℕ) (hj : j ≤ b) :
      HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (i + j + 0 + shift * k) c.val (Z c k i j) := by
    simpa only [Nat.add_zero] using (hsystem i k j (hk.trans hn) (by omega)).2 c
  have hprod : HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (a + b + shift * n) c.val
      (diagonalJetProduct (diagonalJetProduct C A) (Z c) n a b) := by
    simpa only [Nat.add_zero, Nat.zero_add] using n04PulledFields_diagonalJetProduct_parameterDegree
      hWW hHH hQQ (diagonalJetProduct C A) (Z c) n a b shift 0 0 0 c.val hcf hzf
  obtain ⟨K, P, hK, hP, hbnd⟩ := hprod
  refine ⟨K, P, hK, hP, fun i x hx hxB w hw y hy => ?_⟩
  let q : X := (i, ((x, w), y))
  have hq : q ∈ Ω := ⟨hx, hxB, hw, hy⟩
  have he := jointMixedDiagonal_triple_mul (JC i) (JA i) (JZ c i)
    (((JC i).mul (JA i)).mul (JZ c i)) hU (hV i) (hc i)
    (fun _ _ _ _ => rfl) n a b x w hx y hy
  exact (congrArg abs he).trans_le (hbnd q hq)

end ContinuousFlexibility.Analysis
