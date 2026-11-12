import ContinuousFlexibility.Analysis.N01ReturnTransportRecurrences
import ContinuousFlexibility.Analysis.MixedDiagonalPowerGrowth
import ContinuousFlexibility.Analysis.CircleStripAngularInterpolation

/-!
# Fixed spatial degree for genuine transport jets

The actual mixed Leibniz identities place a genuine joint transport
system in the finite numerical recurrence. The common high scale is
fixed before radial induction. The independently transported field
retains exactly one copy of its label weight, including in the final
velocity product.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : I → Set PolarPoint}

/-- The radial-zero boundary estimate on the common interpolation
scale. The label factor is kept explicit. -/
def AngularDiagonalPowerGrowth
    (p : ℕ → Seminorm ℝ E) (F : I → ℝ)
    {f : I → E × PolarPoint → ℝ}
    (J : ∀ i, SmoothDirections (U ×ˢ V i) (f i))
    (nmax B : ℕ) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ U → p B x ≤ R → ∀ w, p B w ≤ 1 →
      ∀ y ∈ V i,
      |jointMixedDiagonal (J i) n 0 b x w y| ≤
        C * F i * (1 + p (N + B + 1) x + p (N + B + 1) w) ^
          ((b : ℝ) / ((N : ℝ) + 1))

theorem AngularDiagonalPowerGrowth.mono_base
    {p : ℕ → Seminorm ℝ E} {F : I → ℝ} (hp : Monotone p) (hF : ∀ i, 0 ≤ F i)
    {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)} {nmax B B' : ℕ}
    (hg : AngularDiagonalPowerGrowth p F J nmax B) (hB : B ≤ B') :
    AngularDiagonalPowerGrowth p F J nmax B' := by
  intro R hR N n hn b hb
  obtain ⟨C, hC, hc⟩ := hg R hR N n hn b hb
  refine ⟨C, hC, fun i x hx hxB w hw y hy => ?_⟩
  exact (hc i x hx ((hp hB x).trans hxB) w ((hp hB w).trans hw) y hy).trans
    (mul_le_mul_of_nonneg_left (common_spatial_scale_mono hp hB x w)
      (mul_nonneg hC (hF i)))

/-- Genuine radial transport, its angular boundary estimates, and the
original characteristic estimates imply the exact power-growth bound
for both corrected velocity products. -/
theorem jointTransport_velocity_mixedPowerGrowth
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
    (nmax B : ℕ)
    (hL : MixedDiagonalPowerGrowth p W (fun _ => 1) JL nmax B)
    (hC : ∀ n a b, ∃ K P : ℝ, 0 ≤ K ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U → ∀ w, ∀ y ∈ V i,
        |jointMixedDiagonal (JC i) n a b x w y| ≤ K * W i ^ P)
    (hA : AngularDiagonalPowerGrowth p (fun _ => 1) JA nmax B)
    (hZ : ∀ c : Fin 2, AngularDiagonalPowerGrowth p (fun i => H i ^ c.val) (JZ c) nmax B)
    (hAr : ∀ i x, x ∈ U → ∀ y ∈ V i,
      radialPartial (fun q => fA i (x, q)) y =
        angularPartial (fun q => fL i (x, q)) y * fA i (x, y) -
          fL i (x, y) * angularPartial (fun q => fA i (x, q)) y)
    (hZr : ∀ c i x, x ∈ U → ∀ y ∈ V i,
      radialPartial (fun q => fZ c i (x, q)) y =
        -((fL i (x, y) + fC i (x, y) * fA i (x, y) * fZ 0 i (x, y)) *
          angularPartial (fun q => fZ c i (x, q)) y)) :
    ∀ c : Fin 2, MixedDiagonalPowerGrowth p W (fun i => H i ^ c.val)
      (fun i => ((JC i).mul (JA i)).mul (JZ c i)) nmax B := by
  intro c R hR N n hn a b hab
  let X := I × ((E × E) × PolarPoint)
  let Ω : Set X := {q | q.2.1.1 ∈ U ∧ p B q.2.1.1 ≤ R ∧
    p B q.2.1.2 ≤ 1 ∧ q.2.2 ∈ V q.1}
  let WW : X → ℝ := fun q => W q.1
  let HH : X → ℝ := fun q => H q.1
  let QQ : X → ℝ := fun q => 1 + p (N + B + 1) q.2.1.1 + p (N + B + 1) q.2.1.2
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
    linarith only [apply_nonneg (p (N + B + 1)) q.2.1.1,
      apply_nonneg (p (N + B + 1)) q.2.1.2]
  have hdenom : 0 < (N : ℝ) + 1 := by positivity
  have hLb (k i j : ℕ) (hk : k ≤ nmax) (hij : i + j ≤ N) :
      HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (i + j) 0 (L k i j) := by
    obtain ⟨K, P, hK, hP, hbnd⟩ := hL R hR N k hk i j hij
    refine ⟨K, P, hK, hP, fun q hq => ?_⟩
    have hb := hbnd q.1 q.2.1.1 hq.1 hq.2.1 q.2.1.2 hq.2.2.1 q.2.2 hq.2.2.2
    simpa only [L, WW, HH, QQ, pow_zero, mul_one] using hb
  have hCb (k i j : ℕ) (_hk : k ≤ nmax) (_hij : i + j ≤ N) :
      HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) 0 0 (C k i j) := by
    obtain ⟨K, P, hK, hP, hbnd⟩ := hC k i j
    refine ⟨K, P, hK, hP, fun q hq => ?_⟩
    simpa only [C, WW, HH, QQ, pow_zero, Nat.cast_zero, zero_div, Real.rpow_zero, mul_one]
      using hbnd q.1 q.2.1.1 hq.1 q.2.1.2 q.2.2 hq.2.2.2
  have hAb (k j : ℕ) (hk : k ≤ nmax) (hj : j ≤ N) :
      HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) j 0 (A k 0 j) := by
    obtain ⟨K, hK, hbnd⟩ := hA R hR N k hk j hj
    refine ⟨K, 0, hK, le_rfl, fun q hq => ?_⟩
    simpa only [A, WW, HH, QQ, Real.rpow_zero, pow_zero, mul_one]
      using hbnd q.1 q.2.1.1 hq.1 hq.2.1 q.2.1.2 hq.2.2.1 q.2.2 hq.2.2.2
  have hZb (d : Fin 2) (k j : ℕ) (hk : k ≤ nmax) (hj : j ≤ N) :
      HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) j d.val (Z d k 0 j) := by
    obtain ⟨K, hK, hbnd⟩ := hZ d R hR N k hk j hj
    refine ⟨K, 0, hK, le_rfl, fun q hq => ?_⟩
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
  have hsystem := weightedJetBounds_transportSystem nmax N hWW hHH hQQ hdenom
    L C A Tj Z hLb hCb hAb hZb hTj hAj hZj
  have hCA (k i j : ℕ) (hk : k ≤ nmax) (hij : i + j ≤ N) :
      HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (i + j) 0
        (diagonalJetProduct C A k i j) := by
    have hcf (t : ℕ) (ht : t ≤ k) (u : ℕ) (hu : u ≤ i) (v : ℕ) (hv : v ≤ j) :
        HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (u + v + 0) 0 (C t u v) :=
      (hCb t u v (ht.trans hk) (by omega)).monoDegree hWW hHH hQQ hdenom (Nat.zero_le _)
    have haf (t : ℕ) (ht : t ≤ k) (u : ℕ) (hu : u ≤ i) (v : ℕ) (hv : v ≤ j) :
        HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (u + v + 0) 0 (A t u v) := by
      simpa only [Nat.add_zero] using (hsystem u t v (ht.trans hk) (by omega)).1
    simpa only [Nat.add_zero] using hasWeightedJetBound_diagonalJetProduct
      hWW hHH hQQ C A k i j 0 0 0 0 hcf haf
  have hcf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a) (j : ℕ) (hj : j ≤ b) :
      HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (i + j + 0) 0
        (diagonalJetProduct C A k i j) := by
    simpa only [Nat.add_zero] using hCA k i j (hk.trans hn) (by omega)
  have hzf (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i ≤ a) (j : ℕ) (hj : j ≤ b) :
      HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (i + j + 0) c.val (Z c k i j) := by
    simpa only [Nat.add_zero] using (hsystem i k j (hk.trans hn) (by omega)).2 c
  have hprod : HasWeightedJetBound WW HH QQ Ω ((N : ℝ) + 1) (a + b) c.val
      (diagonalJetProduct (diagonalJetProduct C A) (Z c) n a b) := by
    simpa only [Nat.add_zero, Nat.zero_add] using hasWeightedJetBound_diagonalJetProduct
      hWW hHH hQQ (diagonalJetProduct C A) (Z c) n a b 0 0 0 c.val hcf hzf
  obtain ⟨K, P, hK, hP, hbnd⟩ := hprod
  refine ⟨K, P, hK, hP, fun i x hx hxB w hw y hy => ?_⟩
  let q : X := (i, ((x, w), y))
  have hq : q ∈ Ω := ⟨hx, hxB, hw, hy⟩
  have he := jointMixedDiagonal_triple_mul (JC i) (JA i) (JZ c i)
    (((JC i).mul (JA i)).mul (JZ c i)) hU (hV i) (hc i)
    (fun _ _ _ _ => rfl) n a b x w hx y hy
  exact (congrArg abs he).trans_le (hbnd q hq)

end ContinuousFlexibility.Analysis
