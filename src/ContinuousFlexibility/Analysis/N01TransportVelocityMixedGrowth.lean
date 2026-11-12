import ContinuousFlexibility.Analysis.JointTransportPowerBounds
import ContinuousFlexibility.Analysis.N01TransportCharacteristicInterpolation
import ContinuousFlexibility.Analysis.JointMixedRadialScalar

/-!
# The same actual cutoff velocity has fixed-loss mixed parameter bounds

The angular boundary estimates, original characteristic estimates and
cutoff bounds all come from the actual N01 construction on its buffered
strips. One common low order is selected before the spatial budget.
The true transport equations then propagate the estimates radially.
Both the independent residual and the supplied N02 residual use the
same cutoff and the same flow inverses.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

private def radialCutoffScalarTower
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {V : Set PolarPoint} (hU : IsOpen U) (hV : IsOpen V)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    SmoothDirections (U ×ˢ V) (fun x : E × PolarPoint => deriv χ x.2.1) := by
  let L : E × PolarPoint →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  have hd : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  exact (smoothDirectionsOfContDiffOn isOpen_univ hd.contDiffOn).compLinear L
    (hU.prod hV) (fun _ _ => mem_univ _)

private def radialCutoffScalarTowers
    {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {V : I → Set PolarPoint}
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (χ : I → ℝ → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) :
    ∀ i, SmoothDirections (U ×ˢ V i)
      (fun x : E × PolarPoint => deriv (χ i) x.2.1) :=
  fun i => radialCutoffScalarTower
    (E := E) (U := U) (V := V i) (χ := χ i) hU (hV i) (hχ i)

private def transportVelocity_twoTowers
    {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {U : Set E} {V : I → Set PolarPoint}
    {f₀ f₁ : I → E × PolarPoint → ℝ}
    (J₀ : ∀ i, SmoothDirections (U ×ˢ V i) (f₀ i))
    (J₁ : ∀ i, SmoothDirections (U ×ˢ V i) (f₁ i)) :
    ∀ (c : Fin 2) i, SmoothDirections (U ×ˢ V i)
      ((Fin.cases f₀ (Fin.cases f₁ Fin.elim0) :
        Fin 2 → I → E × PolarPoint → ℝ) c i) :=
  Fin.cases J₀ (Fin.cases J₁ (fun i => Fin.elim0 i))

/-- The actual towers are passed between stages without choosing new witnesses. -/
private structure TransportVelocityTowerFamilies
    {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (U : Set E) (V : I → Set PolarPoint)
    (fL fA : I → E × PolarPoint → ℝ)
    (fZ : Fin 2 → I → E × PolarPoint → ℝ) where
  JL : ∀ i, SmoothDirections (U ×ˢ V i) (fL i)
  JA : ∀ i, SmoothDirections (U ×ˢ V i) (fA i)
  JZ : ∀ c i, SmoothDirections (U ×ˢ V i) (fZ c i)

/-- Keep the four original choices and their exact common budget together. -/
private structure TransportVelocityGrowthData (growth : ℕ → Prop) where
  BL : ℕ
  BA : ℕ
  B₀ : ℕ
  B₁ : ℕ
  common : growth (BL + BA + B₀ + B₁)

private theorem transportVelocity_commonGrowth
    {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} (l h : I → ℝ)
    (p : ℕ → Seminorm ℝ E) (W H : I → ℝ)
    (hp : Monotone p) (hW : ∀ i, 0 ≤ W i) (hH : ∀ i, 0 ≤ H i)
    {fL fA : I → E × PolarPoint → ℝ} {fZ : Fin 2 → I → E × PolarPoint → ℝ}
    (JL : ∀ i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fL i))
    (JA : ∀ i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fA i))
    (JZ : ∀ c i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fZ c i))
    (nmax BL BA B₀ B₁ B : ℕ)
    (hbL : BL ≤ B) (hbA : BA ≤ B) (hb0 : B₀ ≤ B) (hb1 : B₁ ≤ B)
    (hBL : ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ a b : ℕ, a + b ≤ N →
      ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧
        ∀ i (x : E), x ∈ U → ∀ w : E, p BL x ≤ A → p BL w ≤ 1 →
          ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
            |jointMixedDiagonal (JL i) n a b x w y| ≤ K * W i ^ Q *
              (1 + p (N + BL + 1) x + p (N + BL + 1) w) ^
                (((a + b : ℕ) : ℝ) / ((N : ℝ) + 1)))
    (hBA : ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i (x : E), x ∈ U → ∀ w : E,
        p BA x ≤ A → p BA w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
          |jointMixedDiagonal (JA i) n 0 b x w y| ≤ K *
            (1 + p (N + BA + 1) x + p (N + BA + 1) w) ^
              ((b : ℝ) / ((N : ℝ) + 1)))
    (hB₀ : ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i (x : E), x ∈ U → ∀ w : E,
        p B₀ x ≤ A → p B₀ w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
          |jointMixedDiagonal (JZ 0 i) n 0 b x w y| ≤ K *
            (1 + p (N + B₀ + 1) x + p (N + B₀ + 1) w) ^
              ((b : ℝ) / ((N : ℝ) + 1)))
    (hB₁ : ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i (x : E), x ∈ U → ∀ w : E,
        p B₁ x ≤ A → p B₁ w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
          |jointMixedDiagonal (JZ 1 i) n 0 b x w y| ≤ K * H i *
            (1 + p (N + B₁ + 1) x + p (N + B₁ + 1) w) ^
              ((b : ℝ) / ((N : ℝ) + 1))) :
    MixedDiagonalPowerGrowth p W (fun _ => 1) JL nmax B ∧
      AngularDiagonalPowerGrowth p (fun _ => 1) JA nmax B ∧
      ∀ c : Fin 2, AngularDiagonalPowerGrowth p (fun i => H i ^ c.val) (JZ c) nmax B := by
  let V : I → Set PolarPoint := fun i => Ioo (l i) (h i) ×ˢ univ
  have hgL₀ : MixedDiagonalPowerGrowth p W (fun _ => 1) JL nmax BL := by
    intro A hA N n hn a b hab
    obtain ⟨K, Q, hK, hQ, hbnd⟩ := hBL A hA N n hn a b hab
    refine ⟨K, Q, hK, hQ, fun i x hx hxB w hw y hy => ?_⟩
    simpa only [mul_one] using hbnd i x hx w hxB hw y hy.1
  have hgL : MixedDiagonalPowerGrowth p W (fun _ => 1) JL nmax B :=
    MixedDiagonalPowerGrowth.mono_base
      (I := I) (E := E) (U := U) (V := V) (p := p) (W := W) (F := fun _ => 1)
      (f := fL) (J := JL) (nmax := nmax) (B := BL) (B' := B)
      hp hW (fun _ => zero_le_one) hgL₀ hbL
  have hgA₀ : AngularDiagonalPowerGrowth p (fun _ => 1) JA nmax BA := by
    intro A hA N n hn b hb
    obtain ⟨K, hK, hbnd⟩ := hBA A hA N n hn b hb
    refine ⟨K, hK, fun i x hx hxB w hw y hy => ?_⟩
    simpa only [mul_one] using hbnd i x hx w hxB hw y hy.1
  have hgA : AngularDiagonalPowerGrowth p (fun _ => 1) JA nmax B :=
    AngularDiagonalPowerGrowth.mono_base
      (I := I) (E := E) (U := U) (V := V) (p := p) (F := fun _ => 1)
      (f := fA) (J := JA) (nmax := nmax) (B := BA) (B' := B)
      hp (fun _ => zero_le_one) hgA₀ hbA
  have hg0base : AngularDiagonalPowerGrowth p (fun _ => 1) (JZ 0) nmax B₀ := by
    intro A hA N n hn b hb
    obtain ⟨K, hK, hbnd⟩ := hB₀ A hA N n hn b hb
    refine ⟨K, hK, fun i x hx hxB w hw y hy => ?_⟩
    simpa only [mul_one] using hbnd i x hx w hxB hw y hy.1
  have hg0 : AngularDiagonalPowerGrowth p (fun _ => 1) (JZ 0) nmax B :=
    AngularDiagonalPowerGrowth.mono_base
      (I := I) (E := E) (U := U) (V := V) (p := p) (F := fun _ => 1)
      (f := fZ 0) (J := JZ 0) (nmax := nmax) (B := B₀) (B' := B)
      hp (fun _ => zero_le_one) hg0base hb0
  have hg1base : AngularDiagonalPowerGrowth p H (JZ 1) nmax B₁ := by
    intro A hA N n hn b hb
    obtain ⟨K, hK, hbnd⟩ := hB₁ A hA N n hn b hb
    exact ⟨K, hK, fun i x hx hxB w hw y hy => hbnd i x hx w hxB hw y hy.1⟩
  have hg1 : AngularDiagonalPowerGrowth p H (JZ 1) nmax B :=
    AngularDiagonalPowerGrowth.mono_base
      (I := I) (E := E) (U := U) (V := V) (p := p) (F := H)
      (f := fZ 1) (J := JZ 1) (nmax := nmax) (B := B₁) (B' := B)
      hp hH hg1base hb1
  refine ⟨hgL, hgA, ?_⟩
  intro c
  fin_cases c
  · simpa only [Fin.mk_zero, Fin.val_zero, pow_zero] using hg0
  · simpa only [Fin.mk_one, Fin.val_one, pow_one] using hg1

private theorem transportVelocity_flatOfGrowth
    {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {V : I → Set PolarPoint}
    (p : ℕ → Seminorm ℝ E) (W H : I → ℝ)
    (hW : ∀ i, 1 ≤ W i) (hH : ∀ i, 0 ≤ H i)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i)) (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    {fL fC fA fV fE : I → E × PolarPoint → ℝ}
    {fZ : Fin 2 → I → E × PolarPoint → ℝ}
    (JL : ∀ i, SmoothDirections (U ×ˢ V i) (fL i))
    (JC : ∀ i, SmoothDirections (U ×ˢ V i) (fC i))
    (JA : ∀ i, SmoothDirections (U ×ˢ V i) (fA i))
    (JZ : ∀ c i, SmoothDirections (U ×ˢ V i) (fZ c i))
    (JV : ∀ i, SmoothDirections (U ×ˢ V i) (fV i))
    (JE : ∀ i, SmoothDirections (U ×ˢ V i) (fE i))
    (nmax B : ℕ)
    (hL : MixedDiagonalPowerGrowth p W (fun _ => 1) JL nmax B)
    (hC : ∀ n a b, ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U → ∀ w, ∀ y ∈ V i,
        |jointMixedDiagonal (JC i) n a b x w y| ≤ K * W i ^ Q)
    (hA : AngularDiagonalPowerGrowth p (fun _ => 1) JA nmax B)
    (hZ : ∀ c : Fin 2,
      AngularDiagonalPowerGrowth p (fun i => H i ^ c.val) (JZ c) nmax B)
    (hAr : ∀ i x, x ∈ U → ∀ y ∈ V i,
      radialPartial (fun q => fA i (x, q)) y =
        angularPartial (fun q => fL i (x, q)) y * fA i (x, y) -
          fL i (x, y) * angularPartial (fun q => fA i (x, q)) y)
    (hZr : ∀ c i x, x ∈ U → ∀ y ∈ V i,
      radialPartial (fun q => fZ c i (x, q)) y =
        -((fL i (x, y) + fC i (x, y) * fA i (x, y) * fZ 0 i (x, y)) *
          angularPartial (fun q => fZ c i (x, q)) y))
    (hVeq : ∀ i, EqOn (fun x => fC i x * fA i x * fZ 1 i x) (fV i) (U ×ˢ V i))
    (hEeq : ∀ i, EqOn (fun x => fC i x * fA i x * fZ 0 i x) (fE i) (U ×ˢ V i)) :
    FlatMixedDiagonalGrowth p W H JV nmax B (B + 1) ∧
      FlatMixedDiagonalGrowth p W (fun _ => 1) JE nmax B (B + 1) := by
  let fvel : Fin 2 → I → E × PolarPoint → ℝ :=
    fun c i x => fC i x * fA i x * fZ c i x
  let Jvel : ∀ c i, SmoothDirections (U ×ˢ V i) (fvel c i) := fun c i =>
    SmoothDirections.mul
      (E := E × PolarPoint) (U := U ×ˢ V i)
      (f := fun x => fC i x * fA i x) (g := fZ c i)
      (SmoothDirections.mul (E := E × PolarPoint) (U := U ×ˢ V i)
        (f := fC i) (g := fA i) (JC i) (JA i)) (JZ c i)
  have hvel : ∀ c : Fin 2,
      MixedDiagonalPowerGrowth p W (fun i => H i ^ c.val) (Jvel c) nmax B :=
    jointTransport_velocity_mixedPowerGrowth
      (I := I) (E := E) (U := U) (V := V)
      (fL := fL) (fC := fC) (fA := fA) (fZ := fZ)
      p W H hW hH hU hV hc JL JC JA JZ nmax B hL hC hA hZ hAr hZr
  have hflat1 : FlatMixedDiagonalGrowth p W (fun i => H i ^ (1 : Fin 2).val)
      (Jvel 1) nmax B (B + 1) :=
    MixedDiagonalPowerGrowth.flat
      (I := I) (E := E) (U := U) (V := V)
      (p := p) (W := W) (F := fun i => H i ^ (1 : Fin 2).val)
      (f := fvel 1) (J := Jvel 1) (nmax := nmax) (B := B)
      hW (fun i => pow_nonneg (hH i) (1 : Fin 2).val) (hvel 1)
  have hflat0 : FlatMixedDiagonalGrowth p W (fun i => H i ^ (0 : Fin 2).val)
      (Jvel 0) nmax B (B + 1) :=
    MixedDiagonalPowerGrowth.flat
      (I := I) (E := E) (U := U) (V := V)
      (p := p) (W := W) (F := fun i => H i ^ (0 : Fin 2).val)
      (f := fvel 0) (J := Jvel 0) (nmax := nmax) (B := B)
      hW (fun i => pow_nonneg (hH i) (0 : Fin 2).val) (hvel 0)
  constructor
  · have hsame : FlatMixedDiagonalGrowth p W (fun i => H i ^ (1 : Fin 2).val)
        JV nmax B (B + 1) :=
      FlatMixedDiagonalGrowth.congr
        (I := I) (E := E) (U := U) (V := V)
        (p := p) (W := W) (F := fun i => H i ^ (1 : Fin 2).val)
        (f := fvel 1) (g := fV) (J := Jvel 1) (n := nmax) (low := B) (loss := B + 1)
        hflat1 JV hV hVeq
    simpa only [Fin.val_one, pow_one] using hsame
  · have hsame : FlatMixedDiagonalGrowth p W (fun i => H i ^ (0 : Fin 2).val)
        JE nmax B (B + 1) :=
      FlatMixedDiagonalGrowth.congr
        (I := I) (E := E) (U := U) (V := V)
        (p := p) (W := W) (F := fun i => H i ^ (0 : Fin 2).val)
        (f := fvel 0) (g := fE) (J := Jvel 0) (n := nmax) (low := B) (loss := B + 1)
        hflat0 JE hV hEeq
    simpa only [Fin.val_zero, pow_zero] using hsame

/-- Build the scalar cutoff tower and finish the transport estimate over an
abstract parameter space, before specializing to the physical spaces. -/
private theorem transportVelocity_flatWithRadialCutoff
    {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {V : I → Set PolarPoint}
    (p : ℕ → Seminorm ℝ E) (W H : I → ℝ)
    (hW : ∀ i, 1 ≤ W i) (hH : ∀ i, 0 ≤ H i)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i)) (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    (χ : I → ℝ → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hcutoff : ∀ k : ℕ, ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧ ∀ i r,
      |iteratedDeriv k (χ i) r| ≤ K * W i ^ Q)
    {fL fA fV fE : I → E × PolarPoint → ℝ}
    {fZ : Fin 2 → I → E × PolarPoint → ℝ}
    (JL : ∀ i, SmoothDirections (U ×ˢ V i) (fL i))
    (JA : ∀ i, SmoothDirections (U ×ˢ V i) (fA i))
    (JZ : ∀ c i, SmoothDirections (U ×ˢ V i) (fZ c i))
    (JV : ∀ i, SmoothDirections (U ×ˢ V i) (fV i))
    (JE : ∀ i, SmoothDirections (U ×ˢ V i) (fE i))
    (nmax B : ℕ)
    (hL : MixedDiagonalPowerGrowth p W (fun _ => 1) JL nmax B)
    (hA : AngularDiagonalPowerGrowth p (fun _ => 1) JA nmax B)
    (hZ : ∀ c : Fin 2,
      AngularDiagonalPowerGrowth p (fun i => H i ^ c.val) (JZ c) nmax B)
    (hAr : ∀ i x, x ∈ U → ∀ y ∈ V i,
      radialPartial (fun q => fA i (x, q)) y =
        angularPartial (fun q => fL i (x, q)) y * fA i (x, y) -
          fL i (x, y) * angularPartial (fun q => fA i (x, q)) y)
    (hZr : ∀ c i x, x ∈ U → ∀ y ∈ V i,
      radialPartial (fun q => fZ c i (x, q)) y =
        -((fL i (x, y) + deriv (χ i) y.1 * fA i (x, y) * fZ 0 i (x, y)) *
          angularPartial (fun q => fZ c i (x, q)) y))
    (hVeq : ∀ i, EqOn
      (fun x => deriv (χ i) x.2.1 * fA i x * fZ 1 i x) (fV i) (U ×ˢ V i))
    (hEeq : ∀ i, EqOn
      (fun x => deriv (χ i) x.2.1 * fA i x * fZ 0 i x) (fE i) (U ×ˢ V i)) :
    FlatMixedDiagonalGrowth p W H JV nmax B (B + 1) ∧
      FlatMixedDiagonalGrowth p W (fun _ => 1) JE nmax B (B + 1) := by
  let fC : I → E × PolarPoint → ℝ := fun i x => deriv (χ i) x.2.1
  let JC : ∀ i, SmoothDirections (U ×ˢ V i) (fC i) :=
    radialCutoffScalarTowers (I := I) (E := E) (U := U) (V := V) hU hV χ hχ
  have hW0 (i : I) : 0 ≤ W i := zero_le_one.trans (hW i)
  have hgC (n a b : ℕ) : ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U → ∀ w, ∀ y ∈ V i,
        |jointMixedDiagonal (JC i) n a b x w y| ≤ K * W i ^ Q := by
    obtain ⟨K, Q, hK, hQ, hbnd⟩ := hcutoff (a + 1)
    exact ⟨K, Q, hK, hQ, fun i x hx w y hy =>
      jointMixedDiagonal_radial_deriv_abs_le
        (E := E) (U := U) (V := V i) (χ := χ i) (p := y)
        (K := K) (W := W i) (P := Q) (JC i) hU (hV i) (hc i)
        n a b x w hx hy hK (hW0 i) (hbnd i y.1)⟩
  exact transportVelocity_flatOfGrowth
    (I := I) (E := E) (U := U) (V := V)
    (fL := fL) (fC := fC) (fA := fA) (fZ := fZ) (fV := fV) (fE := fE)
    p W H hW hH hU hV hc JL JC JA JZ JV JE nmax B
    hL hgC hA hZ hAr hZr hVeq hEeq

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology

local instance n01TransportVelocityMixedGrowthStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01TransportVelocityMixedGrowthParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S × ℝ) := Prod.instSMul

private def n01TransportVelocityCircleSMul_cache (S : PhysicalSpacesData) :
    SMul ℝ (CircleSpace S) :=
  Submodule.smul (R := ℝ) (S := ℝ)
    (Analysis.compatibleSubmodule
      (fun n => (S.circle (3 / 4 : ℝ)).level n)
      (S.circle (3 / 4 : ℝ)).bond)

private theorem n01TransportVelocityCircleSMul_cache_eq (S : PhysicalSpacesData) :
    n01TransportVelocityCircleSMul_cache S =
      (inferInstance : SMul ℝ (CircleSpace S)) := rfl

attribute [local instance] n01TransportVelocityCircleSMul_cache

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- This type fixes the actual functions and the order of the two residual labels. -/
private abbrev N01TransportVelocityTowers
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (R : ReturnEquationData S) (base : ℕ) (ε : ℝ)
    (l h : ℕ → ℝ) (χ : ℕ → ℝ → ℝ) : Type :=
  let E := (StateDirections S × ℝ) × CircleSpace S
  let U : Set E := sectorNeighborhood S base ε ε ×ˢ univ
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let fL : ℕ → E × PolarPoint → ℝ := fun _ x =>
    minusCharacteristicSpeed
      (originalCoefficients D S C (liftSectorParameter S C x.1.1)) x.2
  let fA : ℕ → E × PolarPoint → ℝ := fun m x =>
    returnFlowInverseSlope S C (liftSectorParameter S C x.1.1) m x.2
  let f₀ : ℕ → E × PolarPoint → ℝ := fun m x =>
    returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1.1)
      m x.2 (R.residual (liftSectorParameter S C x.1.1))
  let f₁ : ℕ → E × PolarPoint → ℝ := fun m x =>
    returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1.1)
      m x.2 x.1.2
  let fZ : Fin 2 → ℕ → E × PolarPoint → ℝ :=
    Fin.cases f₀ (Fin.cases f₁ Fin.elim0)
  TransportVelocityTowerFamilies U V fL fA fZ

private abbrev N01TransportVelocityCommonGrowth
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S) (base : ℕ) (ε : ℝ)
    (j : ℕ → ℕ) (l h : ℕ → ℝ) (χ : ℕ → ℝ → ℝ)
    (towers : N01TransportVelocityTowers D S C R base ε l h χ)
    (nmax B : ℕ) : Prop :=
  let p := pairGrading (pairGrading (sectorGrading S) realGrading)
    (S.circle (3 / 4 : ℝ)).grading
  let W := fun m => radialE (D.cellIndex (j m))
  let H := fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)
  MixedDiagonalPowerGrowth p W (fun _ => 1) towers.JL nmax B ∧
    AngularDiagonalPowerGrowth p (fun _ => 1) towers.JA nmax B ∧
    ∀ c : Fin 2,
      AngularDiagonalPowerGrowth p (fun m => H m ^ c.val) (towers.JZ c) nmax B

/-- Construct exactly the original characteristic, slope and two displacement towers. -/
private def n01TransportVelocity_buildTowers
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hR : N02Properties D T S C R base ε)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    {lam P : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (y : PolarPoint),
      y.1 ∈ Ioo (l m) (h m) →
      let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
      d ≤ (originalCoefficients D S C z).a y ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b y ^ 2 -
        (originalCoefficients D S C z).a y * (originalCoefficients D S C z).c y)
    (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    : N01TransportVelocityTowers D S C R base ε l h χ := by
  let E₀ : Type := StateDirections S × ℝ
  let E : Type := E₀ × CircleSpace S
  let U₀ : Set E₀ := sectorNeighborhood S base ε ε
  let U : Set E := U₀ ×ˢ univ
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let p₀ : ℕ → Seminorm ℝ E₀ := pairGrading (sectorGrading S) realGrading
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  let fL₀ : ℕ → E₀ × PolarPoint → ℝ := fun _ x =>
    minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) x.2
  let fL : ℕ → E × PolarPoint → ℝ := fun m x => fL₀ m (x.1.1, x.2)
  let fA₀ : ℕ → E₀ × PolarPoint → ℝ := fun m x =>
    returnFlowInverseSlope S C (liftSectorParameter S C x.1) m x.2
  let fA : ℕ → E × PolarPoint → ℝ := fun m x => fA₀ m (x.1.1, x.2)
  let f₀₀ : ℕ → E₀ × PolarPoint → ℝ := fun m x =>
    returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1) m x.2
      (R.residual (liftSectorParameter S C x.1))
  let f₀ : ℕ → E × PolarPoint → ℝ := fun m x => f₀₀ m (x.1.1, x.2)
  let f₁ : ℕ → E × PolarPoint → ℝ := fun m x =>
    returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1.1)
      m x.2 x.1.2
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  have hU₀ : IsOpen U₀ := sectorNeighborhood_isOpen S base ε ε
  have hV (m : ℕ) : IsOpen (V m) := isOpen_Ioo.prod isOpen_univ
  have hdisc (m : ℕ) (z : StateDirections S × ℝ)
      (hz : z ∈ sectorNeighborhood S base ε ε) (y : PolarPoint)
      (hy : y.1 ∈ Ioo (l m) (h m)) :
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b y ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a y *
          (originalCoefficients D S C (liftSectorParameter S C z)).c y := by
    have hd : 0 < lam * W m ^ (-P) / 2 :=
      half_pos (mul_pos hlam (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hW m)) _))
    exact (pow_pos hd 2).trans_le (hpositive (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl) m y hy).2
  let characteristicData : ∃ K : ∀ m, SmoothDirections (U₀ ×ˢ V m) (fL₀ m),
      ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧ UniformWeightedJointGrowth p₀ W K B L :=
    hN.exists_minusCharacteristicSpeed_strip_joint_growth
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      (lam := lam) (P := P) hS hT j hcell l h hl hh hlam hP hpositive
  let JL₀ : ∀ m, SmoothDirections (U₀ ×ˢ V m) (fL₀ m) := characteristicData.choose
  let liftTower : ∀ (m : ℕ) (f : E₀ × PolarPoint → ℝ),
      SmoothDirections (U₀ ×ˢ V m) f →
        SmoothDirections (U ×ˢ V m)
          (fun x : E × PolarPoint => f (x.1.1, x.2)) :=
    fun m f K => SmoothDirections.fstParameter
      (E := E₀) (F := CircleSpace S) (P := PolarPoint) (G := ℝ)
      (U := U₀) (V := V m) (f := f) K hU₀ (hV m)
  let JL : ∀ m, SmoothDirections (U ×ˢ V m) (fL m) :=
    fun m => liftTower m (fL₀ m) (JL₀ m)
  let JA₀ : ∀ m, SmoothDirections (U₀ ×ˢ V m) (fA₀ m) := fun m =>
    hN.returnFlowInverseSlope_parameterSpatialTower
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      hS hT m (l m) (h m) (hl m) (hh m) (hdisc m)
  let JA : ∀ m, SmoothDirections (U ×ˢ V m) (fA m) :=
    fun m => liftTower m (fA₀ m) (JA₀ m)
  let J₀₀ : ∀ m, SmoothDirections (U₀ ×ˢ V m) (f₀₀ m) := fun m =>
    hN.returnCorrectionPulledResidual_parameterSpatialTower
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε)
      hS hT m (l m) (h m) (hl m) (hh m) (hdisc m) χ hχ hχrange hR
  let J₀ : ∀ m, SmoothDirections (U ×ˢ V m) (f₀ m) :=
    fun m => liftTower m (f₀₀ m) (J₀₀ m)
  let J₁ : ∀ m, SmoothDirections (U ×ˢ V m) (f₁ m) := fun m =>
    hN.returnCorrectionPulledDisplacement_parameterSpatialTower
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      hS hT m (l m) (h m) (hl m) (hh m) (hdisc m) χ hχ hχrange
  let fZ : Fin 2 → ℕ → E × PolarPoint → ℝ :=
    Fin.cases f₀ (Fin.cases f₁ Fin.elim0)
  let JZ : ∀ c m, SmoothDirections (U ×ˢ V m) (fZ c m) :=
    transportVelocity_twoTowers
      (I := ℕ) (E := E) (U := U) (V := V) (f₀ := f₀) (f₁ := f₁) J₀ J₁
  exact ⟨JL, JA, JZ⟩

/-- Select the four interpolation orders and assemble their common budget while
all parameter spaces and seminorms are abstract. -/
private def transportVelocity_growthData
    {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} (l h : I → ℝ)
    (p : ℕ → Seminorm ℝ E) (W H : I → ℝ)
    (hp : Monotone p) (hW0 : ∀ i, 0 ≤ W i) (hH : ∀ i, 0 ≤ H i)
    {fL fA : I → E × PolarPoint → ℝ} {fZ : Fin 2 → I → E × PolarPoint → ℝ}
    (JL : ∀ i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fL i))
    (JA : ∀ i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fA i))
    (JZ : ∀ c i, SmoothDirections (U ×ˢ (Ioo (l i) (h i) ×ˢ univ)) (fZ c i))
    (nmax : ℕ)
    (characteristicBounds : ∃ B : ℕ,
      ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ a b : ℕ, a + b ≤ N →
        ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧
          ∀ i (x : E), x ∈ U → ∀ w : E, p B x ≤ A → p B w ≤ 1 →
            ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
              |jointMixedDiagonal (JL i) n a b x w y| ≤ K * W i ^ Q *
                (1 + p (N + B + 1) x + p (N + B + 1) w) ^
                  (((a + b : ℕ) : ℝ) / ((N : ℝ) + 1)))
    (slopeBounds : ∃ B : ℕ,
      ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ i (x : E), x ∈ U → ∀ w : E,
          p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
            |jointMixedDiagonal (JA i) n 0 b x w y| ≤ K *
              (1 + p (N + B + 1) x + p (N + B + 1) w) ^
                ((b : ℝ) / ((N : ℝ) + 1)))
    (residualBounds : ∃ B : ℕ,
      ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ i (x : E), x ∈ U → ∀ w : E,
          p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
            |jointMixedDiagonal (JZ 0 i) n 0 b x w y| ≤ K *
              (1 + p (N + B + 1) x + p (N + B + 1) w) ^
                ((b : ℝ) / ((N : ℝ) + 1)))
    (displacementBounds : ∃ B : ℕ,
      ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ i (x : E), x ∈ U → ∀ w : E,
          p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
            |jointMixedDiagonal (JZ 1 i) n 0 b x w y| ≤ K * H i *
              (1 + p (N + B + 1) x + p (N + B + 1) w) ^
                ((b : ℝ) / ((N : ℝ) + 1)))
    : TransportVelocityGrowthData (fun B =>
      MixedDiagonalPowerGrowth p W (fun _ => 1) JL nmax B ∧
        AngularDiagonalPowerGrowth p (fun _ => 1) JA nmax B ∧
        ∀ c : Fin 2,
          AngularDiagonalPowerGrowth p (fun i => H i ^ c.val) (JZ c) nmax B) := by
  let BL : ℕ := characteristicBounds.choose
  have hBL : ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ a b : ℕ, a + b ≤ N →
      ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧
        ∀ i (x : E), x ∈ U → ∀ w : E, p BL x ≤ A → p BL w ≤ 1 →
          ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
            |jointMixedDiagonal (JL i) n a b x w y| ≤ K * W i ^ Q *
              (1 + p (N + BL + 1) x + p (N + BL + 1) w) ^
                (((a + b : ℕ) : ℝ) / ((N : ℝ) + 1)) := characteristicBounds.choose_spec
  let BA : ℕ := slopeBounds.choose
  have hBA : ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i (x : E), x ∈ U → ∀ w : E,
        p BA x ≤ A → p BA w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
          |jointMixedDiagonal (JA i) n 0 b x w y| ≤ K *
            (1 + p (N + BA + 1) x + p (N + BA + 1) w) ^
              ((b : ℝ) / ((N : ℝ) + 1)) := slopeBounds.choose_spec
  let B₀ : ℕ := residualBounds.choose
  have hB₀ : ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i (x : E), x ∈ U → ∀ w : E,
        p B₀ x ≤ A → p B₀ w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
          |jointMixedDiagonal (JZ 0 i) n 0 b x w y| ≤ K *
            (1 + p (N + B₀ + 1) x + p (N + B₀ + 1) w) ^
              ((b : ℝ) / ((N : ℝ) + 1)) := residualBounds.choose_spec
  let B₁ : ℕ := displacementBounds.choose
  have hB₁ : ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ i (x : E), x ∈ U → ∀ w : E,
        p B₁ x ≤ A → p B₁ w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l i) (h i) →
          |jointMixedDiagonal (JZ 1 i) n 0 b x w y| ≤ K * H i *
            (1 + p (N + B₁ + 1) x + p (N + B₁ + 1) w) ^
              ((b : ℝ) / ((N : ℝ) + 1)) := displacementBounds.choose_spec
  let B : ℕ := BL + BA + B₀ + B₁
  have hbL : BL ≤ B := by dsimp only [B]; omega
  have hbA : BA ≤ B := by dsimp only [B]; omega
  have hb0 : B₀ ≤ B := by dsimp only [B]; omega
  have hb1 : B₁ ≤ B := by dsimp only [B]; omega
  have hcommon :
      MixedDiagonalPowerGrowth p W (fun _ => 1) JL nmax B ∧
        AngularDiagonalPowerGrowth p (fun _ => 1) JA nmax B ∧
        ∀ c : Fin 2,
          AngularDiagonalPowerGrowth p (fun i => H i ^ c.val) (JZ c) nmax B :=
    transportVelocity_commonGrowth
      (I := I) (E := E) (U := U) (fL := fL) (fA := fA) (fZ := fZ)
      l h p W H hp hW0 hH JL JA JZ nmax BL BA B₀ B₁ B
      hbL hbA hb0 hb1 hBL hBA hB₀ hB₁
  exact ⟨BL, BA, B₀, B₁, hcommon⟩

/-- Choose each original interpolation order once and keep their sum as the common order. -/
private def n01TransportVelocity_buildGrowth
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hR : N02Properties D T S C R base ε)
    (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) → ∀ θ,
        1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
        deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    {lam P : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (y : PolarPoint),
      y.1 ∈ Ioo (l m) (h m) →
      let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
      d ≤ (originalCoefficients D S C z).a y ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b y ^ 2 -
        (originalCoefficients D S C z).a y * (originalCoefficients D S C z).c y)
    (χ : ℕ → ℝ → ℝ)
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (towers : N01TransportVelocityTowers D S C R base ε l h χ) (nmax : ℕ) :
    TransportVelocityGrowthData
      (N01TransportVelocityCommonGrowth D T S C R base ε j l h χ towers nmax) := by
  let E₀ : Type := StateDirections S × ℝ
  let E : Type := E₀ × CircleSpace S
  let U₀ : Set E₀ := sectorNeighborhood S base ε ε
  let U : Set E := U₀ ×ˢ univ
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let p₀ : ℕ → Seminorm ℝ E₀ := pairGrading (sectorGrading S) realGrading
  let p : ℕ → Seminorm ℝ E := pairGrading p₀ (S.circle (3 / 4 : ℝ)).grading
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  let H : ℕ → ℝ := fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)
  let fL₀ : ℕ → E₀ × PolarPoint → ℝ := fun _ x =>
    minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) x.2
  let fL : ℕ → E × PolarPoint → ℝ := fun m x => fL₀ m (x.1.1, x.2)
  let fA₀ : ℕ → E₀ × PolarPoint → ℝ := fun m x =>
    returnFlowInverseSlope S C (liftSectorParameter S C x.1) m x.2
  let fA : ℕ → E × PolarPoint → ℝ := fun m x => fA₀ m (x.1.1, x.2)
  let f₀₀ : ℕ → E₀ × PolarPoint → ℝ := fun m x =>
    returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1) m x.2
      (R.residual (liftSectorParameter S C x.1))
  let f₀ : ℕ → E × PolarPoint → ℝ := fun m x => f₀₀ m (x.1.1, x.2)
  let f₁ : ℕ → E × PolarPoint → ℝ := fun m x =>
    returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1.1)
      m x.2 x.1.2
  let fZ : Fin 2 → ℕ → E × PolarPoint → ℝ :=
    Fin.cases f₀ (Fin.cases f₁ Fin.elim0)
  let JL : ∀ m, SmoothDirections (U ×ˢ V m) (fL m) := towers.JL
  let JA : ∀ m, SmoothDirections (U ×ˢ V m) (fA m) := towers.JA
  let JZ : ∀ c m, SmoothDirections (U ×ˢ V m) (fZ c m) := towers.JZ
  let J₀ : ∀ m, SmoothDirections (U ×ˢ V m) (f₀ m) := JZ 0
  let J₁ : ∀ m, SmoothDirections (U ×ˢ V m) (f₁ m) := JZ 1
  have hp : Monotone p := correctionParameterGrading_monotone S
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  have hW0 (m : ℕ) : 0 ≤ W m := zero_le_one.trans (hW m)
  have hH (m : ℕ) : 0 ≤ H m := Real.rpow_nonneg
    ((material_circle_sample_weights_pos hT hN.1.1).2 m).le _
  let characteristicBounds : ∃ B : ℕ,
      ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ a b : ℕ, a + b ≤ N →
        ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧
          ∀ m (x : E), x ∈ U → ∀ w : E, p B x ≤ A → p B w ≤ 1 →
            ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
              |jointMixedDiagonal (JL m) n a b x w y| ≤ K * W m ^ Q *
                (1 + p (N + B + 1) x + p (N + B + 1) w) ^
                  (((a + b : ℕ) : ℝ) / ((N : ℝ) + 1)) :=
    hN.minusCharacteristicSpeed_correction_mixed_interpolation
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      (lam := lam) (P := P) hS hT j hcell l h hl hh hlam hP hpositive JL nmax
  let slopeBounds : ∃ B : ℕ,
      ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ m (x : E), x ∈ U → ∀ w : E,
          p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
            |jointMixedDiagonal (JA m) n 0 b x w y| ≤ K *
              (1 + p (N + B + 1) x + p (N + B + 1) w) ^
                ((b : ℝ) / ((N : ℝ) + 1)) :=
    hN.returnFlowInverseSlope_angular_diagonal_interpolation
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      hS hT hflow l h hl hh JA nmax
  let residualBounds : ∃ B : ℕ,
      ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ m (x : E), x ∈ U → ∀ w : E,
          p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
            |jointMixedDiagonal (J₀ m) n 0 b x w y| ≤ K *
              (1 + p (N + B + 1) x + p (N + B + 1) w) ^
                ((b : ℝ) / ((N : ℝ) + 1)) :=
    hN.returnCorrectionPulledResidual_angular_diagonal_interpolation
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε)
      hS hT hflow l h hl hh χ hχrange hR J₀ nmax
  let displacementBounds : ∃ B : ℕ,
      ∀ A : ℝ, 0 ≤ A → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ m (x : E), x ∈ U → ∀ w : E,
          p B x ≤ A → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
            |jointMixedDiagonal (J₁ m) n 0 b x w y| ≤ K * H m *
              (1 + p (N + B + 1) x + p (N + B + 1) w) ^
                ((b : ℝ) / ((N : ℝ) + 1)) :=
    hN.returnCorrectionPulledDisplacement_angular_diagonal_interpolation
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      hS hT hflow l h hl hh χ hχrange J₁ nmax
  exact transportVelocity_growthData
    (I := ℕ) (E := E) (U := U) (fL := fL) (fA := fA) (fZ := fZ)
    l h p W H hp hW0 hH JL JA JZ nmax
    characteristicBounds slopeBounds residualBounds displacementBounds

/-- The actual transport equations finish the supplied towers at the selected common order. -/
private theorem n01TransportVelocity_flatFromGrowth
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hR : N02Properties D T S C R base ε)
    (j : ℕ → ℕ)
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    {lam P : ℝ} (hlam : 0 < lam)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (y : PolarPoint),
      y.1 ∈ Ioo (l m) (h m) →
      let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
      d ≤ (originalCoefficients D S C z).a y ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b y ^ 2 -
        (originalCoefficients D S C z).a y * (originalCoefficients D S C z).c y)
    (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hcutoff : ∀ k : ℕ, ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ K * radialE (D.cellIndex (j m)) ^ Q)
    (JV : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2))
    (JE : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
          (R.residual (liftSectorParameter S C x.1.1))))
    (nmax B : ℕ)
    (towers : N01TransportVelocityTowers D S C R base ε l h χ)
    (hcommon : N01TransportVelocityCommonGrowth D T S C R base ε j l h χ towers nmax B) :
    let p := pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading
    let W := fun m => radialE (D.cellIndex (j m))
    FlatMixedDiagonalGrowth p W (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)) JV
      nmax B (B + 1) ∧
      FlatMixedDiagonalGrowth p W (fun _ => 1) JE nmax B (B + 1) := by
  let E₀ : Type := StateDirections S × ℝ
  let E : Type := E₀ × CircleSpace S
  let U₀ : Set E₀ := sectorNeighborhood S base ε ε
  let U : Set E := U₀ ×ˢ univ
  let V : ℕ → Set PolarPoint := fun m => Ioo (l m) (h m) ×ˢ univ
  let p₀ : ℕ → Seminorm ℝ E₀ := pairGrading (sectorGrading S) realGrading
  let p : ℕ → Seminorm ℝ E := pairGrading p₀ (S.circle (3 / 4 : ℝ)).grading
  let W : ℕ → ℝ := fun m => radialE (D.cellIndex (j m))
  let H : ℕ → ℝ := fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)
  let fL₀ : ℕ → E₀ × PolarPoint → ℝ := fun _ x =>
    minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) x.2
  let fL : ℕ → E × PolarPoint → ℝ := fun m x => fL₀ m (x.1.1, x.2)
  let fA₀ : ℕ → E₀ × PolarPoint → ℝ := fun m x =>
    returnFlowInverseSlope S C (liftSectorParameter S C x.1) m x.2
  let fA : ℕ → E × PolarPoint → ℝ := fun m x => fA₀ m (x.1.1, x.2)
  let f₀₀ : ℕ → E₀ × PolarPoint → ℝ := fun m x =>
    returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1) m x.2
      (R.residual (liftSectorParameter S C x.1))
  let f₀ : ℕ → E × PolarPoint → ℝ := fun m x => f₀₀ m (x.1.1, x.2)
  let f₁ : ℕ → E × PolarPoint → ℝ := fun m x =>
    returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1.1)
      m x.2 x.1.2
  let fZ : Fin 2 → ℕ → E × PolarPoint → ℝ :=
    Fin.cases f₀ (Fin.cases f₁ Fin.elim0)
  let JL : ∀ m, SmoothDirections (U ×ˢ V m) (fL m) := towers.JL
  let JA : ∀ m, SmoothDirections (U ×ˢ V m) (fA m) := towers.JA
  let JZ : ∀ c m, SmoothDirections (U ×ˢ V m) (fZ c m) := towers.JZ
  have hW (m : ℕ) : 1 ≤ W m := one_le_radialE_of_nat _
  have hH (m : ℕ) : 0 ≤ H m := Real.rpow_nonneg
    ((material_circle_sample_weights_pos hT hN.1.1).2 m).le _
  have hU : IsOpen U := (sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ
  have hV (m : ℕ) : IsOpen (V m) := isOpen_Ioo.prod isOpen_univ
  have hc (m : ℕ) : Convex ℝ (U ×ˢ V m) :=
    ((sectorNeighborhood_convex S base ε ε).prod (convex_univ : Convex ℝ (univ : Set (CircleSpace S)))).prod
      ((convex_Ioo (l m) (h m)).prod (convex_univ : Convex ℝ (univ : Set ℝ)))
  have hdisc (m : ℕ) (z : StateDirections S × ℝ)
      (hz : z ∈ sectorNeighborhood S base ε ε) (y : PolarPoint)
      (hy : y.1 ∈ Ioo (l m) (h m)) :
      0 < (originalCoefficients D S C (liftSectorParameter S C z)).b y ^ 2 -
        (originalCoefficients D S C (liftSectorParameter S C z)).a y *
          (originalCoefficients D S C (liftSectorParameter S C z)).c y := by
    have hd : 0 < lam * W m ^ (-P) / 2 :=
      half_pos (mul_pos hlam (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hW m)) _))
    exact (pow_pos hd 2).trans_le (hpositive (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl) m y hy).2
  have hAr (m : ℕ) (x : E) (hx : x ∈ U) (y : PolarPoint) (hy : y ∈ V m) :
      radialPartial (returnFlowInverseSlope S C (liftSectorParameter S C x.1) m) y =
        angularPartial (minusCharacteristicSpeed (originalCoefficients D S C
          (liftSectorParameter S C x.1))) y *
            returnFlowInverseSlope S C (liftSectorParameter S C x.1) m y -
        minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) y *
          angularPartial (returnFlowInverseSlope S C (liftSectorParameter S C x.1) m) y :=
    hN.returnFlowInverseSlope_transport_of_discriminant
      (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      (z := liftSectorParameter S C x.1) hS hT
      (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
      (hN.2.2.1.liftSectorParameter_sector x.1) m y
      ⟨(hl m).trans hy.1.1, hy.1.2.trans (hh m)⟩ (hdisc m x.1 hx.1 y hy.1)
  have hZr (c : Fin 2) (m : ℕ) (x : E) (hx : x ∈ U) (y : PolarPoint) (hy : y ∈ V m) :
      radialPartial (fun q => fZ c m (x, q)) y =
        -((minusCharacteristicSpeed (originalCoefficients D S C (liftSectorParameter S C x.1)) y +
            deriv (χ m) y.1 * returnFlowInverseSlope S C (liftSectorParameter S C x.1) m y *
              fZ 0 m (x, y)) * angularPartial (fun q => fZ c m (x, q)) y) := by
    have hrec (ρ : CircleSpace S) :
        radialPartial (fun q => returnCorrectionPulledDisplacementLinear S C χ
          (liftSectorParameter S C x.1) m q ρ) y =
          -(minusCharacteristicSpeed (originalCoefficients D S C
              (liftSectorParameter S C x.1)) y +
            deriv (χ m) y.1 * returnFlowInverseSlope S C (liftSectorParameter S C x.1) m y *
              returnCorrectionPulledDisplacementLinear S C χ (liftSectorParameter S C x.1)
                m y (R.residual (liftSectorParameter S C x.1))) *
            angularPartial (fun q => returnCorrectionPulledDisplacementLinear S C χ
              (liftSectorParameter S C x.1) m q ρ) y :=
      hN.returnCorrectionPulledDisplacementLinear_transport_actual
        (D := D) (T := T) (S := S) (C := C) (R := R)
        (base := base) (loss := loss) (ε := ε) (z := liftSectorParameter S C x.1) hS hT
        (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
        (hN.2.2.1.liftSectorParameter_sector x.1) hR χ m (hχ m) (hχrange m)
        ρ y ⟨(hl m).trans hy.1.1, hy.1.2.trans (hh m)⟩
    refine Fin.cases ?_ (fun c => ?_) c
    · simpa only [fZ, f₀, f₀₀, Fin.cases_zero, neg_mul] using
        hrec (R.residual (liftSectorParameter S C x.1))
    · refine Fin.cases ?_ (fun i => Fin.elim0 i) c
      simpa only [fZ, f₀, f₀₀, f₁, Fin.cases_succ, Fin.cases_zero, neg_mul] using hrec x.2
  exact transportVelocity_flatWithRadialCutoff
    (I := ℕ) (E := E) (U := U) (V := V)
    (fL := fL) (fA := fA) (fZ := fZ)
    (fV := fun m x => returnCorrectionVelocityLinear D S C χ
      (liftSectorParameter S C x.1.1) m x.2 x.1.2)
    (fE := fun m x => returnCorrectionVelocityLinear D S C χ
      (liftSectorParameter S C x.1.1) m x.2
        (R.residual (liftSectorParameter S C x.1.1)))
    p W H hW hH hU hV hc χ hχ hcutoff JL JA JZ JV JE nmax B
    hcommon.1 hcommon.2.1 hcommon.2.2 hAr hZr
    (fun m x _ =>
      (returnCorrectionVelocityLinear_eq_transportProduct D S C χ
        (liftSectorParameter S C x.1.1) m x.2 x.1.2).symm)
    (fun m x _ =>
      (returnCorrectionVelocityLinear_eq_transportProduct D S C χ
        (liftSectorParameter S C x.1.1) m x.2
          (R.residual (liftSectorParameter S C x.1.1))).symm)

/-- Fixed-loss bounds for the actual independent and frozen-residual
velocities. All geometric assumptions are the witnesses produced by
the buffered, uniform N01 neighborhood construction. -/
theorem N01Properties.returnCorrectionVelocity_flatMixedGrowth
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hR : N02Properties D T S C R base ε)
    (hflow : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) → ∀ θ,
        1 / 2 ≤ deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ∧
        deriv (C.minusFlow (liftSectorParameter S C z) m r) θ ≤ 3 / 2)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (l h : ℕ → ℝ) (hl : ∀ m, C.left m < l m) (hh : ∀ m, h m < C.right m)
    {lam P : ℝ} (hlam : 0 < lam) (hP : 0 ≤ P)
    (hpositive : ∀ z ∈ stateNeighborhood S C base ε, ∀ (m : ℕ) (y : PolarPoint),
      y.1 ∈ Ioo (l m) (h m) →
      let d := lam * radialE (D.cellIndex (j m)) ^ (-P) / 2
      d ≤ (originalCoefficients D S C z).a y ∧
      d ^ 2 ≤ (originalCoefficients D S C z).b y ^ 2 -
        (originalCoefficients D S C z).a y * (originalCoefficients D S C z).c y)
    (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (hcutoff : ∀ k : ℕ, ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧ ∀ m r,
      |iteratedDeriv k (χ m) r| ≤ K * radialE (D.cellIndex (j m)) ^ Q)
    (JV : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2 x.1.2))
    (JE : ∀ m, SmoothDirections
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ (Ioo (l m) (h m) ×ˢ univ))
      (fun x : ((StateDirections S × ℝ) × CircleSpace S) × PolarPoint =>
        returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C x.1.1) m x.2
          (R.residual (liftSectorParameter S C x.1.1))))
    (nmax : ℕ) :
    let p := pairGrading (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading
    let W := fun m => radialE (D.cellIndex (j m))
    ∃ B : ℕ,
      FlatMixedDiagonalGrowth p W (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ)) JV
        nmax B (B + 1) ∧
      FlatMixedDiagonalGrowth p W (fun _ => 1) JE nmax B (B + 1) := by
  let towers : N01TransportVelocityTowers D S C R base ε l h χ :=
    n01TransportVelocity_buildTowers
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε) (lam := lam) (P := P)
      hN hS hT hR j hcell l h hl hh hlam hP hpositive χ hχ hχrange
  let bounds : TransportVelocityGrowthData
      (N01TransportVelocityCommonGrowth D T S C R base ε j l h χ towers nmax) :=
    n01TransportVelocity_buildGrowth
      (D := D) (T := T) (S := S) (C := C) (R := R)
      (base := base) (loss := loss) (ε := ε) (lam := lam) (P := P)
      hN hS hT hR hflow j hcell l h hl hh hlam hP hpositive χ hχrange towers nmax
  let B : ℕ := bounds.BL + bounds.BA + bounds.B₀ + bounds.B₁
  refine ⟨B, ?_⟩
  exact n01TransportVelocity_flatFromGrowth
    (D := D) (T := T) (S := S) (C := C) (R := R)
    (base := base) (loss := loss) (ε := ε) (lam := lam) (P := P)
    hN hS hT hR j l h hl hh hlam hpositive χ hχ hχrange hcutoff
    JV JE nmax B towers bounds.common

end ContinuousFlexibility.Statements
