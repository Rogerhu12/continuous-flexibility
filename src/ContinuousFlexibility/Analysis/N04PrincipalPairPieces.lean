module

public import ContinuousFlexibility.Analysis.N04PrincipalPairAlgebra

/-!
# Reindexing and covering the actual pieces

Piece indices are discrete labels. Reindexing therefore preserves every
parameter and spatial tower. A cover by two predicates combines their
genuine towers into one family defined on every index, while taking one
common low order and uniform constants for the two estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {ι κ : Type*} {U : Set X} {Ω : Set PolarPoint}

theorem n04Principal_weightedTower_reindex
    (p : ℕ → Seminorm ℝ X) (base : ℕ) (E W : ι → ℝ) (ρ : κ → ι)
    {f : ι → X → PolarPoint → ℝ}
    (R : ∀ m, MixedJetRegularity U Ω (f m))
    (hb : N04PrincipalWeightedTowerBounds p base E W R) :
    N04PrincipalWeightedTowerBounds p base (fun n => E (ρ n)) (fun n => W (ρ n))
      (fun n => R (ρ n)) := by
  intro k
  obtain ⟨loss, hloss⟩ := hb k
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hloss s
  exact ⟨B, hB, fun n a b hab q hq x hx hlow v =>
    hbound (ρ n) a b hab q hq x hx hlow v⟩

namespace N04PrincipalPairBounds

variable {p : ℕ → Seminorm ℝ X} {E W : ι → ℝ}
  {f : ι → X → PolarPoint → ℝ} {f₀ : ι → PolarPoint → ℝ}

/-- The same paired family with any chosen indexing map. -/
theorem reindex (hf : N04PrincipalPairBounds (U := U) (Ω := Ω) p E W f f₀)
    (ρ : κ → ι) :
    N04PrincipalPairBounds (U := U) (Ω := Ω) p
      (fun n => E (ρ n)) (fun n => W (ρ n))
      (fun n => f (ρ n)) (fun n => f₀ (ρ n)) := by
  obtain ⟨base, RF, RR, RD, hF, hR, hD⟩ := hf
  exact ⟨base, (fun n => RF (ρ n)), (fun n => RR (ρ n)), (fun n => RD (ρ n)),
    n04Principal_weightedTower_reindex p base E (fun _ => 1) ρ RF hF,
    n04Principal_weightedTower_reindex p base E (fun _ => 1) ρ RR hR,
    n04Principal_weightedTower_reindex p base E W ρ RD hD⟩

end N04PrincipalPairBounds

private def n04Principal_pieceRegularity
    (P Q : ι → Prop) (hcover : ∀ m, P m ∨ Q m)
    (f : ι → X → PolarPoint → ℝ)
    (RP : ∀ m : {m // P m}, MixedJetRegularity U Ω (f m.val))
    (RQ : ∀ m : {m // Q m}, MixedJetRegularity U Ω (f m.val)) :
    ∀ m, MixedJetRegularity U Ω (f m) := by
  classical
  exact fun m => if hm : P m then RP ⟨m, hm⟩ else RQ ⟨m, (hcover m).resolve_left hm⟩

private theorem n04Principal_weightedTower_union_subtype
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (bp bq : ℕ)
    (E W : ι → ℝ) (hE : ∀ m, 1 ≤ E m) (hW : ∀ m, 0 ≤ W m)
    (P Q : ι → Prop) (hcover : ∀ m, P m ∨ Q m)
    (f : ι → X → PolarPoint → ℝ)
    (RP : ∀ m : {m // P m}, MixedJetRegularity U Ω (f m.val))
    (RQ : ∀ m : {m // Q m}, MixedJetRegularity U Ω (f m.val))
    (hP : N04PrincipalWeightedTowerBounds p bp
      (fun m : {m // P m} => E m.val) (fun m => W m.val) RP)
    (hQ : N04PrincipalWeightedTowerBounds p bq
      (fun m : {m // Q m} => E m.val) (fun m => W m.val) RQ) :
    N04PrincipalWeightedTowerBounds p (max bp bq) E W
      (n04Principal_pieceRegularity P Q hcover f RP RQ) := by
  classical
  have hP' := n04Principal_weightedTower_monoBase p hp
    (fun m : {m // P m} => E m.val) (fun m => W m.val)
    (fun m => hE m.val) (fun m => hW m.val) (le_max_left bp bq) RP hP
  have hQ' := n04Principal_weightedTower_monoBase p hp
    (fun m : {m // Q m} => E m.val) (fun m => W m.val)
    (fun m => hE m.val) (fun m => hW m.val) (le_max_right bp bq) RQ hQ
  intro k
  obtain ⟨lp, hlp⟩ := hP' k
  obtain ⟨lq, hlq⟩ := hQ' k
  refine ⟨max lp lq, fun s => ?_⟩
  obtain ⟨Bp, hBp, hpb⟩ := hlp s
  obtain ⟨Bq, hBq, hqb⟩ := hlq s
  refine ⟨Bp + Bq, add_pos hBp hBq, ?_⟩
  intro m a b hab q hq x hx hlow v
  have he : 0 ≤ E m := zero_le_one.trans (hE m)
  have hB : 0 ≤ Bp + Bq := (add_pos hBp hBq).le
  have hraise {C : ℝ} {l : ℕ} (hC : 0 < C) (hCB : C ≤ Bp + Bq)
      (hl : l ≤ max lp lq) :
      C * E m ^ C * W m * oneHighVariationWeight p (max bp bq) (s + l) x v ≤
        (Bp + Bq) * E m ^ (Bp + Bq) * W m *
          oneHighVariationWeight p (max bp bq) (s + max lp lq) x v := by
    have hcoefficient : C * E m ^ C * W m ≤ (Bp + Bq) * E m ^ (Bp + Bq) * W m :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hCB (Real.rpow_le_rpow_of_exponent_le (hE m) hCB)
          (Real.rpow_nonneg he _) hB) (hW m)
    exact mul_le_mul hcoefficient
      (oneHighVariationWeight_mono hp le_rfl (Nat.add_le_add_left hl s) x v)
      (oneHighVariationWeight_nonneg _ _ _ _ _)
      (mul_nonneg (mul_nonneg hB (Real.rpow_nonneg he _)) (hW m))
  by_cases hm : P m
  · have hb := (hpb ⟨m, hm⟩ a b hab q hq x hx hlow v).trans
      (hraise hBp (le_add_of_nonneg_right hBq.le) (le_max_left lp lq))
    simpa only [n04Principal_pieceRegularity, dif_pos hm] using hb
  · have hb := (hqb ⟨m, (hcover m).resolve_left hm⟩ a b hab q hq x hx hlow v).trans
      (hraise hBq (le_add_of_nonneg_left hBp.le) (le_max_right lp lq))
    simpa only [n04Principal_pieceRegularity, dif_neg hm] using hb

namespace N04PrincipalPairBounds

variable {p : ℕ → Seminorm ℝ X} {E W : ι → ℝ}
  {f : ι → X → PolarPoint → ℝ} {f₀ : ι → PolarPoint → ℝ}

/-- A cover by two piece predicates supplies genuine paired towers on
every original piece, including all parameter orders. -/
theorem union_subtype {P Q : ι → Prop}
    (hf : N04PrincipalPairBounds (U := U) (Ω := Ω) p
      (fun m : {m // P m} => E m.val) (fun m => W m.val)
      (fun m => f m.val) (fun m => f₀ m.val))
    (hg : N04PrincipalPairBounds (U := U) (Ω := Ω) p
      (fun m : {m // Q m} => E m.val) (fun m => W m.val)
      (fun m => f m.val) (fun m => f₀ m.val))
    (hp : Monotone p) (hE : ∀ m, 1 ≤ E m) (hW : ∀ m, 0 ≤ W m)
    (hcover : ∀ m, P m ∨ Q m) :
    N04PrincipalPairBounds (U := U) (Ω := Ω) p E W f f₀ := by
  obtain ⟨bp, RF, RR, RD, hF, hR, hD⟩ := hf
  obtain ⟨bq, SF, SR, SD, hG, hS, hQ⟩ := hg
  let TF := n04Principal_pieceRegularity P Q hcover f RF SF
  let TR := n04Principal_pieceRegularity P Q hcover (fun m _ => f₀ m) RR SR
  let TD := n04Principal_pieceRegularity P Q hcover (fun m x q => f m x q - f₀ m q) RD SD
  exact ⟨max bp bq, TF, TR, TD,
    n04Principal_weightedTower_union_subtype p hp bp bq E (fun _ => 1) hE
      (fun _ => zero_le_one) P Q hcover f RF SF hF hG,
    n04Principal_weightedTower_union_subtype p hp bp bq E (fun _ => 1) hE
      (fun _ => zero_le_one) P Q hcover (fun m _ => f₀ m) RR SR hR hS,
    n04Principal_weightedTower_union_subtype p hp bp bq E W hE hW
      P Q hcover (fun m x q => f m x q - f₀ m q) RD SD hD hQ⟩

end N04PrincipalPairBounds

end ContinuousFlexibility.Analysis
