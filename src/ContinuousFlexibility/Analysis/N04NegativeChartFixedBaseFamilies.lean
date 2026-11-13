import ContinuousFlexibility.Analysis.TameFixedBaseCompositionBounds
import ContinuousFlexibility.Analysis.TameUniformSmoothFamily

/-!
# Finite assembly with a common low order

This strengthens the existing uniform-family estimate by choosing its low
order before every parameter order. The objects remain genuine directional
towers. The elementary operations and the actual partition chain rule
preserve this order of quantifiers.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {I E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]

/-- Uniform one-high estimates with one low order for the entire tower. -/
def N04FixedBaseSmoothFamilyOn
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (U : Set E) (f : I → E → F) : Prop :=
  ∃ J : ∀ i, SmoothDirections U (f i), ∃ base : ℕ,
    ∀ n : ℕ, ∃ loss : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ U → p base x ≤ R →
      ∀ v : Fin n → E, q s ((J i).D n x v) ≤ C * tameJetSize p n s loss base x v

theorem N04FixedBaseSmoothFamilyOn.uniform
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f : I → E → F} (hf : N04FixedBaseSmoothFamilyOn p q U f) :
    UniformSmoothFamilyOn p q U f := by
  obtain ⟨J, B, hb⟩ := hf
  refine ⟨J, fun n => ?_⟩
  apply uniformFamilyLowGrowthOn_of_oneHigh
  obtain ⟨L, hL⟩ := hb n
  exact ⟨B, L, hL⟩

theorem N04FixedBaseSmoothFamilyOn.congr
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f g : I → E → F} (hf : N04FixedBaseSmoothFamilyOn p q U f)
    (heq : ∀ i x, x ∈ U → f i x = g i x) : N04FixedBaseSmoothFamilyOn p q U g := by
  obtain ⟨J, B, hb⟩ := hf
  exact ⟨fun i => (J i).congr (heq i), B, hb⟩

theorem N04FixedBaseSmoothFamilyOn.reindex
    {K : Type*} {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f : I → E → F} (hf : N04FixedBaseSmoothFamilyOn p q U f) (a : K → I) :
    N04FixedBaseSmoothFamilyOn p q U (fun k => f (a k)) := by
  obtain ⟨J, B, hb⟩ := hf
  refine ⟨fun k => J (a k), B, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hb n
  refine ⟨L, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hL R hR s
  exact ⟨C, hC, fun k x hx hlow v => hc (a k) x hx hlow v⟩

theorem N04FixedBaseSmoothFamilyOn.restrict
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U V : Set E}
    {f : I → E → F} (hf : N04FixedBaseSmoothFamilyOn p q U f)
    (hV : IsOpen V) (hsub : V ⊆ U) : N04FixedBaseSmoothFamilyOn p q V f := by
  obtain ⟨J, B, hb⟩ := hf
  refine ⟨fun i => (J i).restrict hV hsub, B, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hb n
  refine ⟨L, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hL R hR s
  exact ⟨C, hC, fun i x hx hlow v => hc i x (hsub hx) hlow v⟩

/-- The same bounds hold for any genuine tower of the same family. -/
theorem N04FixedBaseSmoothFamilyOn.jets
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f : I → E → F} (hf : N04FixedBaseSmoothFamilyOn p q U f)
    (J : ∀ i, SmoothDirections U (f i)) :
    ∃ base : ℕ, ∀ n : ℕ, ∃ loss : ℕ,
      ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i x, x ∈ U → p base x ≤ R → ∀ v : Fin n → E,
        q s ((J i).D n x v) ≤ C * tameJetSize p n s loss base x v := by
  obtain ⟨K, B, hb⟩ := hf
  refine ⟨B, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hb n
  refine ⟨L, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hL R hR s
  refine ⟨C, hC, fun i x hx hlow v => ?_⟩
  rw [(J i).unique (K i) n x hx]
  exact hc i x hx hlow v

theorem N04FixedBaseSmoothFamilyOn.postContinuousLinear
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : I → E → F} (hf : N04FixedBaseSmoothFamilyOn p q U f)
    (L : I → F →L[ℝ] G) (loss : ℕ)
    (hL : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ i y, r s (L i y) ≤ C * q (s + loss) y) :
    N04FixedBaseSmoothFamilyOn p r U (fun i x => L i (f i x)) := by
  obtain ⟨J, B, hb⟩ := hf
  refine ⟨fun i => smoothDirectionsPostContinuousLinear (J i) (L i), B, fun n => ?_⟩
  obtain ⟨d, hd⟩ := hb n
  refine ⟨loss + d, fun R hR s => ?_⟩
  obtain ⟨A, hA, ha⟩ := hL s
  obtain ⟨C, hC, hc⟩ := hd R hR (s + loss)
  refine ⟨A * C, mul_nonneg hA hC, fun i x hx hlow v => ?_⟩
  change r s (L i ((J i).D n x v)) ≤ _
  have h := (ha i ((J i).D n x v)).trans (mul_le_mul_of_nonneg_left
    (hc i x hx hlow v) hA)
  simpa only [tameJetSize, Nat.add_assoc, mul_assoc] using h

theorem N04FixedBaseSmoothFamilyOn.postTameContinuousLinear
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : I → E → F} (hf : N04FixedBaseSmoothFamilyOn p q U f)
    (L : F →L[ℝ] G) {loss : ℕ} (hL : IsTameLinear q r L.toLinearMap loss 0) :
    N04FixedBaseSmoothFamilyOn p r U (fun i x => L (f i x)) := by
  apply hf.postContinuousLinear (fun _ => L) loss
  intro s
  obtain ⟨C, hc⟩ := hL s (Nat.zero_le s)
  exact ⟨C, C.coe_nonneg, fun _ y => hc y⟩

theorem N04FixedBaseSmoothFamilyOn.prodMk
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : I → E → F} {g : I → E → G}
    (hf : N04FixedBaseSmoothFamilyOn p q U f) (hp : Monotone p)
    (hg : N04FixedBaseSmoothFamilyOn p r U g) :
    N04FixedBaseSmoothFamilyOn p (pairGrading q r) U (fun i x => (f i x, g i x)) := by
  obtain ⟨J, BJ, hbJ⟩ := hf
  obtain ⟨K, BK, hbK⟩ := hg
  refine ⟨fun i => smoothDirectionsProd (J i) (K i), max BJ BK, fun n => ?_⟩
  obtain ⟨d, hd⟩ := hbJ n
  obtain ⟨e, he⟩ := hbK n
  refine ⟨max d e, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hd R hR s
  obtain ⟨A, hA, ha⟩ := he R hR s
  refine ⟨C + A, add_nonneg hC hA, fun i x hx hlow v => ?_⟩
  have hJ := (hc i x hx ((hp (le_max_left BJ BK) x).trans hlow) v).trans
    (mul_le_mul_of_nonneg_left
      (tameJetSize_mono hp (le_max_left d e) (le_max_left BJ BK) n s x v) hC)
  have hK := (ha i x hx ((hp (le_max_right BJ BK) x).trans hlow) v).trans
    (mul_le_mul_of_nonneg_left
      (tameJetSize_mono hp (le_max_right d e) (le_max_right BJ BK) n s x v) hA)
  change q s ((J i).D n x v) + r s ((K i).D n x v) ≤ _
  exact (add_le_add hJ hK).trans_eq (add_mul C A _).symm

theorem N04FixedBaseSmoothFamilyOn.add
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f g : I → E → F} (hf : N04FixedBaseSmoothFamilyOn p q U f)
    (hp : Monotone p) (hg : N04FixedBaseSmoothFamilyOn p q U g) :
    N04FixedBaseSmoothFamilyOn p q U (fun i x => f i x + g i x) := by
  let L : (F × F) →L[ℝ] F := ContinuousLinearMap.fst ℝ F F + ContinuousLinearMap.snd ℝ F F
  exact (hf.prodMk hp hg).postContinuousLinear (fun _ => L) 0
    (fun s => ⟨1, zero_le_one, fun _ y => by
      simpa only [L, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', pairGrading_apply, Nat.add_zero, one_mul]
        using map_add_le_add (q s) y.1 y.2⟩)

theorem N04FixedBaseSmoothFamilyOn.neg
    [ContinuousNeg F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f : I → E → F} (hf : N04FixedBaseSmoothFamilyOn p q U f) :
    N04FixedBaseSmoothFamilyOn p q U (fun i x => -f i x) := by
  let L : F →L[ℝ] F := { toLinearMap := -LinearMap.id, cont := continuous_neg }
  exact hf.postContinuousLinear (fun _ => L) 0
    (fun s => ⟨1, zero_le_one, fun _ y => by
      change q s (-y) ≤ 1 * q (s + 0) y
      simp only [map_neg_eq_map, Nat.add_zero, one_mul, le_refl]⟩)

theorem N04FixedBaseSmoothFamilyOn.sub
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f g : I → E → F} (hf : N04FixedBaseSmoothFamilyOn p q U f)
    (hp : Monotone p) (hg : N04FixedBaseSmoothFamilyOn p q U g) :
    N04FixedBaseSmoothFamilyOn p q U (fun i x => f i x - g i x) :=
  (hf.add hp hg.neg).congr (fun _ _ _ => (sub_eq_add_neg _ _).symm)

theorem n04FixedBaseSmoothFamilyOn_linear
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    (hU : IsOpen U) (L : I → E →L[ℝ] F) (loss : ℕ)
    (hL : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, q s (L i x) ≤ C * p (s + loss) x) :
    N04FixedBaseSmoothFamilyOn p q U (fun i x => L i x) := by
  refine ⟨fun i => smoothDirectionsOfJets hU (continuousLinearJets (L i))
    (hasProjectiveJetsOn_continuousLinear (L i) U), 0, fun n =>
      ⟨loss, fun R _hR s => ?_⟩⟩
  obtain ⟨C, hC, hc⟩ := hL s
  refine ⟨C, hC, fun i x _hx _hlow v => ?_⟩
  change q s (continuousLinearJets (L i) n x v) ≤ C * tameJetSize p n s loss 0 x v
  cases n with
  | zero =>
      rw [tameJetSize_zero]
      exact (hc i x).trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left zero_le_one) hC)
  | succ n =>
      cases n with
      | zero =>
          rw [tameJetSize_one]
          exact (hc i (v 0)).trans (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left (by positivity)) hC)
      | succ n =>
          change q s 0 ≤ _
          rw [map_zero]
          exact mul_nonneg hC (tameJetSize_nonneg _ _ _ _ _ _ _)

section Composition

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {Y : ℕ → Type*} [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
  [∀ n, CompleteSpace (Y n)] {bond : ∀ n, Y (n + 1) →L[ℝ] Y n}
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {r : ℕ → Seminorm ℝ (ProjectiveLimit Y bond)}
  {U : Set E} {V : Set F} {f : I → E → F} {g : I → F → ProjectiveLimit Y bond}

theorem N04FixedBaseSmoothFamilyOn.comp
    (hg : N04FixedBaseSmoothFamilyOn q r V g) (hp : Monotone p)
    (hIp : HasInterpolation (pairGrading realGrading p))
    (hf : N04FixedBaseSmoothFamilyOn p q U f)
    (hU : IsOpen U) (hV : IsOpen V) (hmap : ∀ i, MapsTo (f i) U V) :
    N04FixedBaseSmoothFamilyOn p r U (fun i x => g i (f i x)) := by
  obtain ⟨J, BJ, hbJ⟩ := hf
  obtain ⟨K, BK, hbK⟩ := hg
  let A : ∀ i, SmoothDirections U (fun x => g i (f i x)) := fun i =>
    smoothDirectionsOfJets hU (projectiveCompositionJets (f i) (J i).D (K i).D)
      (HasProjectiveJetsOn.comp_topological hU hV (J i).hasProjectiveJetsOn
        (K i).hasProjectiveJetsOn (hmap i))
  let d : ℕ → ℕ := fun n => (hbJ n).choose
  let e : ℕ → ℕ := fun n => (hbK n).choose
  let data := projectiveCompositionJets_fixedBase_oneHigh p q r hp hIp J K BJ BK d e
    (fun n => (hbJ n).choose_spec) (fun n => (hbK n).choose_spec) hmap
  exact ⟨A, data.choose, data.choose_spec.2⟩

end Composition

end ContinuousFlexibility.Analysis
