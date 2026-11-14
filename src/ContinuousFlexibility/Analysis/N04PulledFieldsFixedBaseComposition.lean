import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBaseFamily

/-!
# Composition without moving the common low base past the parameter order

Contracting linear pullbacks retain the given base and losses. General
composition uses the existing finite-partition theorem, whose interpolation
base is chosen once before all parameter orders. Every output tower is the
genuine chain-rule tower of the specified maps.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

private theorem n04PulledFields_tameJetSize_map_le
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (L : E →ₗ[ℝ] F)
    (hL : ∀ s x, q s (L x) ≤ p s x)
    (n s loss base : ℕ) (x : E) (v : Fin n → E) :
    tameJetSize q n s loss base (L x) (fun i => L (v i)) ≤
      tameJetSize p n s loss base x v := by
  unfold tameJetSize
  apply add_le_add
  · exact mul_le_mul (add_le_add le_rfl (hL _ _))
      (Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _) (fun _ _ => hL _ _))
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) (by positivity)
  · apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul (hL _ _)
      (Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _) (fun _ _ => hL _ _))
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) (apply_nonneg _ _)

theorem N04PulledFieldsFixedBaseFamily.precompContracting
    {I E F G : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [IsTopologicalAddGroup F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set F} {V : Set E} {f : I → F → G}
    (hf : N04PulledFieldsFixedBaseFamily q r U f) (hV : IsOpen V)
    (L : I → E →L[ℝ] F) (hL : ∀ i s x, q s (L i x) ≤ p s x)
    (hmap : ∀ i, MapsTo (L i) V U) :
    N04PulledFieldsFixedBaseFamily p r V (fun i x => f i (L i x)) := by
  obtain ⟨J, B, d, h⟩ := hf
  have hmap' (i : I) : MapsTo (fun x => (0 : F) + L i x) V U := by
    simpa only [zero_add] using hmap i
  refine ⟨fun i => ((J i).compAffine (L i) 0 hV (hmap' i)).congrOn
    (fun x _ => congrArg (f i) (zero_add (L i x))), B, d, fun n R hR s => ?_⟩
  let data := h n R hR s
  refine ⟨data.choose, data.choose_spec.1, fun i x hx hbx v => ?_⟩
  change r s ((J i).D n (0 + L i x) (fun j => L i (v j))) ≤ _
  rw [zero_add]
  exact (data.choose_spec.2 i (L i x) (hmap i hx) ((hL i B x).trans hbx)
    (fun j => L i (v j))).trans
      (mul_le_mul_of_nonneg_left
        (n04PulledFields_tameJetSize_map_le p q (L i).toLinearMap (hL i) n s (d n) B x v)
        data.choose_spec.1)

theorem N04PulledFieldsFixedBaseFamily.fst
    {I E F G : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : I → E → F} (hf : N04PulledFieldsFixedBaseFamily p q U f)
    (hU : IsOpen U) :
    N04PulledFieldsFixedBaseFamily (pairGrading p r) q (U ×ˢ univ)
      (fun i x => f i x.1) := by
  apply hf.precompContracting (hU.prod isOpen_univ)
    (fun _ : I => ContinuousLinearMap.fst ℝ E G)
  · intro i s x
    change p s x.1 ≤ pairGrading p r s x
    rw [pairGrading_apply]
    exact le_add_of_nonneg_right (apply_nonneg _ _)
  · exact fun _ _ hx => hx.1

/-- The finite-partition composition theorem chooses one input base
before every parameter order. It never replaces that base by a prefix
maximum over derivative orders. -/
theorem N04PulledFieldsFixedBaseFamily.comp
    {I E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    {Y : ℕ → Type*} [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
    [∀ n, CompleteSpace (Y n)] {bond : ∀ n, Y (n + 1) →L[ℝ] Y n}
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {r : ℕ → Seminorm ℝ (ProjectiveLimit Y bond)}
    {U : Set E} {V : Set F} {f : I → E → F} {g : I → F → ProjectiveLimit Y bond}
    (hg : N04PulledFieldsFixedBaseFamily q r V g)
    (hp : Monotone p) (hI : HasInterpolation (pairGrading realGrading p))
    (hf : N04PulledFieldsFixedBaseFamily p q U f) (hU : IsOpen U) (hV : IsOpen V)
    (hmap : ∀ i, MapsTo (f i) U V) :
    N04PulledFieldsFixedBaseFamily p r U (fun i x => g i (f i x)) := by
  obtain ⟨J, BJ, d, hJ⟩ := hf
  obtain ⟨K, BK, e, hK⟩ := hg
  let data := projectiveCompositionJets_fixedBase_oneHigh p q r hp hI
    J K BJ BK d e hJ hK hmap
  refine ⟨fun i => smoothDirectionsOfJets hU
    (projectiveCompositionJets (f i) (J i).D (K i).D)
    (HasProjectiveJetsOn.comp_topological hU hV (J i).hasProjectiveJetsOn
      (K i).hasProjectiveJetsOn (hmap i)),
    data.choose, fun n => (data.choose_spec.2 n).choose, fun n R hR s => ?_⟩
  exact (data.choose_spec.2 n).choose_spec R hR s

end ContinuousFlexibility.Analysis
