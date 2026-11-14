module

public import ContinuousFlexibility.Analysis.TameUniformFamilyJets

/-!
# Finite assembly of uniformly estimated genuine families

This proposition records an actual directional tower and the numerical
family bounds proved in the preceding module. The closure lemmas retain
the concrete maps and their genuine jets; no estimate is inferred from
an abstract smooth-tame assertion.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {I E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]

def UniformSmoothFamilyOn
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (U : Set E) (f : I → E → F) : Prop :=
  ∃ J : ∀ i, SmoothDirections U (f i), UniformFamilyJetBounds p q J

theorem UniformSmoothFamilyOn.congr
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f g : I → E → F} (hf : UniformSmoothFamilyOn p q U f)
    (heq : ∀ i x, x ∈ U → f i x = g i x) : UniformSmoothFamilyOn p q U g := by
  obtain ⟨J, hJ⟩ := hf
  exact ⟨fun i => (J i).congr (heq i), hJ⟩

theorem UniformSmoothFamilyOn.reindex
    {K : Type*} {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f : I → E → F} (hf : UniformSmoothFamilyOn p q U f) (a : K → I) :
    UniformSmoothFamilyOn p q U (fun k => f (a k)) := by
  obtain ⟨J, hJ⟩ := hf
  exact ⟨fun k => J (a k), hJ.reindex a⟩

theorem UniformSmoothFamilyOn.restrict
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U V : Set E}
    {f : I → E → F} (hf : UniformSmoothFamilyOn p q U f) (hV : IsOpen V) (hVU : V ⊆ U) :
    UniformSmoothFamilyOn p q V f := by
  obtain ⟨J, hJ⟩ := hf
  exact ⟨fun i => smoothDirectionsRestrict (J i) hV hVU, hJ.restrict hV hVU⟩

theorem UniformSmoothFamilyOn.jets
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f : I → E → F} (hf : UniformSmoothFamilyOn p q U f)
    (J : ∀ i, SmoothDirections U (f i)) : UniformFamilyJetBounds p q J := by
  obtain ⟨K, hK⟩ := hf
  exact hK.congr J (fun _ _ _ => rfl)

theorem UniformSmoothFamilyOn.postContinuousLinear
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : I → E → F} (hf : UniformSmoothFamilyOn p q U f)
    (hp : Monotone p) (L : I → F →L[ℝ] G) (loss : ℕ)
    (hL : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ i y, r s (L i y) ≤ C * q (s + loss) y) :
    UniformSmoothFamilyOn p r U (fun i x => L i (f i x)) := by
  obtain ⟨J, hJ⟩ := hf
  exact ⟨fun i => smoothDirectionsPostContinuousLinear (J i) (L i),
    hJ.postContinuousLinear hp L loss hL⟩

theorem UniformSmoothFamilyOn.postTameContinuousLinear
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : I → E → F} (hf : UniformSmoothFamilyOn p q U f)
    (hp : Monotone p) (L : F →L[ℝ] G) {loss : ℕ}
    (hL : IsTameLinear q r L.toLinearMap loss 0) :
    UniformSmoothFamilyOn p r U (fun i x => L (f i x)) := by
  apply hf.postContinuousLinear hp (fun _ => L) loss
  intro s
  obtain ⟨C, hc⟩ := hL s (Nat.zero_le s)
  exact ⟨C, C.coe_nonneg, fun _ y => hc y⟩

theorem UniformSmoothFamilyOn.add
    [IsTopologicalAddGroup F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f g : I → E → F} (hf : UniformSmoothFamilyOn p q U f)
    (hp : Monotone p) (hg : UniformSmoothFamilyOn p q U g) :
    UniformSmoothFamilyOn p q U (fun i x => f i x + g i x) := by
  obtain ⟨J, hJ⟩ := hf
  obtain ⟨K, hK⟩ := hg
  exact ⟨fun i => smoothDirectionsAdd (J i) (K i), hJ.add hp hK⟩

theorem UniformSmoothFamilyOn.neg
    [ContinuousNeg F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f : I → E → F} (hf : UniformSmoothFamilyOn p q U f) (hp : Monotone p) :
    UniformSmoothFamilyOn p q U (fun i x => -f i x) := by
  let L : F →L[ℝ] F :=
    { toLinearMap := -LinearMap.id
      cont := continuous_neg }
  exact hf.postContinuousLinear hp (fun _ => L) 0
    (fun s => ⟨1, zero_le_one, fun i y => by
      change q s (-y) ≤ 1 * q (s + 0) y
      simp only [map_neg_eq_map, Nat.add_zero, one_mul, le_refl]⟩)

theorem UniformSmoothFamilyOn.sub
    [IsTopologicalAddGroup F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f g : I → E → F} (hf : UniformSmoothFamilyOn p q U f)
    (hp : Monotone p) (hg : UniformSmoothFamilyOn p q U g) :
    UniformSmoothFamilyOn p q U (fun i x => f i x - g i x) :=
  (hf.add hp (hg.neg hp)).congr (fun _ _ _ => (sub_eq_add_neg _ _).symm)

theorem UniformSmoothFamilyOn.prodMk
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : I → E → F} {g : I → E → G}
    (hf : UniformSmoothFamilyOn p q U f) (hp : Monotone p)
    (hg : UniformSmoothFamilyOn p r U g) :
    UniformSmoothFamilyOn p (pairGrading q r) U (fun i x => (f i x, g i x)) := by
  obtain ⟨J, hJ⟩ := hf
  obtain ⟨K, hK⟩ := hg
  exact ⟨fun i => smoothDirectionsProd (J i) (K i), hJ.prodMk hp hK⟩

theorem uniformSmoothFamilyOn_linear
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    (hU : IsOpen U) (hp : Monotone p) (L : I → E →L[ℝ] F) (loss : ℕ)
    (hL : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, q s (L i x) ≤ C * p (s + loss) x) :
    UniformSmoothFamilyOn p q U (fun i x => L i x) :=
  ⟨fun i => smoothDirectionsOfJets hU (continuousLinearJets (L i))
    (hasProjectiveJetsOn_continuousLinear (L i) U),
      uniformFamilyJetBounds_linear hU hp L loss hL⟩

theorem UniformSmoothFamilyOn.precompLinearFamily
    [IsTopologicalAddGroup F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set F} {V : Set E} {f : I → F → G}
    (hf : UniformSmoothFamilyOn q r U f) (hp : Monotone p) (hV : IsOpen V)
    (L : I → E →L[ℝ] F) (loss : ℕ)
    (hL : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, q s (L i x) ≤ C * p (s + loss) x)
    (hmap : ∀ i, MapsTo (L i) V U) :
    UniformSmoothFamilyOn p r V (fun i x => f i (L i x)) := by
  obtain ⟨J, hJ⟩ := hf
  let K := fun i => (J i).compAffine (L i) 0 hV
    (by simpa only [zero_add] using hmap i)
  have hK : UniformFamilyJetBounds p r K := by
    intro n
    have hselect : HasUniformFamilyLowGrowthOn (jetGrading p n) (jetGrading q n)
        (V ×ˢ univ) (fun i z => (L i z.1, fun j => L i (z.2 j))) := by
      apply uniformFamilyLowGrowthOn_of_bound _ _ _ _ loss
      intro s
      obtain ⟨C, hC, hc⟩ := hL s
      refine ⟨C, hC, fun i z _ => ?_⟩
      rw [jetGrading_apply, jetGrading_apply, mul_add, Finset.mul_sum]
      exact add_le_add (hc i z.1) (Finset.sum_le_sum (fun j _ => hc i (z.2 j)))
    have hcomp := (hJ n).comp (jetGrading_monotone hp n) hselect
      (fun i _ hz => ⟨hmap i hz.1, mem_univ _⟩)
    apply hcomp.congr
    intro i z hz
    change (J i).D n (0 + L i z.1) (fun j => L i (z.2 j)) = _
    rw [zero_add]
  exact (show UniformSmoothFamilyOn p r V (fun i x => f i (0 + L i x)) from ⟨K, hK⟩).congr
    (fun i x _ => congrArg (f i) (zero_add (L i x)))

theorem UniformSmoothFamilyOn.fst
    [IsTopologicalAddGroup E]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : I → E → F} (hf : UniformSmoothFamilyOn p q U f)
    (hp : Monotone p) (hr : Monotone r) (hU : IsOpen U) :
    UniformSmoothFamilyOn (pairGrading p r) q (U ×ˢ univ) (fun i x => f i x.1) := by
  apply hf.precompLinearFamily (tamePairGrading_monotone hp hr) (hU.prod isOpen_univ)
    (fun _ : I => ContinuousLinearMap.fst ℝ E G) 0
  · intro s
    exact ⟨1, zero_le_one, fun i x => by
      change p s x.1 ≤ 1 * (p (s + 0) x.1 + r (s + 0) x.2)
      simp only [Nat.add_zero, one_mul]
      exact le_add_of_nonneg_right (apply_nonneg _ _)⟩
  · exact fun _ _ hx => hx.1

section Composition

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {Y : ℕ → Type*} [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
  [∀ n, CompleteSpace (Y n)] {bond : ∀ n, Y (n + 1) →L[ℝ] Y n}
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {r : ℕ → Seminorm ℝ (ProjectiveLimit Y bond)}
  {U : Set E} {V : Set F} {f : I → E → F} {g : I → F → ProjectiveLimit Y bond}

theorem UniformSmoothFamilyOn.comp
    (hg : UniformSmoothFamilyOn q r V g) (hp : Monotone p)
    (hf : UniformSmoothFamilyOn p q U f) (hU : IsOpen U) (hV : IsOpen V)
    (hmap : ∀ i, MapsTo (f i) U V) :
    UniformSmoothFamilyOn p r U (fun i x => g i (f i x)) := by
  obtain ⟨J, hJ⟩ := hf
  obtain ⟨K, hK⟩ := hg
  exact ⟨fun i => smoothDirectionsOfJets hU
      (projectiveCompositionJets (f i) (J i).D (K i).D)
      (HasProjectiveJetsOn.comp_topological hU hV (J i).hasProjectiveJetsOn
        (K i).hasProjectiveJetsOn (hmap i)), hJ.comp hp hU hV hK hmap⟩

end Composition

end ContinuousFlexibility.Analysis
