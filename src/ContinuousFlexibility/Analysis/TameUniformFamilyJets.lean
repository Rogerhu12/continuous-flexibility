import ContinuousFlexibility.Analysis.TameUniformFamilyGrowth
import ContinuousFlexibility.Analysis.TameTopologicalComposition
import ContinuousFlexibility.Analysis.TameProductDirections
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine
import ContinuousFlexibility.Analysis.TameTransfer

/-!
# Uniform estimates for genuine indexed directional towers

All jets below belong to the specified `SmoothDirections` towers. Their
finite partition formula gives uniform bounds for composition. Products,
linear operators and equality on the open domain preserve the same
quantifier order, so an external radius selector never enters a chosen
loss or numerical constant.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {I E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]

def UniformFamilyJetBounds
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    {U : Set E} {f : I → E → F} (J : ∀ i, SmoothDirections U (f i)) : Prop :=
  ∀ n, HasUniformFamilyLowGrowthOn (jetGrading p n) q (U ×ˢ univ)
    (fun i z => (J i).D n z.1 z.2)

theorem UniformFamilyJetBounds.oneHigh
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} {f : I → E → F} {J : ∀ i, SmoothDirections U (f i)}
    (hJ : UniformFamilyJetBounds p q J) (n : ℕ) :
    ∃ base loss : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i x, x ∈ U → p base x ≤ R → ∀ v : Fin n → E,
        q s ((J i).D n x v) ≤ C * tameJetSize p n s loss base x v :=
  uniformFamilyLowGrowthOn_multilinear_oneHigh (fun i => (J i).D n) (hJ n)

theorem UniformFamilyJetBounds.reindex
    {K : Type*} {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} {f : I → E → F} {J : ∀ i, SmoothDirections U (f i)}
    (hJ : UniformFamilyJetBounds p q J) (a : K → I) :
    UniformFamilyJetBounds p q (fun k => J (a k)) :=
  fun n => (hJ n).reindex a

theorem UniformFamilyJetBounds.restrict
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U V : Set E} {f : I → E → F} {J : ∀ i, SmoothDirections U (f i)}
    (hJ : UniformFamilyJetBounds p q J) (hV : IsOpen V) (hVU : V ⊆ U) :
    UniformFamilyJetBounds p q (fun i => smoothDirectionsRestrict (J i) hV hVU) :=
  fun n => (hJ n).mono (fun _ hz => ⟨hVU hz.1, hz.2⟩)

theorem UniformFamilyJetBounds.congr
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
    {f g : I → E → F} {J : ∀ i, SmoothDirections U (f i)}
    (hJ : UniformFamilyJetBounds p q J) (K : ∀ i, SmoothDirections U (g i))
    (heq : ∀ i x, x ∈ U → f i x = g i x) :
    UniformFamilyJetBounds p q K := by
  intro n
  apply (hJ n).congr
  intro i z hz
  exact congrArg (fun A => A z.2)
    ((K i).unique ((J i).congr (heq i)) n z.1 hz.1)

theorem UniformFamilyJetBounds.value
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} {f : I → E → F} {J : ∀ i, SmoothDirections U (f i)}
    (hp : Monotone p) (hJ : UniformFamilyJetBounds p q J) :
    HasUniformFamilyLowGrowthOn p q U f := by
  have hzero : HasUniformFamilyLowGrowthOn p (jetGrading p 0) U
      (fun (_ : I) x => (x, (Fin.elim0 : Fin 0 → E))) := by
    apply uniformFamilyLowGrowthOn_of_contraction
    intro s i x hx
    simp only [jetGrading_apply, Finset.univ_eq_empty, Finset.sum_empty, add_zero, le_refl]
  have h := (hJ 0).comp hp hzero (fun _ _ hx => ⟨hx, mem_univ _⟩)
  exact h.congr (fun i x hx => ((J i).zero x hx).symm)

/-- Postcomposition retains the actual quotient-limit identities. -/
def smoothDirectionsPostContinuousLinear
    {U : Set E} {f : E → F} (J : SmoothDirections U f) (L : F →L[ℝ] G) :
    SmoothDirections U (fun x => L (f x)) where
  open_domain := J.open_domain
  D n x := L.compContinuousMultilinearMap (J.D n x)
  zero x hx := congrArg L (J.zero x hx)
  continuous n := L.continuous.comp_continuousOn (J.continuous n)
  derivative n x hx v w := (J.derivative n x hx v w).clm_comp L

theorem UniformFamilyJetBounds.postContinuousLinear
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : I → E → F} {J : ∀ i, SmoothDirections U (f i)}
    (hp : Monotone p) (hJ : UniformFamilyJetBounds p q J)
    (L : I → F →L[ℝ] G) (loss : ℕ)
    (hL : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ i y, r s (L i y) ≤ C * q (s + loss) y) :
    UniformFamilyJetBounds p r (fun i => smoothDirectionsPostContinuousLinear (J i) (L i)) := by
  have hlin : HasUniformFamilyLowGrowthOn q r univ (fun i y => L i y) :=
    uniformFamilyLowGrowthOn_of_bound q r univ (fun i y => L i y) loss
      (fun s => by
        obtain ⟨C, hC, hc⟩ := hL s
        exact ⟨C, hC, fun i y _ => hc i y⟩)
  exact fun n => hlin.comp (jetGrading_monotone hp n) (hJ n) (fun _ _ _ => mem_univ _)

theorem UniformFamilyJetBounds.prodMk
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    {U : Set E} {f : I → E → F} {g : I → E → G}
    {J : ∀ i, SmoothDirections U (f i)} {K : ∀ i, SmoothDirections U (g i)}
    (hp : Monotone p) (hJ : UniformFamilyJetBounds p q J)
    (hK : UniformFamilyJetBounds p r K) :
    UniformFamilyJetBounds p (pairGrading q r)
      (fun i => smoothDirectionsProd (J i) (K i)) :=
  fun n => (hJ n).prodMk (jetGrading_monotone hp n) (hK n)

theorem UniformFamilyJetBounds.add
    [IsTopologicalAddGroup F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} {f g : I → E → F}
    {J : ∀ i, SmoothDirections U (f i)} {K : ∀ i, SmoothDirections U (g i)}
    (hp : Monotone p) (hJ : UniformFamilyJetBounds p q J)
    (hK : UniformFamilyJetBounds p q K) :
    UniformFamilyJetBounds p q (fun i => smoothDirectionsAdd (J i) (K i)) :=
  fun n => (hJ n).add (jetGrading_monotone hp n) (hK n)

theorem uniformFamilyJetBounds_linear
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} (hU : IsOpen U) (hp : Monotone p)
    (L : I → E →L[ℝ] F) (loss : ℕ)
    (hL : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, q s (L i x) ≤ C * p (s + loss) x) :
    UniformFamilyJetBounds p q (fun i => smoothDirectionsOfJets hU
      (continuousLinearJets (L i)) (hasProjectiveJetsOn_continuousLinear (L i) U)) := by
  have hlin : HasUniformFamilyLowGrowthOn p q univ (fun i x => L i x) :=
    uniformFamilyLowGrowthOn_of_bound p q univ (fun i x => L i x) loss
      (fun s => by
        obtain ⟨C, hC, hc⟩ := hL s
        exact ⟨C, hC, fun i x _ => hc i x⟩)
  intro n
  cases n with
  | zero => exact hlin.comp (jetGrading_monotone hp 0)
      ((uniformLowGrowth_jet_base p 0).uniformFamilyOn (U ×ˢ univ))
      (fun _ _ _ => mem_univ _)
  | succ n =>
      cases n with
      | zero => exact hlin.comp (jetGrading_monotone hp 1)
          ((uniformLowGrowth_jet_direction p 1 0).uniformFamilyOn (U ×ˢ univ))
          (fun _ _ _ => mem_univ _)
      | succ n => exact (uniformLowGrowth_const (jetGrading p (n + 2)) q (0 : F)).uniformFamilyOn
          (U ×ˢ univ)

theorem uniformFamilyJetBounds_quadratic
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} (hU : IsOpen U) (hp : Monotone p)
    (B : I → E [×2]→L[ℝ] F)
    (hB : HasUniformFamilyLowGrowthOn (pairGrading p p) q univ
      (fun i z => bilinearJetValue (B i) z.1 z.2)) :
    UniformFamilyJetBounds p q (fun i => smoothDirectionsOfJets hU
      (quadraticJets (B i)) (hasProjectiveJetsOn_quadratic (B i) U)) := by
  intro n
  have hb := (uniformLowGrowth_jet_base p n).uniformFamilyOn (I := I) (U ×ˢ univ)
  have hd (j : Fin n) := (uniformLowGrowth_jet_direction p n j).uniformFamilyOn
    (I := I) (U ×ˢ univ)
  have hp' := jetGrading_monotone hp n
  cases n with
  | zero => exact hB.comp hp' (hb.prodMk hp' hb) (fun _ _ _ => mem_univ _)
  | succ n =>
      cases n with
      | zero =>
          have h₁ := hB.comp hp' ((hd 0).prodMk hp' hb) (fun _ _ _ => mem_univ _)
          have h₂ := hB.comp hp' (hb.prodMk hp' (hd 0)) (fun _ _ _ => mem_univ _)
          apply (h₁.add hp' h₂).congr
          intro i z hz
          exact quadraticJetFirst_apply (B i) z.1 (z.2 0)
      | succ n =>
          cases n with
          | zero =>
              have h₁ := hB.comp hp' ((hd 0).prodMk hp' (hd 1)) (fun _ _ _ => mem_univ _)
              have h₂ := hB.comp hp' ((hd 1).prodMk hp' (hd 0)) (fun _ _ _ => mem_univ _)
              apply (h₁.add hp' h₂).congr
              intro i z hz
              exact quadraticJetSecond_apply (B i) z.2
          | succ n => exact (uniformLowGrowth_const (jetGrading p (n + 3)) q (0 : F)).uniformFamilyOn
              (U ×ˢ univ)

section Composition

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
  {U : Set E} {V : Set F} {f : I → E → F} {g : I → F → G}
  {J : ∀ i, SmoothDirections U (f i)} {K : ∀ i, SmoothDirections V (g i)}

theorem uniformFamilyLowGrowthOn_compositionTerm
    (hp : Monotone p) (hJ : UniformFamilyJetBounds p q J)
    (hK : UniformFamilyJetBounds q r K) (hmap : ∀ i, MapsTo (f i) U V)
    {n : ℕ} (c : OrderedFinpartition n) :
    HasUniformFamilyLowGrowthOn (jetGrading p n) r (U ×ˢ univ)
      (fun i z => projectiveCompositionTerm (f i) (J i).D (K i).D c z.1 z.2) := by
  have hp' := jetGrading_monotone hp n
  have hbase : HasUniformFamilyLowGrowthOn (jetGrading p n) q (U ×ˢ univ)
      (fun i z => f i z.1) :=
    (hJ.value hp).comp hp' ((uniformLowGrowth_jet_base p n).uniformFamilyOn (U ×ˢ univ))
      (fun _ _ hz => hz.1)
  have hblock (j : Fin c.length) :
      HasUniformFamilyLowGrowthOn (jetGrading p n) q (U ×ˢ univ)
        (fun i z => (J i).D (c.partSize j) z.1 (z.2 ∘ c.emb j)) := by
    have hs := (uniformLowGrowth_of_zeroLoss (tameJetSelection (c.emb j))
      (tameJetSelection_isTameLinear p (c.emb j))).uniformFamilyOn (I := I) (U ×ˢ univ)
    simpa only [tameJetSelection_apply] using
      (hJ (c.partSize j)).comp hp' hs (fun _ _ hz => ⟨hz.1, mem_univ _⟩)
  exact (hK c.length).comp hp'
    (hbase.prodMk hp' (HasUniformFamilyLowGrowthOn.pi hp' hblock))
    (fun i _ hz => ⟨hmap i hz.1, mem_univ _⟩)

theorem uniformFamilyLowGrowthOn_compositionJets
    (hp : Monotone p) (hJ : UniformFamilyJetBounds p q J)
    (hK : UniformFamilyJetBounds q r K) (hmap : ∀ i, MapsTo (f i) U V) (n : ℕ) :
    HasUniformFamilyLowGrowthOn (jetGrading p n) r (U ×ˢ univ)
      (fun i z => projectiveCompositionJets (f i) (J i).D (K i).D n z.1 z.2) := by
  classical
  simp only [projectiveCompositionJets_apply]
  exact HasUniformFamilyLowGrowthOn.finset_sum (jetGrading_monotone hp n) Finset.univ
    (fun c _ => uniformFamilyLowGrowthOn_compositionTerm hp hJ hK hmap c)

end Composition

section ActualComposition

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {Y : ℕ → Type*} [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
  [∀ n, CompleteSpace (Y n)] {bond : ∀ n, Y (n + 1) →L[ℝ] Y n}
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {r : ℕ → Seminorm ℝ (ProjectiveLimit Y bond)}
  {U : Set E} {V : Set F} {f : I → E → F} {g : I → F → ProjectiveLimit Y bond}
  {J : ∀ i, SmoothDirections U (f i)} {K : ∀ i, SmoothDirections V (g i)}

theorem UniformFamilyJetBounds.comp
    (hp : Monotone p) (hU : IsOpen U) (hV : IsOpen V)
    (hJ : UniformFamilyJetBounds p q J) (hK : UniformFamilyJetBounds q r K)
    (hmap : ∀ i, MapsTo (f i) U V) :
    UniformFamilyJetBounds p r (fun i => smoothDirectionsOfJets hU
      (projectiveCompositionJets (f i) (J i).D (K i).D)
      (HasProjectiveJetsOn.comp_topological hU hV (J i).hasProjectiveJetsOn
        (K i).hasProjectiveJetsOn (hmap i))) :=
  fun n => uniformFamilyLowGrowthOn_compositionJets hp hJ hK hmap n

theorem UniformFamilyJetBounds.comp_of_eq
    {h : I → E → ProjectiveLimit Y bond}
    (hp : Monotone p) (hU : IsOpen U) (hV : IsOpen V)
    (hJ : UniformFamilyJetBounds p q J) (hK : UniformFamilyJetBounds q r K)
    (hmap : ∀ i, MapsTo (f i) U V) (H : ∀ i, SmoothDirections U (h i))
    (heq : ∀ i x, x ∈ U → g i (f i x) = h i x) :
    UniformFamilyJetBounds p r H :=
  (hJ.comp hp hU hV hK hmap).congr H heq

end ActualComposition

end ContinuousFlexibility.Analysis
