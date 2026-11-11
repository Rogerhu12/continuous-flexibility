import ContinuousFlexibility.Analysis.TameJetComposition
import ContinuousFlexibility.Analysis.TameJetLocalBounds
import ContinuousFlexibility.Analysis.TameLocalLinear

/-!
# Smooth tame composition on projective limits

Each ordered-partition summand is a composition of jointly locally tame
jet evaluations and linear coordinate selections. Finite sums preserve
these local bounds. Multilinear normalization then recovers the exact
homogeneous estimate required by `SmoothTameOn` for the genuine jet tower.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open scoped Topology BigOperators NNReal
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

section CoordinateSelections

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-- Keep the base point and select a finite list of its increments. -/
def tameJetSelection {m n : ℕ} (a : Fin m → Fin n) :
    (E × (Fin n → E)) →L[ℝ] E × (Fin m → E) :=
  (ContinuousLinearMap.fst ℝ E (Fin n → E)).prod
    ((ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (a i))).comp
      (ContinuousLinearMap.snd ℝ E (Fin n → E)))

@[simp] theorem tameJetSelection_apply {m n : ℕ} (a : Fin m → Fin n)
    (z : E × (Fin n → E)) : tameJetSelection a z = (z.1, z.2 ∘ a) := by
  ext <;> simp [tameJetSelection, Function.comp_def]

theorem tameJetSelection_isTameLinear (p : ℕ → Seminorm ℝ E)
    {m n : ℕ} (a : Fin m → Fin n) :
    IsTameLinear (jetGrading p n) (jetGrading p m)
      (tameJetSelection a).toLinearMap 0 0 := by
  intro s _
  refine ⟨(m : ℝ≥0) + 1, fun z => ?_⟩
  simp only [Nat.add_zero, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one,
    ContinuousLinearMap.coe_coe, tameJetSelection_apply, jetGrading_apply,
    Function.comp_apply]
  have hsum : ∑ i : Fin m, p s (z.2 (a i)) ≤ (m : ℝ) * ∑ j : Fin n, p s (z.2 j) := by
    calc
      _ ≤ ∑ _i : Fin m, ∑ j : Fin n, p s (z.2 j) :=
        Finset.sum_le_sum (fun i _ => Finset.single_le_sum
          (fun j _ => apply_nonneg _ _) (Finset.mem_univ (a i)))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
  have hx : 0 ≤ p s z.1 := apply_nonneg _ _
  have hv : 0 ≤ ∑ j : Fin n, p s (z.2 j) := Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- The zero-increment inclusion is lossless for the joint grading. -/
theorem tameZeroJet_isTameLinear (p : ℕ → Seminorm ℝ E) :
    IsTameLinear p (jetGrading p 0)
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] (Fin 0 → E))).toLinearMap 0 0 := by
  intro s _
  refine ⟨1, fun x => ?_⟩
  simp [jetGrading_apply]

end CoordinateSelections

section LocalComposition

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]
variable {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
  {U : Set X} {V : Set Y} {u : X → Y} {v : Y → Z}

/-- Order zero of the exact tame jet estimates gives ordinary local growth. -/
theorem locallyTameOn_of_smoothDirections (ht : WithSeminorms p)
    (J : SmoothDirections U u) (hJ : J.TameBounds p q) :
    LocallyTameOn p q U u := by
  have hz := (locallyTameOn_jetEvaluation ht J hJ 0).comp
    (locallyTameOn_of_isTameLinear
      ((ContinuousLinearMap.id ℝ X).prod (0 : X →L[ℝ] (Fin 0 → X)))
      (tameZeroJet_isTameLinear p) U)
    (fun x hx => ⟨hx, mem_univ _⟩)
  apply hz.congr
  intro x hx
  change u x = J.D 0 x (0 : Fin 0 → X)
  rw [show (0 : Fin 0 → X) = Fin.elim0 from Subsingleton.elim _ _]
  exact (J.zero x hx).symm

/-- Each finite partition expression has a fixed-loss local value bound. -/
theorem locallyTameOn_compositionTerm (hp : Monotone p)
    (htp : WithSeminorms p) (htq : WithSeminorms q)
    (J : SmoothDirections U u) (K : SmoothDirections V v)
    (hJ : J.TameBounds p q) (hK : K.TameBounds q r) (hmap : MapsTo u U V)
    {n : ℕ} (c : OrderedFinpartition n) :
    LocallyTameOn (jetGrading p n) r (U ×ˢ univ)
      (fun z : X × (Fin n → X) => projectiveCompositionTerm u J.D K.D c z.1 z.2) := by
  have hp' := jetGrading_monotone hp n
  have hbase : LocallyTameOn (jetGrading p n) q (U ×ˢ univ)
      (fun z : X × (Fin n → X) => u z.1) :=
    (locallyTameOn_of_smoothDirections htp J hJ).comp
      (locallyTameOn_of_isTameLinear (ContinuousLinearMap.fst ℝ X (Fin n → X))
        (inverseTame_fst p (tupleGrading (fun _ : Fin n => p))) (U ×ˢ univ))
      (fun _ hz => hz.1)
  have hblock (i : Fin c.length) : LocallyTameOn (jetGrading p n) q (U ×ˢ univ)
      (fun z : X × (Fin n → X) => J.D (c.partSize i) z.1 (z.2 ∘ c.emb i)) := by
    exact (locallyTameOn_jetEvaluation htp J hJ (c.partSize i)).comp
      (locallyTameOn_of_isTameLinear (tameJetSelection (c.emb i))
        (tameJetSelection_isTameLinear p (c.emb i)) (U ×ˢ univ))
      (fun _ hz => ⟨hz.1, mem_univ _⟩)
  exact (locallyTameOn_jetEvaluation htq K hK c.length).comp
    (hbase.prodMk hp' (LocallyTameOn.pi hp' hblock))
    (fun _ hz => ⟨hmap hz.1, mem_univ _⟩)

/-- The full partition sum has joint local tame growth at every order. -/
theorem locallyTameOn_compositionJets (hp : Monotone p)
    (htp : WithSeminorms p) (htq : WithSeminorms q)
    (J : SmoothDirections U u) (K : SmoothDirections V v)
    (hJ : J.TameBounds p q) (hK : K.TameBounds q r) (hmap : MapsTo u U V) (n : ℕ) :
    LocallyTameOn (jetGrading p n) r (U ×ˢ univ)
      (fun z : X × (Fin n → X) => projectiveCompositionJets u J.D K.D n z.1 z.2) := by
  classical
  simp only [projectiveCompositionJets_apply]
  exact LocallyTameOn.finset_sum (jetGrading_monotone hp n) Finset.univ
    (fun c _ => locallyTameOn_compositionTerm hp htp htq J K hJ hK hmap c)

end LocalComposition

section ProjectiveComposition

variable {E F G : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, NormedAddCommGroup (G n)] [∀ n, NormedSpace ℝ (G n)]
  [∀ n, CompleteSpace (G n)]
variable {e : ∀ n, E (n + 1) →L[ℝ] E n}
  {f : ∀ n, F (n + 1) →L[ℝ] F n} {g : ∀ n, G (n + 1) →L[ℝ] G n}
variable {u : ProjectiveLimit E e → ProjectiveLimit F f}
  {v : ProjectiveLimit F f → ProjectiveLimit G g}
  {U : Set (ProjectiveLimit E e)} {V : Set (ProjectiveLimit F f)}

/-- Smooth tame maps between the actual projective limits compose. -/
theorem smoothTameOn_comp (hU : IsOpen U) (hV : IsOpen V) (hmap : MapsTo u U V)
    (hu : SmoothTameOn (gradedSeminorm E e) (gradedSeminorm F f) U u)
    (hv : SmoothTameOn (gradedSeminorm F f) (gradedSeminorm G g) V v) :
    SmoothTameOn (gradedSeminorm E e) (gradedSeminorm G g) U (v ∘ u) := by
  obtain ⟨J, hJ⟩ := hu
  obtain ⟨K, hK⟩ := hv
  let JK := smoothDirectionsOfJets hU (projectiveCompositionJets u J.D K.D)
    (HasProjectiveJetsOn.comp hU hV J.hasProjectiveJetsOn K.hasProjectiveJetsOn hmap)
  apply smoothTameOn_of_locallyTameOn_jets (gradedSeminorm_monotone E e)
    (withSeminorms_graded E e) JK
  intro k
  exact locallyTameOn_compositionJets (gradedSeminorm_monotone E e)
    (withSeminorms_graded E e) (withSeminorms_graded F f) J K hJ hK hmap k

end ProjectiveComposition

end ContinuousFlexibility.Analysis
