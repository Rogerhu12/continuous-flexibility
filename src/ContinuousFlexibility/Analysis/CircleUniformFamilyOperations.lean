module

public import ContinuousFlexibility.Analysis.CircleTravelUniformJets
public import ContinuousFlexibility.Analysis.CircleAverageCompositionUniformBounds
public import ContinuousFlexibility.Analysis.TameUniformSmoothFamily

/-!
# Uniform genuine families of the actual circle operations

The multiplication, averaged composition, forward composition and
positive inverse are the existing circle-model maps. Their quantitative
jet estimates, including arbitrary selector-dependent travel, assemble
through the actual finite chain rule.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

private theorem operations_constant_family_of_global_oneHigh
    {I E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    {U : Set E} {f : E → F} (J : SmoothDirections U f)
    (hb : ∀ n, ∃ base loss : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, p base x ≤ R → ∀ v : Fin n → E,
        q s (J.D n x v) ≤ C * tameJetSize p n s loss base x v) :
    UniformFamilyJetBounds p q (fun _ : I => J) := by
  intro n
  refine uniformFamilyLowGrowthOn_of_oneHigh (p := p) (q := q) (U := U)
    (fun (_ : I) (x : E) (v : Fin n → E) => J.D n x v) ?_
  obtain ⟨base, loss, hbound⟩ := hb n
  refine ⟨base, loss, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hbound R hR s
  exact ⟨C, hC, fun _ x _ hx v => hc x hx v⟩

private theorem operations_uniform_binary_comp
    {I E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    {Y : ℕ → Type*} [∀ n, NormedAddCommGroup (Y n)] [∀ n, NormedSpace ℝ (Y n)]
    [∀ n, CompleteSpace (Y n)] {bond : ∀ n, Y (n + 1) →L[ℝ] Y n}
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {r : ℕ → Seminorm ℝ (ProjectiveLimit Y bond)}
    {U : Set E} {f g : I → E → F}
    (B : I → F → F → ProjectiveLimit Y bond)
    (hB : UniformSmoothFamilyOn (pairGrading q q) r univ
      (fun i x => B i x.1 x.2))
    (hp : Monotone p) (hU : IsOpen U)
    (hf : UniformSmoothFamilyOn p q U f) (hg : UniformSmoothFamilyOn p q U g) :
    UniformSmoothFamilyOn p r U (fun i x => B i (f i x) (g i x)) := by
  exact hB.comp hp (hf.prodMk hp hg) hU isOpen_univ (fun _ _ _ => mem_univ _)

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : CircleModelData}

theorem uniformSmoothFamilyOn_circleComposition
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation H.grading)
    (travel : I → ℕ → ℝ) :
    UniformSmoothFamilyOn (pairGrading H.grading H.grading) H.grading univ
      (fun i x => circleShiftedChartComposeLinear hH hT hD hγ (travel i) x.1 x.2) := by
  let J := fun i => (smoothTameOn_circleShiftedChartComposeLinear hH hT hD hγ hi (travel i)).choose
  exact ⟨J, circleComposition_uniformFamilyJetBounds hH hT hD hγ hi travel J⟩

theorem uniformSmoothFamilyOn_circleInverseComposition
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation H.grading)
    (travel : I → ℕ → ℝ) (a : ℝ) (ha : 0 < a) :
    UniformSmoothFamilyOn (pairGrading H.grading H.grading) H.grading
      (circleUniformInverseDomain H a ×ˢ univ)
      (fun i x => circlePositiveInverseComposeLinear hH hT hD hγ (travel i) x.1 x.2) := by
  let J := fun i => (smoothTameOn_circlePositiveInverseComposeLinear hH hT hD hγ hi (travel i)).choose
  exact ⟨fun i => smoothDirectionsRestrict (J i)
      ((circleUniformInverseDomain_isOpen H a).prod isOpen_univ)
      (fun _ hx => ⟨circleUniformInverseDomain_subset_positive ha hx.1, hx.2⟩),
    circlePositiveInverse_uniformFamilyJetBounds hH hT hD hγ hi travel J a ha⟩

theorem uniformSmoothFamilyOn_circleAverage
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation H.grading)
    (travel : ℕ → ℝ) :
    UniformSmoothFamilyOn (pairGrading H.grading H.grading) H.grading univ
      (fun (_ : I) x => circleAverageComposeLinear hH hT hD hγ travel x.1 x.2) := by
  let h := exists_circleAverageComposeLinear_uniform_oneHigh hH hT hD hγ hi travel
  let J : SmoothDirections univ (fun x : H.Space × H.Space =>
      circleAverageComposeLinear hH hT hD hγ travel x.1 x.2) := h.choose
  exact ⟨fun _ : I => J,
    operations_constant_family_of_global_oneHigh
      (pairGrading H.grading H.grading) H.grading J h.choose_spec⟩

theorem uniformSmoothFamilyOn_circleProduct
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation H.grading) :
    UniformSmoothFamilyOn (pairGrading H.grading H.grading) H.grading univ
      (fun (_ : I) x => circleProductBilinear hH hT hD hγ x.1 x.2) := by
  let p := pairGrading H.grading H.grading
  have hm := gradedSeminorm_monotone (fun n => H.level n) H.bond
  have hp : Monotone p := tamePairGrading_monotone hm hm
  have hpp := tamePairGrading_monotone hp hp
  let B := circleProductPairMultilinear hH hT hD hγ
  have hleft : HasUniformLowGrowth (pairGrading p p) H.grading
      (fun z : (H.Space × H.Space) × (H.Space × H.Space) => z.1.1) :=
    (uniformLowGrowth_pair_fst H.grading H.grading).comp hpp (uniformLowGrowth_pair_fst p p)
  have hright : HasUniformLowGrowth (pairGrading p p) H.grading
      (fun z : (H.Space × H.Space) × (H.Space × H.Space) => z.2.2) :=
    (uniformLowGrowth_pair_snd H.grading H.grading).comp hpp (uniformLowGrowth_pair_snd p p)
  have hB : HasUniformLowGrowth (pairGrading p p) H.grading
      (fun z : (H.Space × H.Space) × (H.Space × H.Space) => bilinearJetValue B z.1 z.2) := by
    apply ((uniformLowGrowth_circleProduct hH hT hD hγ hi).comp hpp
      (hleft.prodMk hpp hright)).congr
    intro z
    exact circleProductPairMultilinear_apply hH hT hD hγ ![z.1, z.2]
  have hquad : UniformSmoothFamilyOn p H.grading univ
      (fun _ : I => quadraticJetValue B) :=
    ⟨fun _ => smoothDirectionsOfJets isOpen_univ (quadraticJets B)
        (hasProjectiveJetsOn_quadratic B univ),
      uniformFamilyJetBounds_quadratic isOpen_univ hp (fun _ : I => B)
        (hB.uniformFamilyOn univ)⟩
  exact hquad.congr (fun _ x _ => circleProductPairMultilinear_apply hH hT hD hγ ![x, x])

section Maps

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {p : ℕ → Seminorm ℝ E} {U : Set E} {f g : I → E → H.Space}

theorem uniformSmoothFamilyOn_circleCompose_maps
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation H.grading)
    (travel : I → ℕ → ℝ) (hp : Monotone p) (hU : IsOpen U)
    (hf : UniformSmoothFamilyOn p H.grading U f)
    (hg : UniformSmoothFamilyOn p H.grading U g) :
    UniformSmoothFamilyOn p H.grading U
      (fun i x => circleShiftedChartComposeLinear hH hT hD hγ (travel i) (f i x) (g i x)) := by
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  exact operations_uniform_binary_comp
    (Y := fun n => H.level n) (bond := H.bond)
    (p := p) (q := H.grading) (r := H.grading)
    (fun i y z => circleShiftedChartComposeLinear hH hT hD hγ (travel i) y z)
    (uniformSmoothFamilyOn_circleComposition hH hT hD hγ hi travel) hp hU hf hg

theorem uniformSmoothFamilyOn_circleInverse_maps
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation H.grading)
    (travel : I → ℕ → ℝ) (a : ℝ) (ha : 0 < a) (hp : Monotone p) (hU : IsOpen U)
    (hlower : ∀ i x, x ∈ U → ∀ m θ, a ≤ 1 + deriv (H.decode (f i x) m) θ)
    (hf : UniformSmoothFamilyOn p H.grading U f)
    (hg : UniformSmoothFamilyOn p H.grading U g) :
    UniformSmoothFamilyOn p H.grading U
      (fun i x => circlePositiveInverseComposeLinear hH hT hD hγ (travel i) (f i x) (g i x)) := by
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  exact (uniformSmoothFamilyOn_circleInverseComposition hH hT hD hγ hi travel a ha).comp hp
    (hf.prodMk hp hg) hU ((circleUniformInverseDomain_isOpen H a).prod isOpen_univ)
    (fun i x hx => ⟨mem_circleUniformInverseDomain hH hT hD hγ ha (f i x) (hlower i x hx),
      mem_univ _⟩)

theorem uniformSmoothFamilyOn_circleAverage_maps
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation H.grading)
    (travel : ℕ → ℝ) (hp : Monotone p) (hU : IsOpen U)
    (hf : UniformSmoothFamilyOn p H.grading U f)
    (hg : UniformSmoothFamilyOn p H.grading U g) :
    UniformSmoothFamilyOn p H.grading U
      (fun i x => circleAverageComposeLinear hH hT hD hγ travel (f i x) (g i x)) := by
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  exact operations_uniform_binary_comp
    (Y := fun n => H.level n) (bond := H.bond)
    (p := p) (q := H.grading) (r := H.grading)
    (fun (_ : I) y z => circleAverageComposeLinear hH hT hD hγ travel y z)
    (uniformSmoothFamilyOn_circleAverage hH hT hD hγ hi travel) hp hU hf hg

theorem uniformSmoothFamilyOn_circleProduct_maps
    (hH : IsCircleModel T γ H) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation H.grading)
    (hp : Monotone p) (hU : IsOpen U)
    (hf : UniformSmoothFamilyOn p H.grading U f)
    (hg : UniformSmoothFamilyOn p H.grading U g) :
    UniformSmoothFamilyOn p H.grading U
      (fun i x => circleProductBilinear hH hT hD hγ (f i x) (g i x)) := by
  letI : ∀ n, CompleteSpace (H.level n) :=
    fun n => (hH.2.1 n).isComplete.completeSpace_coe
  exact (uniformSmoothFamilyOn_circleProduct hH hT hD hγ hi).comp hp
    (hf.prodMk hp hg) hU isOpen_univ (fun _ _ _ => mem_univ _)

end Maps

end ContinuousFlexibility.Statements
