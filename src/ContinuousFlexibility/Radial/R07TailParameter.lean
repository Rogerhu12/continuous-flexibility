import ContinuousFlexibility.Radial.R07JoinParameterJets

/-!
# Joint continuity of the actual glued profile on either fixed tail

The geometry of the retained cells and their joins is independent of the
height sequence.  The local model scales linearly with its cell amplitude;
the actual joins have the previously proved smooth two-amplitude formula.
Pasting on this fixed locally finite collection of closed intervals therefore
gives joint continuity of every spatial jet, including at all seams.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

/-- A function continuous on each closed block of a strictly increasing
sequence is continuous jointly with arbitrary parameters before the limiting
endpoint.  The initial endpoint is included in the relative topology. -/
theorem continuousOn_parametric_ascending_blocks {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {a : ℕ → ℝ} {b : ℝ}
    {f : X × ℝ → Y} (ha : StrictMono a) (hlim : Tendsto a atTop (𝓝 b))
    (hf : ∀ k, ContinuousOn f {z | z.2 ∈ Icc (a k) (a (k + 1))}) :
    ContinuousOn f {z | z.2 ∈ Ico (a 0) b} := by
  intro z hz
  obtain ⟨k, hk⟩ := morse_outward_block_exists hlim hz.1 hz.2
  cases k with
  | zero =>
    have hu : {y : X × ℝ | y.2 < a (0 + 1)} ∈ 𝓝 z :=
      (isOpen_lt continuous_snd continuous_const).mem_nhds hk.2
    have hmem : {y : X × ℝ | y.2 ∈ Icc (a 0) (a (0 + 1))} ∈
        𝓝[{y : X × ℝ | y.2 ∈ Ico (a 0) b}] z := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hu, self_mem_nhdsWithin] with y hy hs
      exact ⟨hs.1, hy.le⟩
    exact (hf 0 z ⟨hk.1, hk.2.le⟩).mono_of_mem_nhdsWithin hmem
  | succ k =>
    have hc := (hf k).union_of_isClosed (hf (k + 1))
      (isClosed_Icc.preimage continuous_snd) (isClosed_Icc.preimage continuous_snd)
    have hu : {y : X × ℝ | y.2 ∈ Ioo (a k) (a ((k + 1) + 1))} ∈ 𝓝 z :=
      (isOpen_Ioo.preimage continuous_snd).mem_nhds
        ⟨(ha (Nat.lt_succ_self k)).trans_le hk.1, hk.2⟩
    have hmem : ({y : X × ℝ | y.2 ∈ Icc (a k) (a (k + 1))} ∪
        {y : X × ℝ | y.2 ∈ Icc (a (k + 1)) (a ((k + 1) + 1))}) ∈ 𝓝 z := by
      filter_upwards [hu] with y hy
      rcases le_total y.2 (a (k + 1)) with h | h
      · exact Or.inl ⟨hy.1.le, h⟩
      · exact Or.inr ⟨h, hy.2.le⟩
    exact ((hc z (Or.inr ⟨hk.1, hk.2.le⟩)).continuousAt hmem).continuousWithinAt

/-- The model and following join can first be pasted into a closed block;
the preceding theorem then pastes all outward blocks. -/
theorem continuousOn_parametric_outward_pieces {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {endpoint : ℝ}
    (D : MorseOutwardProfileData endpoint) {f : X × ℝ → Y}
    (hm : ∀ k, ContinuousOn f {z | z.2 ∈ Icc (D.enter k) (D.leave k)})
    (hj : ∀ k, ContinuousOn f {z | z.2 ∈ Icc (D.leave k) (D.enter (k + 1))}) :
    ContinuousOn f {z | z.2 ∈ Ico (D.enter 0) endpoint} := by
  apply continuousOn_parametric_ascending_blocks D.enter_strictMono D.limit
  intro k
  refine ((hm k).union_of_isClosed (hj k)
    (isClosed_Icc.preimage continuous_snd) (isClosed_Icc.preimage continuous_snd)).mono ?_
  intro z hz
  rcases le_total z.2 (D.leave k) with h | h
  · exact Or.inl ⟨hz.1, h⟩
  · exact Or.inr ⟨h, hz.2⟩

/-- Every model jet has continuous product-topology dependence on the height
sequence, since its germ is a scalar multiple of one fixed smooth model. -/
theorem continuousOn_morseChainGluedProfile_iteratedDeriv_model {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k n : ℕ) :
    ContinuousOn (fun z : Statements.HeightRatios × ℝ =>
      iteratedDeriv n (morseChainGluedProfile G z.1.val z.1.property) z.2)
      {z | z.2 ∈ Icc (morseChainCellLeftRadius T side k)
        (morseChainCellRightRadius T side k)} := by
  let M₀ := morseChainChosenModel G morseUnitHeights morseUnitHeights_admissible side k
  let A₀ := Statements.morseChainAmplitude T morseUnitHeights (T.index + k)
  have hA₀ : 0 < A₀ := morseChainAmplitude_pos T morseUnitHeights
    morseUnitHeights_admissible (T.index + k)
  have hM₀ := morseChainChosenModel_spec G morseUnitHeights morseUnitHeights_admissible side k
  have hA : Continuous (fun z : Statements.HeightRatios × ℝ =>
      Statements.morseChainAmplitude T z.1.val (T.index + k) / A₀) :=
    ((continuous_morseChainAmplitude T (T.index + k)).comp
      (continuous_subtype_val.comp continuous_fst)).div_const A₀
  have hM : Continuous (fun z : Statements.HeightRatios × ℝ => iteratedDeriv n M₀ z.2) :=
    (hM₀.1.continuous_iteratedDeriv n (by simp)).comp continuous_snd
  refine (hA.mul hM).continuousOn.congr ?_
  intro z hz
  have hσg := morseChainGluedProfile_model_germ G z.1.val z.1.property side k hz
  have h₀g : M₀ =ᶠ[𝓝 z.2] morseChainPhysicalModelHeight G A₀ side k := hM₀.2.2 z.2 hz
  have he : morseChainGluedProfile G z.1.val z.1.property =ᶠ[𝓝 z.2]
      fun y => (Statements.morseChainAmplitude T z.1.val (T.index + k) / A₀) * M₀ y := by
    filter_upwards [hσg, h₀g] with y hyσ hy₀
    rw [hyσ, hy₀]
    change morseChainPhysicalModelHeight G
        (Statements.morseChainAmplitude T z.1.val (T.index + k)) side k y =
      (Statements.morseChainAmplitude T z.1.val (T.index + k) / A₀) *
        morseChainPhysicalModelHeight G A₀ side k y
    simp only [morseChainPhysicalModelHeight]
    field_simp [hA₀.ne']
    <;> ring
  change iteratedDeriv n (morseChainGluedProfile G z.1.val z.1.property) z.2 =
    (Statements.morseChainAmplitude T z.1.val (T.index + k) / A₀) *
      iteratedDeriv n M₀ z.2
  rw [he.iteratedDeriv_eq n, iteratedDeriv_const_mul_field]

/-- The same continuity holds on a physical join, including its two
endpoints, for the actual globally glued profile. -/
theorem continuousOn_morseChainGluedProfile_iteratedDeriv_join {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k n : ℕ) :
    ContinuousOn (fun z : Statements.HeightRatios × ℝ =>
      iteratedDeriv n (morseChainGluedProfile G z.1.val z.1.property) z.2)
      {z | z.2 ∈ Icc (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k))} := by
  refine (continuousOn_morseChainChosenJoinProfile_iteratedDeriv G side k n).congr ?_
  intro z hz
  exact (morseChainGluedProfile_join_germ G z.1.val z.1.property side k hz).iteratedDeriv_eq n

/-- Joint continuity of every spatial jet on either fixed physical tail.
The domain includes the entrance seam and all later model/join seams. -/
theorem continuousOn_morseChainGluedProfile_iteratedDeriv_tail {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (N n : ℕ) :
    ContinuousOn (fun z : Statements.HeightRatios × ℝ =>
      iteratedDeriv n (morseChainGluedProfile G z.1.val z.1.property) z.2)
      {z | if side then z.2 ∈ Ico (morseChainCellLeftRadius T true N) G.rightEnd
        else z.2 ∈ Ioc 1 (morseChainCellRightRadius T false N)} := by
  let f : Statements.HeightRatios × ℝ → ℝ := fun z =>
    iteratedDeriv n (morseChainGluedProfile G z.1.val z.1.property) z.2
  cases side
  · let D := morseChainLeftProfileData G morseUnitHeights morseUnitHeights_admissible
    have hneg : Continuous (fun z : Statements.HeightRatios × ℝ => (z.1, -z.2)) :=
      continuous_fst.prodMk continuous_snd.neg
    have hc : ContinuousOn (fun z : Statements.HeightRatios × ℝ => f (z.1, -z.2))
        {z | z.2 ∈ Ico (D.enter 0) (-1)} := by
      apply continuousOn_parametric_outward_pieces D
      · intro k
        refine (continuousOn_morseChainGluedProfile_iteratedDeriv_model G false k n).comp
          hneg.continuousOn ?_
        intro z hz
        have h₁ : -morseChainCellRightRadius T false k ≤ z.2 := hz.1
        have h₂ : z.2 ≤ -morseChainCellLeftRadius T false k := hz.2
        exact ⟨by linarith only [h₂], by linarith only [h₁]⟩
      · intro k
        refine (continuousOn_morseChainGluedProfile_iteratedDeriv_join G false k n).comp
          hneg.continuousOn ?_
        intro z hz
        rw [(G.joins k).2.2.1, (G.joins k).2.2.2]
        change morseChainCellRightRadius T false (k + 1) ≤ -z.2 ∧
          -z.2 ≤ morseChainCellLeftRadius T false k
        have h₁ : -morseChainCellLeftRadius T false k ≤ z.2 := hz.1
        have h₂ : z.2 ≤ -morseChainCellRightRadius T false (k + 1) := hz.2
        exact ⟨by linarith only [h₂], by linarith only [h₁]⟩
    have htail : ContinuousOn (fun z : Statements.HeightRatios × ℝ => f (z.1, -(-z.2)))
        {z | z.2 ∈ Ioc 1 (morseChainCellRightRadius T false N)} := by
      refine hc.comp hneg.continuousOn ?_
      intro z hz
      refine ⟨?_, neg_lt_neg hz.1⟩
      exact (D.enter_strictMono.monotone (Nat.zero_le N)).trans (neg_le_neg hz.2)
    simpa only [f, neg_neg, Bool.false_eq_true, ite_false] using htail
  · let D := morseChainRightProfileData G morseUnitHeights morseUnitHeights_admissible
    have hc : ContinuousOn f {z | z.2 ∈ Ico (D.enter 0) G.rightEnd} := by
      apply continuousOn_parametric_outward_pieces D
      · intro k
        exact continuousOn_morseChainGluedProfile_iteratedDeriv_model G true k n
      · intro k
        have h := continuousOn_morseChainGluedProfile_iteratedDeriv_join G true k n
        change ContinuousOn f {z | z.2 ∈ Icc
          (morseChainCellRightRadius T true k) (morseChainCellLeftRadius T true (k + 1))}
        simpa only [f, morseChainCellRightRadius, morseChainCellLeftRadius,
          (G.joins k).1, (G.joins k).2.1] using h
    refine hc.mono ?_
    intro z hz
    exact ⟨(D.enter_strictMono.monotone (Nat.zero_le N)).trans hz.1, hz.2⟩

/-- A product continuity statement with a parameter subtype is equivalent
to continuity on the corresponding product subset of the ambient space. -/
theorem continuousOn_prod_of_continuousOn_subtype {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {s : Set X} {t : Set Y} {f : X × Y → Z}
    (hf : ContinuousOn (fun z : s × Y => f (z.1.val, z.2)) {z | z.2 ∈ t}) :
    ContinuousOn f (s ×ˢ t) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  let lift : (s ×ˢ t) → s × Y := fun z => (⟨z.val.1, z.property.1⟩, z.val.2)
  have hlift : Continuous lift :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  have hc : ContinuousOn (fun z : (s ×ˢ t) => f ((lift z).1.val, (lift z).2)) univ :=
    hf.comp hlift.continuousOn (fun z _ => z.property.2)
  exact continuousOn_univ.mp hc

/-- The tail-jet theorem for any total profile family agreeing with the
actual glued profile as a germ on the tail.  In particular it applies after
altering the middle while retaining the two actual Morse tails. -/
theorem continuousOn_morseChain_family_iteratedDeriv_tail {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (w : (ℕ → ℝ) → ℝ → ℝ) (side : Bool) (N n : ℕ)
    (hw : ∀ (σ : ℕ → ℝ) (hσ : ∀ i, 1 ≤ σ i ∧ σ i ≤ 2) (x : ℝ),
      (if side then x ∈ Ico (morseChainCellLeftRadius T true N) G.rightEnd
        else x ∈ Ioc 1 (morseChainCellRightRadius T false N)) →
      w σ =ᶠ[𝓝 x] morseChainGluedProfile G σ hσ) :
    ContinuousOn (fun z : (ℕ → ℝ) × ℝ => iteratedDeriv n (w z.1) z.2)
      ({σ | ∀ i, 1 ≤ σ i ∧ σ i ≤ 2} ×ˢ
        (if side then Ico (morseChainCellLeftRadius T true N) G.rightEnd
          else Ioc 1 (morseChainCellRightRadius T false N))) := by
  apply continuousOn_prod_of_continuousOn_subtype
  change ContinuousOn (fun z : Statements.HeightRatios × ℝ =>
    iteratedDeriv n (w z.1.val) z.2)
    {z | z.2 ∈ (if side then Ico (morseChainCellLeftRadius T true N) G.rightEnd
      else Ioc 1 (morseChainCellRightRadius T false N))}
  have hset : {z : Statements.HeightRatios × ℝ |
      z.2 ∈ (if side then Ico (morseChainCellLeftRadius T true N) G.rightEnd
        else Ioc 1 (morseChainCellRightRadius T false N))} =
      {z : Statements.HeightRatios × ℝ |
        if side then z.2 ∈ Ico (morseChainCellLeftRadius T true N) G.rightEnd
          else z.2 ∈ Ioc 1 (morseChainCellRightRadius T false N)} := by
    cases side <;> rfl
  rw [hset]
  have hc := continuousOn_morseChainGluedProfile_iteratedDeriv_tail G side N n
  refine hc.congr ?_
  intro z hz
  exact (hw z.1.val z.1.property z.2 hz).iteratedDeriv_eq n

end ContinuousFlexibility.Radial
