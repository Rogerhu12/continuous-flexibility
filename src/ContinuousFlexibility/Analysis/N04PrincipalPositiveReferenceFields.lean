import ContinuousFlexibility.Analysis.N04PrincipalPositiveReferenceJets
import ContinuousFlexibility.Analysis.N01OriginalCoefficientTameBounds

/-!
# Reference physical coefficients at the same inverse point

On a positive reference piece the corrected coefficients agree with the
original coefficients. Their physical spatial jets have uniform bounds
from N01. Composing with the actual inverse point therefore costs only
the reference inverse atoms and the fixed physical width of this piece.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff Topology

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

theorem n04PrincipalPositive_reference_pulledPoint_formula {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) :
    G.pulledPoint η (G.ref η) m = fun q =>
      ((G.V η).physicalLeft m + ((G.V η).physicalRight m - (G.V η).physicalLeft m) *
        G.atomRef η .inverseRadial m q,
        q.2 + G.atomRef η .inverseAngleDefect m q) := by
  funext q
  exact (G.n04PrincipalPositive_referenceUnitInverse_point h η m q).symm

theorem n04PrincipalPositive_reference_pulledPoint_smooth {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) (m : ℕ) :
    ContDiffOn ℝ ∞ (G.pulledPoint η (G.ref η) m) unitStrip := by
  rw [G.n04PrincipalPositive_reference_pulledPoint_formula h η m]
  exact (contDiffOn_const.add (contDiffOn_const.mul (href.1 m .inverseRadial).1)).prodMk
    (contDiffOn_snd.add (href.1 m .inverseAngleDefect).1)

theorem n04PrincipalPositive_reference_pulledPoint_maps {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) :
    MapsTo (G.pulledPoint η (G.ref η) m) unitStrip
      (referencePhysicalPieceOpen (G.S η) (G.V η) m) := by
  have hA := (G.n04PrincipalPositive_admissible_parts h η).1
  have hz : G.ref η ∈ stateNeighborhood (G.S η) (G.C η) b ε :=
    reference_mem_stateNeighborhood (G.S η) (G.C η) b h.2.1
  have hs : stateSector (G.S η) (G.C η).referenceState :=
    G.W.through03.1.1.2.2.1.stateSector
  intro q hq
  have hlen : 0 < (G.V η).right m - (G.V η).left m :=
    sub_pos.mpr (hA.referenceBounds m).2.1
  have hcan : canonicalUnitPoint (G.V η) m q ∈ canonicalOpen (G.S η) (G.V η) m := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · change (G.V η).left m < (G.V η).left m + _
      exact lt_add_of_pos_right _ (mul_pos hlen hq.1.1)
    · have ht := mul_lt_of_lt_one_right hlen hq.1.2
      change (G.V η).left m + _ < (G.V η).right m
      linarith only [ht]
  rw [← hA.referenceDomain m]
  exact (hA.charts (G.ref η) hz hs m).2.1 hcan

/-- Only positive inverse derivatives are bounded: the unwrapped angle
is never required to have a zeroth-order envelope. -/
theorem n04PrincipalPositive_reference_pulledPoint_positive_jets {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η))
    (n : ℕ) (hn : 0 < n) :
    ∃ B : ℝ, 0 < B ∧ ∀ m (q : unitStrip),
      ‖iteratedFDeriv ℝ n (G.pulledPoint η (G.ref η) m) q.val‖ ≤
        B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  let X := ℕ × unitStrip
  let E : X → ℝ := fun x => G.W.U.E0 (G.W.U.sample ((G.V η).cell x.1))
  have hE : ∀ x, 1 ≤ E x := fun x => (G.cost_nonneg η).2.2 x.1
  have hwidth : HasPositiveEnvelope E
      (fun x => |(G.V η).physicalRight x.1 - (G.V η).physicalLeft x.1|) := by
    have hb := href.2 0
    refine ⟨hb.choose, hb.choose, hb.choose_spec.1, hb.choose_spec.1, fun x => ?_⟩
    exact hb.choose_spec.2 x.1 .physicalLength x.2.val x.2.property 0 0 (by omega)
  have hatom (a : Atom) : HasPositiveEnvelope E
      (fun x => ‖iteratedFDeriv ℝ n (G.atomRef η a x.1) x.2.val‖) := by
    have hb := G.n04PrincipalPositive_referenceAtom_frechet_bounds η href n
    exact ⟨hb.choose, hb.choose, hb.choose_spec.1, hb.choose_spec.1,
      fun x => hb.choose_spec.2 x.1 a x.2.val x.2.property⟩
  have hsum := ((hwidth.mul hE (hatom .inverseRadial) (fun _ => norm_nonneg _)).add
    hE (hasPositiveEnvelope_const E hE 1)).add hE (hatom .inverseAngleDefect)
  have hb : HasPositiveEnvelope E
      (fun x => ‖iteratedFDeriv ℝ n (G.pulledPoint η (G.ref η) x.1) x.2.val‖) := by
    apply hsum.mono
    intro x
    have hopen : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
    have hu := ((href.1 x.1 .inverseRadial).1 x.2.val x.2.property).contDiffAt
      (hopen.mem_nhds x.2.property)
    have hv := ((href.1 x.1 .inverseAngleDefect).1 x.2.val x.2.property).contDiffAt
      (hopen.mem_nhds x.2.property)
    rw [G.n04PrincipalPositive_reference_pulledPoint_formula h η x.1]
    exact n07a_coordinatePair_iteratedFDeriv_bound hu hv
      ((G.V η).physicalLeft x.1)
      ((G.V η).physicalRight x.1 - (G.V η).physicalLeft x.1) hn
  have hp := coefficientEnvelope_pack hb.choose hb.choose_spec.choose
  exact ⟨hp.choose, hp.choose_spec.1, fun m q =>
    (hb.choose_spec.choose_spec.2.2 (m, q)).trans (hp.choose_spec.2 _ (hE (m, q)))⟩

/-- N03 has not altered the positive reference coefficient field. -/
theorem n04PrincipalPositive_pulledCoefficientRef_eq_original {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (m : ℕ) (hm : G.Pos η m) (c : Fin 3) :
    EqOn (G.pulledRef η (G.coefficientField η c) m)
      (fun q => originalCoefficientEntry G.W.D G.W.S G.W.C c
        (G.W.C.referenceState, 0) (G.pulledPoint η (G.ref η) m q)) unitStrip := by
  have hA := (G.n04PrincipalPositive_admissible_parts h η).1
  have hz : (G.W.C.referenceState, 0) ∈
      stateNeighborhood G.W.S G.W.C G.W.base G.W.ε :=
    reference_mem_stateNeighborhood G.W.S G.W.C G.W.base G.W.through03.1.1.2.1
  have hs : stateSector G.W.S G.W.C.referenceState :=
    G.W.through03.1.1.2.2.1.stateSector
  intro q hq
  let p := G.pulledPoint η (G.ref η) m q
  have hp := G.n04PrincipalPositive_reference_pulledPoint_maps h η m hq
  have hpD : p ∈ annularOpen G.W.D :=
    ⟨(hA.referenceBounds m).2.2 hp.1, mem_univ _⟩
  have hpos : 0 < deriv G.W.D.w p.1 := hA.referencePositive m hm p.1 hp.1
  have ha := G.W.through03.2.1 (G.W.C.referenceState, 0) hz hs p
  have hbc := G.W.through03.2.2.1 (G.W.C.referenceState, 0) hz hs p hpD hpos
  fin_cases c
  · exact ha
  · exact hbc.1.self_of_nhds
  · exact hbc.2.self_of_nhds

/-- The three pulled coefficient references have every spatial jet on
the positive pieces, with a common coefficient-power envelope. -/
theorem n04PrincipalPositive_pulledCoefficientRef_jets {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    (∀ m, G.Pos η m → ∀ c : Fin 3,
      ContDiffOn ℝ ∞ (G.pulledRef η (G.coefficientField η c) m) unitStrip) ∧
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m, G.Pos η m → ∀ (c : Fin 3) (q : unitStrip) i j,
      i + j ≤ s →
      |mixedDerivative i j (G.pulledRef η (G.coefficientField η c) m) q.val| ≤
        B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  let X := ℕ × Fin 3 × unitStrip
  let E : X → ℝ := fun x => G.W.U.E0 (G.W.U.sample ((G.V η).cell x.1))
  let f : X → PolarPoint → ℝ := fun x =>
    originalCoefficientEntry G.W.D G.W.S G.W.C x.2.1 (G.W.C.referenceState, 0)
  let g : X → PolarPoint → PolarPoint := fun x => G.pulledPoint η (G.ref η) x.1
  let p : X → PolarPoint := fun x => x.2.2.val
  have hE : ∀ x, 1 ≤ E x := fun x => (G.cost_nonneg η).2.2 x.1
  have hopen : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hmap (m : ℕ) : MapsTo (G.pulledPoint η (G.ref η) m) unitStrip
      (annularOpen G.W.D) := by
    intro q hq
    have hp := G.n04PrincipalPositive_reference_pulledPoint_maps h η m hq
    exact ⟨((G.n04PrincipalPositive_admissible_parts h η).1.referenceBounds m).2.2 hp.1,
      mem_univ _⟩
  have hfOn (c : Fin 3) : ContDiffOn ℝ ∞
      (originalCoefficientEntry G.W.D G.W.S G.W.C c (G.W.C.referenceState, 0))
      (annularOpen G.W.D) :=
    (G.W.through03.1.1.reference_coefficient_smooth_jets c).1
  have hcompOn (m : ℕ) (c : Fin 3) : ContDiffOn ℝ ∞
      (fun q => originalCoefficientEntry G.W.D G.W.S G.W.C c
        (G.W.C.referenceState, 0) (G.pulledPoint η (G.ref η) m q)) unitStrip :=
    (hfOn c).comp (G.n04PrincipalPositive_reference_pulledPoint_smooth h η href m)
      (hmap m)
  have hf : ∀ x, ContDiffAt ℝ ∞ (f x) (g x (p x)) := fun x =>
    ((hfOn x.2.1) _ (hmap x.1 x.2.2.property)).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds (hmap x.1 x.2.2.property))
  have hg : ∀ x, ContDiffAt ℝ ∞ (g x) (p x) := fun x =>
    ((G.n04PrincipalPositive_reference_pulledPoint_smooth h η href x.1) _
      x.2.2.property).contDiffAt (hopen.mem_nhds x.2.2.property)
  have hfj (n : ℕ) : HasPositiveEnvelope E
      (fun x => ‖iteratedFDeriv ℝ n (f x) (g x (p x))‖) := by
    have hb := G.W.through03.1.1.reference_coefficient_mixed_uniform_bound n
    apply (hasPositiveEnvelope_const E hE ((2 : ℝ) ^ n * hb.choose)).mono
    intro x
    exact norm_iteratedFDeriv_le_of_mixedDerivative
      (isOpen_Ioo.prod isOpen_univ) (hfOn x.2.1) n (hmap x.1 x.2.2.property)
      hb.choose_spec.1 (fun i j hij => by
        rw [Real.norm_eq_abs]
        exact hb.choose_spec.2 x.2.1 i j hij.le _ (hmap x.1 x.2.2.property))
  have hgj (n : ℕ) (hn : 0 < n) : HasPositiveEnvelope E
      (fun x => ‖iteratedFDeriv ℝ n (g x) (p x)‖) := by
    have hb := G.n04PrincipalPositive_reference_pulledPoint_positive_jets h η href n hn
    exact ⟨hb.choose, hb.choose, hb.choose_spec.1, hb.choose_spec.1,
      fun x => hb.choose_spec.2 x.1 x.2.2⟩
  have hcomp (n : ℕ) : HasPositiveEnvelope E
      (fun x => ‖iteratedFDeriv ℝ n (f x ∘ g x) (p x)‖) :=
    n04Realization_envelope_comp_jets hE p f g hf hg n
      (fun j _ => hfj j) (fun j hj _ => hgj j hj)
  refine ⟨?_, fun s => ?_⟩
  · intro m hm c
    exact (hcompOn m c).congr
      (G.n04PrincipalPositive_pulledCoefficientRef_eq_original h η m hm c)
  · have hfinite := n04Realization_envelope_finite_uniform hE
      (fun n : Fin (s + 1) => fun x => ‖iteratedFDeriv ℝ n.val (f x ∘ g x) (p x)‖)
      (fun _ _ => norm_nonneg _) (fun n => hcomp n.val)
    have hp := coefficientEnvelope_pack hfinite.choose hfinite.choose_spec.choose
    refine ⟨hp.choose, hp.choose_spec.1, ?_⟩
    intro m hm c q i j hij
    rw [mixedDerivative_congr_on_open hopen
      (G.n04PrincipalPositive_pulledCoefficientRef_eq_original h η m hm c) i j q.property]
    let x : X := (m, c, q)
    have hmixed := abs_mixedDerivative_le_norm_iteratedFDeriv hopen
      (hcompOn m c) i j q.property
    exact hmixed.trans ((hfinite.choose_spec.choose_spec.2.2 x
      ⟨i + j, by omega⟩).trans (hp.choose_spec.2 _ (hE x)))

end N04RealizationGauge

end ContinuousFlexibility.Analysis
