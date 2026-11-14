module

public import ContinuousFlexibility.Analysis.N04PrincipalPositiveReference
public import ContinuousFlexibility.Analysis.N04RealizationEnvelopeComposition
public import ContinuousFlexibility.Analysis.N07aCoordinateJetNorms

/-!
# Reference jets after the normalized inverse chart

Both coordinates of the normalized inverse are already reference atoms;
the angle is the identity angle plus its stored defect.  Thus finite
composition costs only a coefficient power.  The composition estimate
uses positive inner derivatives and never bounds the unwrapped angle.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- The reference inverse point expressed in the fixed physical unit
coordinates, using the two actual inverse atoms. -/
def n04PrincipalPositive_referenceUnitInverse
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (q : PolarPoint) : PolarPoint :=
  (G.atomRef η .inverseRadial m q, q.2 + G.atomRef η .inverseAngleDefect m q)

theorem n04PrincipalPositive_referenceUnitInverse_maps {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) :
    MapsTo (G.n04PrincipalPositive_referenceUnitInverse η m) unitStrip unitStrip := by
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
  have hx : (G.V η).inverseChart (G.ref η) m (canonicalUnitPoint (G.V η) m q) ∈
      referencePhysicalPieceOpen (G.S η) (G.V η) m := by
    rw [← hA.referenceDomain m]
    exact (hA.charts (G.ref η) hz hs m).2.1 hcan
  have hwidth : 0 < (G.V η).physicalRight m - (G.V η).physicalLeft m :=
    sub_pos.mpr (hA.referenceBounds m).1
  refine ⟨⟨?_, ?_⟩, mem_univ _⟩
  · exact div_pos (sub_pos.mpr hx.1.1) hwidth
  · exact (div_lt_one hwidth).mpr (sub_lt_sub_right hx.1.2 _)

theorem n04PrincipalPositive_referenceUnitInverse_point {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (m : ℕ) (q : PolarPoint) :
    physicalUnitPoint (G.V η) m (G.n04PrincipalPositive_referenceUnitInverse η m q) =
      (G.V η).inverseChart (G.ref η) m (canonicalUnitPoint (G.V η) m q) := by
  have hw : (G.V η).physicalRight m - (G.V η).physicalLeft m ≠ 0 :=
    (sub_pos.mpr ((G.n04PrincipalPositive_admissible_parts h η).1.referenceBounds m).1).ne'
  apply Prod.ext
  · change (G.V η).physicalLeft m + ((G.V η).physicalRight m - (G.V η).physicalLeft m) *
      ((((G.V η).inverseChart (G.ref η) m (canonicalUnitPoint (G.V η) m q)).1 -
        (G.V η).physicalLeft m) /
          ((G.V η).physicalRight m - (G.V η).physicalLeft m)) = _
    rw [mul_div_cancel₀ _ hw]
    ring
  · change q.2 + (((G.V η).inverseChart (G.ref η) m
        (canonicalUnitPoint (G.V η) m q)).2 - (canonicalUnitPoint (G.V η) m q).2) = _
    change q.2 + (_ - q.2) = _
    ring

theorem n04PrincipalPositive_referenceUnitInverse_smooth
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) (m : ℕ) :
    ContDiffOn ℝ ∞ (G.n04PrincipalPositive_referenceUnitInverse η m) unitStrip :=
  (href.1 m .inverseRadial).1.prodMk
    (contDiffOn_snd.add (href.1 m .inverseAngleDefect).1)

/-- Uniform reference mixed-jet bounds also control every ordinary
Fréchet jet, with one coefficient-power constant for all atoms. -/
theorem n04PrincipalPositive_referenceAtom_frechet_bounds
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m a q, q ∈ unitStrip →
      ‖iteratedFDeriv ℝ n (G.atomRef η a m) q‖ ≤
        B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  have hb := href.2 n
  have hp := coefficientEnvelope_pack ((2 : ℝ) ^ n * hb.choose) hb.choose
  refine ⟨hp.choose, hp.choose_spec.1, ?_⟩
  intro m a q hq
  have hE := (G.cost_nonneg η).2.2 m
  have hn := norm_iteratedFDeriv_le_of_mixedDerivative
    (isOpen_Ioo.prod isOpen_univ) (href.1 m a).1 n hq
    (mul_nonneg hb.choose_spec.1.le (Real.rpow_nonneg (zero_le_one.trans hE) _))
    (fun i j hij => by
      rw [Real.norm_eq_abs]
      exact hb.choose_spec.2 m a q hq i j hij.le)
  exact hn.trans (by
    simpa only [mul_assoc] using hp.choose_spec.2 _ hE)

/-- Composition by the reference inverse retains all reference spatial
jets with the material sample of the same piece. -/
theorem n04PrincipalPositive_reference_composedAtom_bounds {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m a (q : unitStrip) i j, i + j ≤ s →
      |mixedDerivative i j (fun y => G.atomRef η a m
        (G.n04PrincipalPositive_referenceUnitInverse η m y)) q.val| ≤
        B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  let X := ℕ × Atom × unitStrip
  let E : X → ℝ := fun x => G.W.U.E0 (G.W.U.sample ((G.V η).cell x.1))
  let f : X → PolarPoint → ℝ := fun x => G.atomRef η x.2.1 x.1
  let g : X → PolarPoint → PolarPoint := fun x =>
    G.n04PrincipalPositive_referenceUnitInverse η x.1
  let p : X → PolarPoint := fun x => x.2.2.val
  have hE : ∀ x, 1 ≤ E x := fun x => (G.cost_nonneg η).2.2 x.1
  have hopen : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hmap : ∀ x, g x (p x) ∈ unitStrip := fun x =>
    G.n04PrincipalPositive_referenceUnitInverse_maps h η x.1 x.2.2.property
  have hf : ∀ x, ContDiffAt ℝ ∞ (f x) (g x (p x)) := fun x =>
    ((href.1 x.1 x.2.1).1 _ (hmap x)).contDiffAt (hopen.mem_nhds (hmap x))
  have hg : ∀ x, ContDiffAt ℝ ∞ (g x) (p x) := fun x =>
    ((G.n04PrincipalPositive_referenceUnitInverse_smooth η href x.1) _ x.2.2.property).contDiffAt
      (hopen.mem_nhds x.2.2.property)
  have hfj (n : ℕ) : HasPositiveEnvelope E
      (fun x => ‖iteratedFDeriv ℝ n (f x) (g x (p x))‖) := by
    have hn := G.n04PrincipalPositive_referenceAtom_frechet_bounds η href n
    exact ⟨hn.choose, hn.choose, hn.choose_spec.1, hn.choose_spec.1,
      fun x => hn.choose_spec.2 x.1 x.2.1 _ (hmap x)⟩
  have hgj (n : ℕ) (hn : 0 < n) : HasPositiveEnvelope E
      (fun x => ‖iteratedFDeriv ℝ n (g x) (p x)‖) := by
    have hb := G.n04PrincipalPositive_referenceAtom_frechet_bounds η href n
    let A := hb.choose
    have hA : 0 < A := hb.choose_spec.1
    have hle : ∀ x, ‖iteratedFDeriv ℝ n (g x) (p x)‖ ≤ (2 * A + 1) * E x ^ A := by
      intro x
      have hu := ((href.1 x.1 .inverseRadial).1 _ x.2.2.property).contDiffAt
        (hopen.mem_nhds x.2.2.property)
      have hv := ((href.1 x.1 .inverseAngleDefect).1 _ x.2.2.property).contDiffAt
        (hopen.mem_nhds x.2.2.property)
      have hpair := n07a_coordinatePair_iteratedFDeriv_bound hu hv 0 1 hn
      have hpair' : ‖iteratedFDeriv ℝ n (g x) (p x)‖ ≤
          ‖iteratedFDeriv ℝ n (G.atomRef η .inverseRadial x.1) (p x)‖ + 1 +
          ‖iteratedFDeriv ℝ n (G.atomRef η .inverseAngleDefect x.1) (p x)‖ := by
        change ‖iteratedFDeriv ℝ n
          (fun y => (G.atomRef η .inverseRadial x.1 y,
            y.2 + G.atomRef η .inverseAngleDefect x.1 y)) x.2.2.val‖ ≤
          ‖iteratedFDeriv ℝ n (G.atomRef η .inverseRadial x.1) x.2.2.val‖ + 1 +
            ‖iteratedFDeriv ℝ n (G.atomRef η .inverseAngleDefect x.1) x.2.2.val‖
        simpa only [atomRef, ref, abs_one, one_mul, zero_add] using hpair
      have huB := hb.choose_spec.2 x.1 .inverseRadial (p x) x.2.2.property
      have hvB := hb.choose_spec.2 x.1 .inverseAngleDefect (p x) x.2.2.property
      have he1 : 1 ≤ E x ^ A := Real.one_le_rpow (hE x) hA.le
      nlinarith only [hpair', huB, hvB, he1]
    exact ⟨2 * A + 1, A, by positivity, hA, hle⟩
  have hcomp (n : ℕ) : HasPositiveEnvelope E
      (fun x => ‖iteratedFDeriv ℝ n (f x ∘ g x) (p x)‖) :=
    n04Realization_envelope_comp_jets hE p f g hf hg n
      (fun j _ => hfj j) (fun j hj _ => hgj j hj)
  have hfinite := n04Realization_envelope_finite_uniform hE
    (fun n : Fin (s + 1) => fun x => ‖iteratedFDeriv ℝ n.val (f x ∘ g x) (p x)‖)
    (fun _ _ => norm_nonneg _) (fun n => hcomp n.val)
  have hp := coefficientEnvelope_pack hfinite.choose hfinite.choose_spec.choose
  refine ⟨hp.choose, hp.choose_spec.1, ?_⟩
  intro m a q i j hij
  let x : X := (m, a, q)
  have hsm : ContDiffOn ℝ ∞ (f x ∘ g x) unitStrip :=
    (href.1 m a).1.comp (G.n04PrincipalPositive_referenceUnitInverse_smooth η href m)
      (G.n04PrincipalPositive_referenceUnitInverse_maps h η m)
  have hm := abs_mixedDerivative_le_norm_iteratedFDeriv hopen hsm i j q.property
  exact hm.trans ((hfinite.choose_spec.choose_spec.2.2 x ⟨i + j, by omega⟩).trans
    (hp.choose_spec.2 _ (hE x)))

/-- The reference pulled height and its reciprocal are the compositions
of the corresponding physical reference atoms with the same normalized
inverse map. -/
theorem n04PrincipalPositive_pulledHeightRef_eq_composedAtom {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (m : ℕ) (inverse : Bool) :
    (fun q => if inverse then (G.pulledHeightRef η m q)⁻¹ else G.pulledHeightRef η m q) =
      (fun q => G.atomRef η (if inverse then .heightInverse else .height) m
        (G.n04PrincipalPositive_referenceUnitInverse η m q)) := by
  funext q
  have he := G.n04PrincipalPositive_referenceUnitInverse_point h η m q
  cases inverse <;>
    simp only [Bool.false_eq_true, ↓reduceIte, atomRef, atom, he,
      pulledHeightRef, heightField, pulledPoint, ref]

/-- Full reference spatial bounds for both pulled-height factors, on all
pieces and without a change of material sample. -/
theorem n04PrincipalPositive_pulledHeightRef_jets {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (href : ReferenceJets G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)) :
    (∀ m (inverse : Bool), ContDiffOn ℝ ∞
      (fun q => if inverse then (G.pulledHeightRef η m q)⁻¹ else G.pulledHeightRef η m q)
      unitStrip) ∧
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m (inverse : Bool) (q : unitStrip) i j, i + j ≤ s →
      |mixedDerivative i j
        (fun y => if inverse then (G.pulledHeightRef η m y)⁻¹ else G.pulledHeightRef η m y)
        q.val| ≤ B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B := by
  refine ⟨?_, fun s => ?_⟩
  · intro m inverse
    rw [G.n04PrincipalPositive_pulledHeightRef_eq_composedAtom h η m inverse]
    exact (href.1 m _).1.comp
      (G.n04PrincipalPositive_referenceUnitInverse_smooth η href m)
      (G.n04PrincipalPositive_referenceUnitInverse_maps h η m)
  · have hb := G.n04PrincipalPositive_reference_composedAtom_bounds h η href s
    refine ⟨hb.choose, hb.choose_spec.1, ?_⟩
    intro m inverse q i j hij
    rw [G.n04PrincipalPositive_pulledHeightRef_eq_composedAtom h η m inverse]
    exact hb.choose_spec.2 m _ q i j hij

end N04RealizationGauge

end ContinuousFlexibility.Analysis
