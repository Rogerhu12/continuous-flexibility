module

public import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit

/-!
# The negative geometry obligation in three parts

The geometry interface on negative pieces is split by atoms:

* the forward chart atoms (`chartRadial`, `chartAngleDefect`, `jacobian`, `jacobianInverse`);
* the height atoms (`height`, `heightInverse`), given the forward chart atoms;
* the inverse chart atoms (`inverseRadial`, `inverseAngleDefect`) and the pulled height,
  given the first two on the same neighborhood.

`n04Realization_negativeGeometry_of_split` derives
`N04RealizationNegativeGeometryObligation` from the three parts.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
  ContinuousFlexibility.Blueprint
open CanonicalGeometry
open scoped ContDiff

/-- The forward chart atoms. -/
def atomIsNegativeChart : Atom → Prop
  | .chartRadial | .chartAngleDefect | .jacobian | .jacobianInverse => True
  | _ => False

/-- The height atoms. -/
def atomIsNegativeHeight : Atom → Prop
  | .height | .heightInverse => True
  | _ => False

/-- The inverse chart atoms. -/
def atomIsNegativeInverse : Atom → Prop
  | .inverseRadial | .inverseAngleDefect => True
  | _ => False

theorem atomIsGeometry_negative_cases (a : Atom) (ha : atomIsGeometry a) :
    atomIsNegativeChart a ∨ atomIsNegativeHeight a ∨ atomIsNegativeInverse a := by
  cases a <;> first
    | exact Or.inl trivial
    | exact Or.inr (Or.inl trivial)
    | exact Or.inr (Or.inr trivial)
    | exact ha.elim

namespace N04RealizationGauge

/-- Jet-difference data on the negative pieces for the atoms selected by `A`. -/
def NegativeAtomData (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (A : Atom → Prop) (b : ℕ) (ε : ℝ) : Prop :=
  ∀ a : Atom, A a → G.Data η (G.Neg η) b ε (G.atomFamily η a) (G.atomRef η a)

theorem negativeAtomData_mono (G : N04RealizationGauge)
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) {A : Atom → Prop} {b b' : ℕ} {ε ε' : ℝ}
    (h : G.NegativeAtomData η A b ε) (hb : b ≤ b') (hε : ε' ≤ ε) :
    G.NegativeAtomData η A b' ε' :=
  fun a ha => (h a ha).mono (fun _ h => h) hb hε (G.cost_nonneg η).1 (G.cost_nonneg η).2.1

end N04RealizationGauge

/-- The forward chart atoms on negative pieces. -/
def N04RealizationNegativeChartObligation : Prop :=
  ∀ (G : N04RealizationGauge) (b : ℕ) (ε : ℝ), G.Admissible b ε →
    ∃ (b' : ℕ) (ε' : ℝ), b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ η, G.NegativeAtomData η atomIsNegativeChart b' ε'

/-- The height atoms on negative pieces, recovered from the forward chart
and the physical radial coefficient through the nondegenerate angular density.
The chart premise is supplied by the preceding sibling, before the auxiliary
column is selected. -/
def N04RealizationNegativeHeightObligation : Prop :=
  ∀ (G : N04RealizationGauge) (b : ℕ) (ε : ℝ), G.Admissible b ε →
    (∀ η, G.NegativeAtomData η atomIsNegativeChart b ε) →
    ∃ (b' : ℕ) (ε' : ℝ), b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ η, G.NegativeAtomData η atomIsNegativeHeight b' ε'

/-- The inverse chart atoms and the pulled height on negative pieces, given the
forward chart and height atoms on the same neighborhood. -/
def N04RealizationNegativeInverseObligation : Prop :=
  ∀ (G : N04RealizationGauge) (b : ℕ) (ε : ℝ), G.Admissible b ε →
    (∀ η, G.NegativeAtomData η atomIsNegativeChart b ε) →
    (∀ η, G.NegativeAtomData η atomIsNegativeHeight b ε) →
    ∃ (b' : ℕ) (ε' : ℝ), b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ η, G.NegativeAtomData η atomIsNegativeInverse b' ε' ∧
        G.Data η (G.Neg η) b' ε' (G.pulledHeight η) (G.pulledHeightRef η)

theorem n04Realization_negativeGeometry_of_split
    (hchart : N04RealizationNegativeChartObligation)
    (hheight : N04RealizationNegativeHeightObligation)
    (hinv : N04RealizationNegativeInverseObligation) :
    N04RealizationNegativeGeometryObligation := by
  intro G b ε hadm
  refine Exists.elim (hchart G b ε hadm) (fun b₁ h₁ => Exists.elim h₁ (fun ε₁ h₁ => ?_))
  have hadm₁ : G.Admissible b₁ ε₁ := G.admissible_mono hadm h₁.1 h₁.2.1 h₁.2.2.1
  refine Exists.elim (hheight G b₁ ε₁ hadm₁ h₁.2.2.2)
    (fun b₂ h₂ => Exists.elim h₂ (fun ε₂ h₂ => ?_))
  have hadm₂ : G.Admissible b₂ ε₂ := G.admissible_mono hadm₁ h₂.1 h₂.2.1 h₂.2.2.1
  have hc : ∀ η, G.NegativeAtomData η atomIsNegativeChart b₂ ε₂ :=
    fun η => G.negativeAtomData_mono η (h₁.2.2.2 η) h₂.1 h₂.2.2.1
  refine Exists.elim (hinv G b₂ ε₂ hadm₂ hc h₂.2.2.2)
    (fun b₃ h₃ => Exists.elim h₃ (fun ε₃ h₃ => ?_))
  refine ⟨b₃, ε₃, h₁.1.trans (h₂.1.trans h₃.1), h₃.2.1,
    h₃.2.2.1.trans (h₂.2.2.1.trans h₁.2.2.1), fun η => ⟨fun a ha => ?_,
      (h₃.2.2.2 η).2⟩⟩
  rcases atomIsGeometry_negative_cases a ha with hca | hha | hia
  · exact G.negativeAtomData_mono η (hc η) h₃.1 h₃.2.2.1 a hca
  · exact G.negativeAtomData_mono η (h₂.2.2.2 η) h₃.1 h₃.2.2.1 a hha
  · exact (h₃.2.2.2 η).1 a hia

end ContinuousFlexibility.Analysis
