import ContinuousFlexibility.Analysis.NeumannPackage
import ContinuousFlexibility.Statements.Nonlinear

/-!
# The algebraic and Banach-space construction in N06

Once the physical perturbed operator has been constructed on the fixed graph domain and its
relative operator is small, the existing Neumann package supplies exactly the inverse required
by `N06Properties`. The source space is complete because its defining jet graph is closed.

The lemmas below do not assert the analytic smallness estimate or construct the physical
operator. They isolate the remaining algebra without changing either of those obligations.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

section Neumann

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A total operator-valued function, equal to the Neumann inverse whenever its norm test holds. -/
def n06TotalNeumannInverse (R : E →L[ℝ] E) : E →L[ℝ] E :=
  if h : ‖R‖ < 1 then neumannInverse R h else 0

theorem n06TotalNeumannInverse_spec (R : E →L[ℝ] E) (hR : ‖R‖ < (1 / 2 : ℝ)) :
    (∀ F, n06TotalNeumannInverse R (F + R F) = F ∧
      n06TotalNeumannInverse R F + R (n06TotalNeumannInverse R F) = F) ∧
      ‖n06TotalNeumannInverse R‖ ≤ 2 := by
  have h1 : ‖R‖ < 1 := lt_trans hR (by norm_num)
  simp only [n06TotalNeumannInverse, dif_pos h1]
  exact ⟨fun F => ⟨neumannInverse_apply_add R h1 F, neumannInverse_add_apply R h1 F⟩,
    norm_neumannInverse_le_two R h1 hR.le⟩

end Neumann

section FixedDomain

variable {S : PhysicalSpacesData} {K : CanonicalData S} {V : VolumeModelData S K}
  {b : ℕ} {B : CanonicalDomainData S K V b}

/-- The relative operator on precisely the already selected source space. -/
def n06RelativeOperator
    (P : AnnularState S × ℝ → B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (z : AnnularState S × ℝ) :
    V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b :=
  (P z).comp B.inverse - ContinuousLinearMap.id ℝ _

/-- The relative inverse data, defined at every parameter, on the original source and graph. -/
def n06RelativeData [CompleteSpace (V.level (3 / 4 : ℝ) 0 b)]
    (P : AnnularState S × ℝ → B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b) :
    RelativeInverseData S K V b B where
  operator := P
  relative := n06RelativeOperator P
  inverse := fun z => n06TotalNeumannInverse (n06RelativeOperator P z)

theorem n06Properties_of_smallRelativeOperator
    [CompleteSpace (V.level (3 / 4 : ℝ) 0 b)]
    (D : ReferenceData) (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (base : ℕ) (ε : ℝ)
    (P : AnnularState S × ℝ → B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (hε : 0 < ε) (hleft : ∀ u : B.Space, B.inverse u.val.2 = u)
    (hphysical : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
        (V.forget (3 / 4 : ℝ) 0 b (P z u)))
    (hsmall : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ‖n06RelativeOperator P z‖ < (1 / 2 : ℝ)) :
    N06Properties D S C K L V b B (n06RelativeData P) base ε := by
  refine ⟨hε, ?_⟩
  intro z hz hsector
  have hR := hsmall z hz hsector
  refine ⟨hphysical z hz hsector, ?_, hR, ?_, ?_, ?_⟩
  · intro F
    simp only [n06RelativeData, n06RelativeOperator, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  · intro u
    change P z u = u.val.2 + ((P z).comp B.inverse - ContinuousLinearMap.id ℝ _) u.val.2
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, hleft]
    abel
  · exact (n06TotalNeumannInverse_spec (n06RelativeOperator P z) hR).1
  · exact (n06TotalNeumannInverse_spec (n06RelativeOperator P z) hR).2

/-- N05 supplies the completeness and graph inverse identities needed by the construction. -/
theorem n06_exists_relativeData
    (D : ReferenceData) (T : MaterialData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (base : ℕ) (ε : ℝ)
    (hN05 : N05Properties D T S C K V b B)
    (P : AnnularState S × ℝ → B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (hε : 0 < ε)
    (hphysical : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
        (V.forget (3 / 4 : ℝ) 0 b (P z u)))
    (hsmall : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ‖n06RelativeOperator P z‖ < (1 / 2 : ℝ)) :
    ∃ Relative : RelativeInverseData S K V b B,
      N06Properties D S C K L V b B Relative base ε := by
  rcases hN05 with ⟨_, hV, _, _, _, _, _, _, hleft, _⟩
  letI : CompleteSpace (V.level (3 / 4 : ℝ) 0 b) :=
    (hV.2.1 (3 / 4 : ℝ) 0 b).completeSpace_coe
  exact ⟨n06RelativeData P,
    n06Properties_of_smallRelativeOperator D C L base ε P hε hleft hphysical hsmall⟩

end FixedDomain

end ContinuousFlexibility.Statements
