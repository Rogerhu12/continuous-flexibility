module

public import ContinuousFlexibility.Analysis.N07aClosedJets
public import ContinuousFlexibility.Analysis.N07aCanonicalSmoothJets

/-!
# Closed jets of the same canonical smooth decoder

The choices below extend the actual mixed L² jets of the original unknown.
No boundary values of the arbitrary total decoder enter the construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open N07aClosedJets
open scoped ContDiff Topology

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

/-- One compatible closed tower for the decoder of the original L² class. -/
def n07aCanonicalClosedJets (hm : K.left m < K.right m)
    (u : n07aCanonicalSmoothSpace S K m) :
    ClosedJetTower (K.left m) (K.right m) (n07aCanonicalSmoothDecode hm u) := by
  classical
  have h := n07aCanonicalSmoothRepresentative_properties hm u
  apply Classical.choice
  apply canonical_closedJetTower_nonempty hm h.1 (fun p _ => h.2.1 p)
  intro a b
  obtain ⟨v, hv⟩ := u.property a a le_rfl b
  exact (memLp_congr_ae (n07aCanonicalSmoothDecode_mixed_ae hm a b u v hv)).mpr (Lp.memLp v)

end ContinuousFlexibility.Analysis
