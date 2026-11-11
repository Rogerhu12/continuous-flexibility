import ContinuousFlexibility.Radial.InnerCentralPhysicalPoisson
import ContinuousFlexibility.Radial.InnerMorsePhysicalPoisson
import ContinuousFlexibility.Radial.InnerOrderedChoices

/-!
# Ordered choices for the same physical central and Morse models

The original R09 statement first gives the compression constants. For
each weight exponent we then choose the frequency threshold, the tail
index, and only afterwards the central cut and the cone length. The
central floor may depend on the chosen index, and the cone coefficients
and floor may also depend on the chosen central cut.

Every physical realization is supplied after these choices. Thus the
central estimate does not presume that a previously fixed small patch
already contains the selected far cuts. Each local existential returns
one model whose genuine physical Poisson columns and full conormal
error satisfy the estimates simultaneously.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements
open scoped Matrix.Norms.L2Operator

/-- At every even mode, one original compressed central model supplies
the physical columns, its positive drift-corrected energies, and both
weighted conormal errors. Realizations are quantified inside the
physical-column property, after the cut has been chosen. -/
def InnerCentralPhysicalFamily (C K X₀ η : ℝ) : Prop :=
  (∀ j : ℝ, 2 ≤ j → 2 * C * centralRadiusA ≤ innerCentralCapMass j X₀) ∧
    ∀ q : ℕ, 1 ≤ q →
      BufferHypotheses (innerCentralBufferData q X₀) ∧
      ∃ M : InnerBufferLocalizedData (innerCentralBufferData q X₀) C K,
        (∀ i, 0 < innerCentralModelCutEnergy M i) ∧
        InnerCentralPhysicalPoissonBound M ∧
        ∀ height : ℝ, 0 < height → ∀ sign : Bool,
          ‖innerTwoCutWeightedError
            (innerPhysicalCutKappa height
              (fun i => centralDensityRoot (bufferCut (innerCentralBufferData q X₀) i))
              (innerCentralModelCutEnergy M)) (fun _ => 1)
            (M.physicalFluxError height
              (fun i => centralDensityRoot (bufferCut (innerCentralBufferData q X₀) i))) sign‖ < η

/-- The same selected model works on both physical tails, for every
allowed weight parameter and both reciprocal signs, in every later
frequency band. No upper frequency cutoff is imposed. -/
def InnerMorsePhysicalFamily (a Cstar : ℝ) (N : ℕ) (C K η : ℝ) : Prop :=
  ∀ (T : MorseChainData) (σ : ℕ → ℝ) (D : ReferenceData) (cost : ℕ → ℝ),
    ∀ hreal : MorseChainRealization T σ D cost, T.index = N →
    ∀ m n j : ℕ, N ≤ m → m < n → 2 ≤ j → radialFrequencyBand T Cstar n j →
      BufferHypotheses
        (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
          (8 * (T.d m : ℝ) ^ 9)) ∧
      ∃ M : InnerBufferLocalizedData
        (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
          (8 * (T.d m : ℝ) ^ 9)) C K,
        (∀ i, 0 < (M.column i).inwardEnergy) ∧
        InnerMorsePhysicalPoissonBound hreal N a M ∧
        ∀ γ : ℝ, |γ| ≤ 1 → ∀ side : Bool, ∀ height : ℝ, 0 < height → ∀ sign : Bool,
          ‖innerTwoCutWeightedError
            (innerPhysicalCutKappa height (fun _ => 1) (fun i => (M.column i).inwardEnergy))
            (innerMorseCutWeight N a γ side m)
            (M.physicalFluxError height (fun _ => 1)) sign‖ < η

/-- The raw cone-head envelope. Its coefficients are allowed to depend
on already chosen geometry. The assertion below derives smallness
from these coefficients and positive exponential decay. -/
def innerConeHeadEnvelope (A b d c L j : ℝ) : ℝ :=
  exp (A + b * log (1 + j) + d * log (1 + L) - c * j * L)

def InnerConeHeadSmall (A b d c η L₀ : ℝ) : Prop :=
  ∀ L j : ℝ, L₀ ≤ L → 1 ≤ j →
    innerConeHeadEnvelope A b d c L j < η ∧
      j * innerConeHeadEnvelope A b d c L j < η

/-- The complete order a → Cstar → N → X₀,L for the actual local
models. Only the original R09 statement and the weight exponent are
inputs. Later numerical cone coefficients are raw envelope data;
their smallness and frequency-smallness are conclusions.

The two local R09 constants remain attached to their own actual model
data. The physical Poisson constants are already fixed absolute
constants in the two family predicates, independent of N, X₀, L and
the number of retained cells. -/
theorem exists_innerPhysicalOrderedChoices (hR09 : R09Statement) {a : ℝ} (ha : 0 ≤ a) :
    ∃ CM KM CC KC : ℝ, 0 < CM ∧ 0 < KM ∧ 0 < CC ∧ 0 < KC ∧
      ∃ Cstar : ℝ, 0 < Cstar ∧ innerMorseBufferThreshold ≤ Cstar ∧
        ∀ η : ℝ, 0 < η → ∀ initial : ℕ, ∃ N : ℕ,
          initial ≤ N ∧ 4096 ≤ N ∧ 64 * a ≤ (N : ℝ) ∧
          ∀ centralFloor : ℝ, ∃ X₀ : ℝ,
            centralFloor ≤ X₀ ∧ 8 ≤ X₀ ∧ innerCentralModelBorderRadius < X₀ ∧
            InnerCentralPhysicalFamily CC KC X₀ η ∧
            ∀ coneFloor Acone bcone dcone ccone : ℝ,
              0 ≤ bcone → 0 ≤ dcone → 0 < ccone → ∃ L : ℝ,
                1 ≤ L ∧ coneFloor ≤ L ∧
                InnerMorsePhysicalFamily a Cstar N CM KM η ∧
                InnerConeHeadSmall Acone bcone dcone ccone η L := by
  obtain ⟨CM, KM, hCM, hKM, hmorse⟩ := exists_innerMorsePhysicalChoices hR09 ha
  obtain ⟨CC, KC, hCC, hKC, hcentral⟩ := exists_innerCentralPhysicalChoices hR09
  obtain ⟨Cstar, hCstar, hgeometry, htail⟩ :=
    hmorse (innerMorseModelAmplitude CM KM) le_rfl
  refine ⟨CM, KM, CC, KC, hCM, hKM, hCC, hKC, Cstar, hCstar, hgeometry, ?_⟩
  intro η hη initial
  obtain ⟨N, hN, hlarge, hweight, hmodels⟩ := htail η hη initial
  have hMorseFamily : InnerMorsePhysicalFamily a Cstar N CM KM η := by
    intro T σ D cost hreal hindex m n j hm hmn hj hband
    obtain ⟨hB, M, hcolumns, herror⟩ :=
      hmodels T σ D cost hreal hindex m n j hm hmn hj hband
    exact ⟨hB, M, fun i => (M.energies_pos hB hCM i).1, hcolumns, herror⟩
  refine ⟨N, hN, hlarge, hweight, ?_⟩
  intro centralFloor
  obtain ⟨X₀, hfloor, hX, hfar, hmodelsCentral⟩ :=
    hcentral (innerCentralModelAmplitude CC KC) le_rfl η hη
      (max centralFloor (innerCentralModelBorderRadius + 1))
  have hsupport : innerCentralModelBorderRadius < X₀ :=
    (lt_add_one _).trans_le ((le_max_right _ _).trans hfloor)
  have hCentralFamily : InnerCentralPhysicalFamily CC KC X₀ η := by
    refine ⟨hfar, ?_⟩
    intro q hq
    obtain ⟨hB, M, hcolumns, herror⟩ := hmodelsCentral q hq
    have hfarq := hfar (2 * q) (innerCentralBuffer_frequency hq)
    exact ⟨hB, M, fun i => (innerCentralModelCutEnergy_bounds M hCC hfarq i).1,
      hcolumns, herror⟩
  refine ⟨X₀, (le_max_left _ _).trans hfloor, hX, hsupport, hCentralFamily, ?_⟩
  intro coneFloor Acone bcone dcone ccone hbcone hdcone hccone
  obtain ⟨L₀, hL₀, hcone⟩ := inner_product_frequency_suppression
    (A := Acone) hbcone hdcone hccone hη
  let L := max coneFloor L₀
  have hL : L₀ ≤ L := le_max_right _ _
  refine ⟨L, hL₀.trans hL, le_max_left _ _, hMorseFamily, ?_⟩
  intro L' j hL' hj
  exact hcone L' (hL.trans hL') j hj

end ContinuousFlexibility.Radial
