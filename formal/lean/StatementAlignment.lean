import RotorFourier
import RotorMatching
import RotorGenerator
import CycleExpansion
import StatementDomains

open IncrementCycles
open RotorRational RotorEnclosure RotorMatching

namespace StatementAlignment
noncomputable section

-- Eq. (3) is used only on probability tables with six positive factors.
theorem eq3_checked (J : Pair) (h : ∀ i j, i ≠ j → 0 < J i j) :
    (∀ i j, i ≠ j → 0 < reversePair J i j) ∧
    Real.log (numerator (reversePair J) / denominator (reversePair J)) =
      Real.log (numerator J / denominator J) :=
  StatementDomains.affinity_positive_domain J h

-- All symbols and all lengths, including a one-symbol word.
theorem twelve_phase_observed_statement (ρ η : ℝ) (n : ℕ) (w : Fin (n+1) → S) :
    let e := fun i a => em η (ctrlEmission i) a
    ObservedReversal.observed (1/12) (controlKernel ρ) e (fun k => IncrementCycles.flip (w k.rev)) =
      ObservedReversal.observed (1/12) (controlKernel ρ) e w :=
  ObservedReversal.control_observed_words ρ η w

-- Eq. (14), including the connection to the normalized six-state generator.
theorem eq14_checked (u a : ℝ) (hu : 0 ≤ u) (ha : -1 ≤ a ∧ a ≤ 1) :
    let Q := RotorGenerator.generator a
    let P := (NormedSpace.exp (u • Q) : RotorGenerator.Mat)
    corr (fun d => P 0 d) =
      (2/9 * Real.exp (-u/2) + 2/3 * Real.exp (-3*u/2)) *
        Real.cos (Real.sqrt 3 * a * u/2) + 1/9 * Real.exp (-2*u) := by
  dsimp only
  have h : (fun d => (NormedSpace.exp (u • RotorGenerator.generator a) : RotorGenerator.Mat) 0 d) =
      kernel u a := by
    funext d
    simpa only [sub_zero] using RotorGenerator.sampled_ctmc u a 0 d
  rw [h,RotorFourier.autocorrelation_eq14 u a hu ha]
  rfl

-- Figure 5 compares the entire observed pair law and a triple contrast at the same bias.
theorem figure5_checked :
    ∃ a ∈ Set.Icc (52363/100000 : ℝ) (52365/100000 : ℝ),
      let P := (NormedSpace.exp (RotorGenerator.generator a) : RotorGenerator.Mat)
      let k := fun d => P 0 d
      let r := rotorR a 1
      rotorR a 2 = r^2 ∧
      (0 < (1-r)/2 ∧ (1-r)/2 < 1/2) ∧
      (∀ s t, pushBinary (markerThree k) s t = pushBinary (equilibrium r) s t) ∧
      (2436/1000000 : ℝ) <
        (observedWord k highSites highSites lowSites highSites -
          observedWord k highSites lowSites highSites highSites) -
        (eqFour r true true false true - eqFour r true false true true) := by
  obtain ⟨a,ha,hpos,hlt,hP,hD,hgap⟩ := rotor_matched_pair_law
  have hb : -1 ≤ a ∧ a ≤ 1 :=
    ⟨(show (-1 : ℝ) ≤ (low : ℝ) by norm_num [low]).trans ha.1,
     ha.2.trans (show (high : ℝ) ≤ 1 by norm_num [high])⟩
  have hav : a ∈ Set.Icc (52363/100000 : ℝ) (52365/100000 : ℝ) := by
    simpa [low, high] using ha
  refine ⟨a,hav,?_⟩
  dsimp only
  have hk : (fun d => (NormedSpace.exp (RotorGenerator.generator a) : RotorGenerator.Mat) 0 d) =
      kernel 1 a := by
    funext d
    simpa only [one_smul,sub_zero] using RotorGenerator.sampled_ctmc 1 a 0 d
  have hr : liveCorr a = rotorR a 1 := RotorFourier.autocorrelation_eq14 1 a (by norm_num) hb
  rw [RotorFourier.gap_eq14 a hb] at hgap
  refine ⟨sub_eq_zero.mp hgap,?_⟩
  rw [hk,← hr]
  exact ⟨⟨hpos,hlt⟩,(fun s t => congrFun (congrFun hP s) t),hD⟩

theorem rotor_word_labels :
    [binaryStep true true, binaryStep true false, binaryStep false true] = [S.P,S.R,S.E] ∧
    [binaryStep true false, binaryStep false true, binaryStep true true] = [S.R,S.E,S.P] ∧
    reverseWord [S.P,S.R,S.E] = [S.R,S.E,S.P] ∧
    StatementDomains.tripleParity (S.P,S.R,S.E) = (S.R,S.E,S.P) :=
  ⟨rfl,rfl,rfl,rfl⟩

def phase6Triple (ρ η : ℝ) (i j k : S) : ℝ :=
  CycleExpansion.emittedThree (1/6) (ResetMixing.kernel ResetMixing.sixCycle ρ)
    ((em η · i) ∘ cycleSymbol) ((em η · j) ∘ cycleSymbol) ((em η · k) ∘ cycleSymbol)

def phase12Triple (ρ η : ℝ) (i j k : S) : ℝ :=
  CycleExpansion.emittedThree (1/12) (controlKernel ρ)
    ((em η · i) ∘ ctrlEmission) ((em η · j) ∘ ctrlEmission) ((em η · k) ∘ ctrlEmission)

theorem six_twelve_actual_separation {ρ η : ℝ} (hr : ρ < 1) (he : η < 1) :
    0 < phase6Triple ρ η S.P S.R S.E - phase6Triple ρ η S.R S.E S.P ∧
    phase12Triple ρ η S.P S.R S.E - phase12Triple ρ η S.R S.E S.P = 0 := by
  constructor
  · simp only [phase6Triple,CycleExpansion.six_three,(eq10 ρ η).1]
    exact triple_positive he hr
  · simp only [phase12Triple,CycleExpansion.twelve_three]
    have h := (eq11 ρ η 0 0).1
    simpa [swapped] using h

end
end StatementAlignment
