import PEqualNP.MetaComplexity.Helpers.ExchangeElim

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers

-- Partial progress for L-meta-1593. The full statement remains unproved.
-- This uses the existing internal constant-folding framework.
-- Four distinct effective readers suffice when the restricted output is nonconstant.

namespace PEqualNP.Outside.L_meta_1593_aux

lemma restriction_reader_count (n : ℕ) (C : Circuit) (z : Fin n) (b : Bool)
    (hC : FanInTwo C)
    (hnc : ∃ x y : Fin n → Bool,
      circuitFun n C (Function.update x z b) ≠ circuitFun n C (Function.update y z b)) :
    ∃ D : Circuit, FanInTwo D ∧
      D.size + (C.gates.map normGate).countP (fun g => g.inputs.contains z.val) ≤ C.size ∧
      circuitFun n D = fun x => circuitFun n C (Function.update x z b) := by
  classical
  let stats : List Stat := List.ofFn (fun i : Fin n =>
    if i = z then Stat.const b else Stat.wire i.val)
  let gs := C.gates.map normGate
  let acc := elim n gs (stats, [])
  have hnorm : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g' (hC g' hg')
  have initial (x : Fin n → Bool) :
      Inv n (List.ofFn x) (List.ofFn (Function.update x z b)) (stats, []) := by
    refine ⟨by simp [stats], ?_⟩
    intro i
    by_cases hi : i < n
    · have hs : stats.getD i (Stat.const false) =
          if (⟨i, hi⟩ : Fin n) = z then Stat.const b else Stat.wire i := by
        simp [stats, hi]
      rw [hs]
      by_cases hiz : (⟨i, hi⟩ : Fin n) = z
      · simp [hiz, Stat.Valid, Stat.val, hi]
      · simp [hiz, Stat.Valid, Stat.val, wiresFrom, hi]
    · have hs : stats.getD i (Stat.const false) = Stat.const false := by
        exact List.getD_eq_default _ _ (by simp [stats]; omega)
      rw [hs]
      simp [Stat.Valid, Stat.val, hi]
  have invariant (x : Fin n → Bool) :
      Inv n (List.ofFn x) (wiresFrom gs (List.ofFn (Function.update x z b))) acc :=
    inv_elim n _ (by simp) gs _ _ (fun g hg => (hnorm g hg).1) (initial x)
  have hvalue (x : Fin n → Bool) :
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn x)) =
        circuitFun n C (Function.update x z b) := by
    rw [((invariant x).2 C.output).2]
    simp only [gs, wiresFrom_norm]
    rfl
  have count := PEqualNP.MetaComplexity.Exchange.elim_count n z.val gs (stats, []) hnorm
    (by simp [stats, z.isLt])
    (by refine ⟨b, ?_⟩; simp [stats, z.isLt])
  have count' : acc.2.length + gs.countP (fun g => g.inputs.contains z.val) ≤ gs.length := by
    simpa only [List.length_nil, Nat.zero_add] using count
  cases hs : acc.1.getD C.output (Stat.const false) with
  | const c =>
    obtain ⟨x, y, hxy⟩ := hnc
    exact (hxy (by rw [← hvalue x, ← hvalue y, hs]; rfl)).elim
  | wire j =>
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), ?_, ?_⟩
    · simpa [Circuit.size, gs] using count'
    · funext x
      have hv := hvalue x
      rw [hs] at hv
      exact hv

lemma effective_reader_count (C : Circuit) (z : ℕ) (hC : FanInTwo C) :
    (C.gates.map normGate).countP (fun g => g.inputs.contains z) =
      (C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains z).length := by
  rw [List.countP_map, ← List.countP_eq_length_filter]
  apply List.countP_congr
  intro g hg
  have he : (normGate g).inputs =
      g.inputs.take (bif g.op.eval [false] then 1 else 2) := by
    obtain ⟨op, ins⟩ := g
    obtain ⟨hop, hlen⟩ := hC ⟨op, ins⟩ hg
    change op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not at hop
    rcases hop with rfl | rfl | rfl <;>
      simp [normGate, GateOp.eval, List.take_of_length_le hlen]
  change (normGate g).inputs.contains z = true ↔
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains z = true
  rw [he]

lemma four_effective_readers (n : ℕ) (C : Circuit) (z : Fin n)
    (hC : FanInTwo C)
    (hnc : ∃ x y : Fin n → Bool,
      circuitFun n C (Function.update x z false) ≠ circuitFun n C (Function.update y z false))
    (hread : 4 ≤ (C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains z.val).length) :
    ∃ t : ℕ, t + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => circuitFun n C (Function.update x z false)) t := by
  obtain ⟨D, hD, hsize, hfun⟩ := restriction_reader_count n C z false hC hnc
  rw [effective_reader_count C z.val hC] at hsize
  refine ⟨D.size, by omega, D, hD, le_rfl, ?_⟩
  intro x
  exact congrFun hfun x

end PEqualNP.Outside.L_meta_1593_aux
