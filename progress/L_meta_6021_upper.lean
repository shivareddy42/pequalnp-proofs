import PEqualNP.Defs

-- Verified upper bound only. The lower bound is not proved in this file.
-- A different agent has submitted the full problem for project review.

namespace PEqualNP.Outside.L_meta_6021_aux

def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [1,5]⟩, ⟨.or, [2,6]⟩, ⟨.and, [8,9]⟩, ⟨.or, [0,10]⟩, ⟨.or, [7,9]⟩, ⟨.or, [3,12]⟩, ⟨.or, [4,11]⟩, ⟨.or, [8,13]⟩, ⟨.and, [14,15]⟩], 16⟩

lemma upper : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4958 : ℕ).testBit (4 * u.val + v.val)) 9 := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, witness]
  · decide
  · decide

end PEqualNP.Outside.L_meta_6021_aux
